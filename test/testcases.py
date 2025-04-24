import difflib
import inspect
import json
import logging
import posixpath
import sys
import threading
import unittest
import warnings
from collections import Counter
from contextlib import contextmanager
from copy import copy, deepcopy
from difflib import get_close_matches
from functools import wraps
from unittest.suite import _DebugResult
from unittest.util import safe_repr
from urllib.parse import (
    parse_qsl,
    unquote,
    urlencode,
    urljoin,
    urlparse,
    urlsplit,
    urlunparse,
)
from urllib.request import url2pathname

from asgiref.sync import async_to_sync, iscoroutinefunction

from django.apps import apps
from django.conf import settings
from django.core import mail
from django.core.exceptions import ImproperlyConfigured, ValidationError
from django.core.files import locks
from django.core.handlers.wsgi import WSGIHandler, get_path_info
from django.core.management import call_command
from django.core.management.color import no_style
from django.core.management.sql import emit_post_migrate_signal
from django.core.servers.basehttp import ThreadedWSGIServer, WSGIRequestHandler
from django.core.signals import setting_changed
from django.db import DEFAULT_DB_ALIAS, connection, connections, transaction
from django.forms.fields import CharField
from django.http import QueryDict
from django.http.request import split_domain_port, validate_host
from django.http.response import HttpResponseBase
from django.test.client import AsyncClient, Client
from django.test.html import HTMLParseError, parse_html
from django.test.signals import template_rendered
from django.test.utils import (
    CaptureQueriesContext,
    ContextList,
    compare_xml,
    modify_settings,
    override_settings,
)
from django.utils.deprecation import RemovedInDjango50Warning, RemovedInDjango51Warning
from django.utils.functional import classproperty
from django.utils.version import PY310
from django.views.static import serve

logger = logging.getLogger("django.test")

__all__ = (
    "TestCase",
    "TransactionTestCase",
    "SimpleTestCase",
    "skipIfDBFeature",
    "skipUnlessDBFeature",
)


def to_list(value):
    """Put value into a list if it's not already one."""
    if not isinstance(value, list):
        value = [value]
    return value


def assert_and_parse_html(self, html, user_msg, msg):
    try:
        dom = parse_html(html)
    except HTMLParseError as e:
        standardMsg = "%s\n%s" % (msg, e)
        self.fail(self._formatMessage(user_msg, standardMsg))
    return dom


class _AssertNumQueriesContext(CaptureQueriesContext):
    def __init__(self, test_case, num, connection):
        self.test_case = test_case
        self.num = num
        super().__init__(connection)

    def __exit__(self, exc_type, exc_value, traceback):
        super().__exit__(exc_type, exc_value, traceback)
        if exc_type is not None:
            return
        executed = len(self)
        self.test_case.assertEqual(
            executed,
            self.num,
            "%d queries executed, %d expected\nCaptured queries were:\n%s"
            % (
                executed,
                self.num,
                "\n".join(
                    "%d. %s" % (i, query["sql"])
                    for i, query in enumerate(self.captured_queries, start=1)
                ),
            ),
        )


class _AssertTemplateUsedContext:
    def __init__(self, test_case, template_name, msg_prefix="", count=None):
        self.test_case = test_case
        self.template_name = template_name
        self.msg_prefix = msg_prefix
        self.count = count

        self.rendered_templates = []
        self.rendered_template_names = []
        self.context = ContextList()

    def on_template_render(self, sender, signal, template, context, **kwargs):
        self.rendered_templates.append(template)
        self.rendered_template_names.append(template.name)
        self.context.append(copy(context))

    def test(self):
        self.test_case._assert_template_used(
            self.template_name,
            self.rendered_template_names,
            self.msg_prefix,
            self.count,
        )

    def __enter__(self):
        template_rendered.connect(self.on_template_render)
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        template_rendered.disconnect(self.on_template_render)
        if exc_type is not None:
            return
        self.test()


class _AssertTemplateNotUsedContext(_AssertTemplateUsedContext):
    def test(self):
        self.test_case.assertFalse(
            self.template_name in self.rendered_template_names,
            f"{self.msg_prefix}Template '{self.template_name}' was used "
            f"unexpectedly in rendering the response",
        )


class DatabaseOperationForbidden(AssertionError):
    pass


class _DatabaseFailure:
    def __init__(self, wrapped, message):
        self.wrapped = wrapped
        self.message = message

    def __call__(self):
        raise DatabaseOperationForbidden(self.message)


# RemovedInDjango50Warning
class _AssertFormErrorDeprecationHelper:
    @staticmethod
    def assertFormError(self, response, form, field, errors, msg_prefix=""):
        """
        Search through all the rendered contexts of the `response` for a form named
        `form` then dispatch to the new assertFormError() using that instance.
        If multiple contexts contain the form, they're all checked in order and any
        failure will abort (this matches the old behavior).
        """
        warning_msg = (
            f"Passing response to assertFormError() is deprecated. Use the form object "
            f"directly: assertFormError(response.context[{form!r}], {field!r}, ...)"
        )
        warnings.warn(warning_msg, RemovedInDjango50Warning, stacklevel=2)

        full_msg_prefix = f"{msg_prefix}: " if msg_prefix else ""
        contexts = to_list(response.context) if response.context is not None else []
        if not contexts:
            self.fail(
                f"{full_msg_prefix}Response did not use any contexts to render the "
                f"response"
            )
        # Search all contexts for the error.
        found_form = False
        for i, context in enumerate(contexts):
            if form not in context:
                continue
            found_form = True
            self.assertFormError(context[form], field, errors, msg_prefix=msg_prefix)
        if not found_form:
            self.fail(
                f"{full_msg_prefix}The form '{form}' was not used to render the "
                f"response"
            )

    @staticmethod
    def assertFormSetError(
        self, response, formset, form_index, field, errors, msg_prefix=""
    ):
        """
        Search for a formset named "formset" in the "response" and dispatch to
        the new assertFormSetError() using that instance. If the name is found
        in multiple contexts they're all checked in order and any failure will
        abort the test.
        """
        warning_msg = (
            f"Passing response to assertFormSetError() is deprecated. Use the formset "
            f"object directly: assertFormSetError(response.context[{formset!r}], "
            f"{form_index!r}, ...)"
        )
        warnings.warn(warning_msg, RemovedInDjango50Warning, stacklevel=2)

        full_msg_prefix = f"{msg_prefix}: " if msg_prefix else ""
        contexts = to_list(response.context) if response.context is not None else []
        if not contexts:
            self.fail(
                f"{full_msg_prefix}Response did not use any contexts to render the "
                f"response"
            )
        found_formset = False
        for i, context in enumerate(contexts):
            if formset not in context or not hasattr(context[formset], "forms"):
                continue
            found_formset = True
            self.assertFormSetError(
                context[formset], form_index, field, errors, msg_prefix
            )
        if not found_formset:
            self.fail(
                f"{full_msg_prefix}The formset '{formset}' was not used to render the "
                f"response"
            )

    @classmethod
    def patch_signature(cls, new_method):
        """
        Replace the decorated method with a new one that inspects the passed
        args/kwargs and dispatch to the old implementation (with deprecation
        warning) when it detects the old signature.
        """

        @wraps(new_method)
        def patched_method(self, *args, **kwargs):
            old_method = getattr(cls, new_method.__name__)
            old_signature = inspect.signature(old_method)
            try:
                old_bound_args = old_signature.bind(self, *args, **kwargs)
            except TypeError:
                # If old signature doesn't match then either:
                # 1) new signature will match
                # 2) or a TypeError will be raised showing the user information
                # about the new signature.
                return new_method(self, *args, **kwargs)

            new_signature = inspect.signature(new_method)
            try:
                new_bound_args = new_signature.bind(self, *args, **kwargs)
            except TypeError:
                # Old signature matches but not the new one (because of
                # previous try/except).
                return old_method(self, *args, **kwargs)

            # If both signatures match, decide on which method to call by
            # inspecting the first arg (arg[0] = self).
            assert old_bound_args.args[1] == new_bound_args.args[1]
            if hasattr(
                old_bound_args.args[1], "context"
            ):  # Looks like a response object => old method.
                return old_method(self, *args, **kwargs)
            elif isinstance(old_bound_args.args[1], HttpResponseBase):
                raise ValueError(
                    f"{old_method.__name__}() is only usable on responses fetched "
                    f"using the Django test Client."
                )
            else:
                return new_method(self, *args, **kwargs)

        return patched_method


class SimpleTestCase(unittest.TestCase):
    # The class we'll use for the test client self.client.
    # Can be overridden in derived classes.
    client_class = Client
    async_client_class = AsyncClient
    _overridden_settings = None
    _modified_settings = None

    databases = set()
    _disallowed_database_msg = (
        "Database %(operation)s to %(alias)r are not allowed in SimpleTestCase "
        "subclasses. Either subclass TestCase or TransactionTestCase to ensure "
        "proper test isolation or add %(alias)r to %(test)s.databases to silence "
        "this failure."
    )
    _disallowed_connection_methods = [
        ("connect", "connections"),
        ("temporary_connection", "connections"),
        ("cursor", "queries"),
        ("chunked_cursor", "queries"),
    ]

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        if cls._overridden_settings:
            cls._cls_overridden_context = override_settings(**cls._overridden_settings)
            cls._cls_overridden_context.enable()
            cls.addClassCleanup(cls._cls_overridden_context.disable)
        if cls._modified_settings:
            cls._cls_modified_context = modify_settings(cls._modified_settings)
            cls._cls_modified_context.enable()
            cls.addClassCleanup(cls._cls_modified_context.disable)
        cls._add_databases_failures()
        cls.addClassCleanup(cls._remove_databases_failures)

    @classmethod
    def _validate_databases(cls):
        if cls.databases == "__all__":
            return frozenset(connections)
        for alias in cls.databases:
            if alias not in connections:
                message = (
                    "%s.%s.databases refers to %r which is not defined in "
                    "settings.DATABASES."
                    % (
                        cls.__module__,
                        cls.__qualname__,
                        alias,
                    )
                )
                close_matches = get_close_matches(alias, list(connections))
                if close_matches:
                    message += " Did you mean %r?" % close_matches[0]
                raise ImproperlyConfigured(message)
        return frozenset(cls.databases)

    @classmethod
    def _add_databases_failures(cls):
        cls.databases = cls._validate_databases()
        for alias in connections:
            if alias in cls.databases:
                continue
            connection = connections[alias]
            for name, operation in cls._disallowed_connection_methods:
                message = cls._disallowed_database_msg % {
                    "test": "%s.%s" % (cls.__module__, cls.__qualname__),
                    "alias": alias,
                    "operation": operation,
                }
                method = getattr(connection, name)
                setattr(connection, name, _DatabaseFailure(method, message))

    @classmethod
    def _remove_databases_failures(cls):
        for alias in connections:
            if alias in cls.databases:
                continue
            connection = connections[alias]
            for name, _ in cls._disallowed_connection_methods:
                method = getattr(connection, name)
                setattr(connection, name, method.wrapped)

    def __call__(self, result=None):
        """
        Wrapper around default __call__ method to perform common Django test
        set up. This means that user-defined Test Cases aren't required to
        include a call to super().setUp().
        """
        self._setup_and_call(result)

    def debug(self):
        """Perform the same as __call__(), without catching the exception."""
        debug_result = _DebugResult()
        self._setup_and_call(debug_result, debug=True)

    def _setup_and_call(self, result, debug=False):
        """
        Perform the following in order: pre-setup, run test, post-teardown,
        skipping pre/post hooks if test is set to be skipped.

        If debug=True, reraise any errors in setup and use super().debug()
        instead of __call__() to run the test.
        """
        testMethod = getattr(self, self._testMethodName)
        skipped = getattr(self.__class__, "__unittest_skip__", False) or getattr(
            testMethod, "__unittest_skip__", False
        )

        # Convert async test methods.
        if iscoroutinefunction(testMethod):
            setattr(self, self._testMethodName, async_to_sync(testMethod))

        if not skipped:
            try:
                self._pre_setup()
            except Exception:
                if debug:
                    raise
                result.addError(self, sys.exc_info())
                return
        if debug:
            super().debug()
        else:
            super().__call__(result)
        if not skipped:
            try:
                self._post_teardown()
            except Exception:
                if debug:
                    raise
                result.addError(self, sys.exc_info())
                return

    def _pre_setup(self):
        """
        Perform pre-test setup:
        * Create a test client.
        * Clear the mail test outbox.
        """
        self.client = self.client_class()
        self.async_client = self.async_client_class()
        mail.outbox = []

    def _post_teardown(self):
        """Perform post-test things."""
        pass

    def settings(self, **kwargs):
        """
        A context manager that temporarily sets a setting and reverts to the
        original value when exiting the context.
        """
        return override_settings(**kwargs)

    def modify_settings(self, **kwargs):
        """
        A context manager that temporarily applies changes a list setting and
        reverts back to the original value when exiting the context.
        """
        return modify_settings(**kwargs)

    def assertRedirects(
        self,
        response,
        expected_url,
        status_code=302,
        target_status_code=200,
        msg_prefix="",
        fetch_redirect_response=True,
    ):
        """
        Assert that a response redirected to a specific URL and that the
        redirect URL can be loaded.

        Won't work for external links since it uses the test client to do a
        request (use fetch_redirect_response=False to check such links without
        fetching them).
        """
        if msg_prefix:
            msg_prefix += ": "

        if hasattr(response, "redirect_chain"):
            # The request was a followed redirect
            self.assertTrue(
                response.redirect_chain,
                msg_prefix
                + (
                    "Response didn't redirect as expected: Response code was %d "
                    "(expected %d)"
                )
                % (response.status_code, status_code),
            )

            self.assertEqual(
                response.redirect_chain[0][1],
                status_code,
                msg_prefix
                + (
                    "Initial response didn't redirect as expected: Response code was "
                    "%d (expected %d)"
                )
                % (response.redirect_chain[0][1], status_code),
            )

            url, status_code = response.redirect_chain[-1]

            self.assertEqual(
                response.status_code,
                target_status_code,
                msg_prefix
                + (
                    "Response didn't redirect as expected: Final Response code was %d "
                    "(expected %d)"
                )
                % (response.status_code, target_status_code),
            )

        else:
            # Not a followed redirect
            self.assertEqual(
                response.status_code,
                status_code,
                msg_prefix
                + (
                    "Response didn't redirect as expected: Response code was %d "
                    "(expected %d)"
                )
                % (response.status_code, status_code),
            )

            url = response.url
            scheme, netloc, path, query, fragment = urlsplit(url)

            # Prepend the request path to handle relative path redirects.
            if not path.startswith("/"):
                url = urljoin(response.request["PATH_INFO"], url)
                path = urljoin(response.request["PATH_INFO"], path)

            if fetch_redirect_response:
                # netloc might be empty, or in cases where Django tests the
                # HTTP scheme, the convention is for netloc to be 'testserver'.
                # Trust both as "internal" URLs here.
                domain, port = split_domain_port(netloc)
                if domain and not validate_host(domain, settings.ALLOWED_HOSTS):
                    raise ValueError(
                        "The test client is unable to fetch remote URLs (got %s). "
                        "If the host is served by Django, add '%s' to ALLOWED_HOSTS. "
                        "Otherwise, use "
                        "assertRedirects(..., fetch_redirect_response=False)."
                        % (url, domain)
                    )
                # Get the redirection page, using the same client that was used
                # to obtain the original response.
                extra = response.client.extra or {}
                headers = response.client.headers or {}
                redirect_response = response.client.get(
                    path,
                    QueryDict(query),
                    secure=(scheme == "https"),
                    headers=headers,
                    **extra,
                )
                self.assertEqual(
                    redirect_response.status_code,
                    target_status_code,
                    msg_prefix
                    + (
                        "Couldn't retrieve redirection page '%s': response code was %d "
                        "(expected %d)"
                    )
                    % (path, redirect_response.status_code, target_status_code),
                )

        self.assertURLEqual(
            url,
            expected_url,
            msg_prefix
            + "Response redirected to '%s', expected '%s'" % (url, expected_url),
        )

    def assertURLEqual(self, url1, url2, msg_prefix=""):
        """
        Assert that two URLs are the same, ignoring the order of query string
        parameters except for parameters with the same name.

        For example, /path/?x=1&y=2 is equal to /path/?y=2&x=1, but
        /path/?a=1&a=2 isn't equal to /path/?a=2&a=1.
        """

        def normalize(url):
            """Sort the URL's query string parameters."""
            url = str(url)  # Coerce reverse_lazy() URLs.
            scheme, netloc, path, params, query, fragment = urlparse(url)
            query_parts = sorted(parse_qsl(query))
            return urlunparse(
                (scheme, netloc, path, params, urlencode(query_parts), fragment)
            )

        self.assertEqual(
            normalize(url1),
            normalize(url2),
            msg_prefix + "Expected '%s' to equal '%s'." % (url1, url2),
        )

    def _assert_contains(self, response, text, status_code, msg_prefix, html):
        # If the response supports deferred rendering and hasn't been rendered
        # yet, then ensure that it does get rendered before proceeding further.
        if (
            hasattr(response, "render")
            and callable(response.render)
            and not response.is_rendered
        ):
            response.render()

        if msg_prefix:
            msg_prefix += ": "

        self.assertEqual(
            response.status_code,
            status_code,
            msg_prefix + "Couldn't retrieve content: Response code was %d"
            " (expected %d)" % (response.status_code, status_code),
        )

        if response.streaming:
            content = b"".join(response.streaming_content)
        else:
            content = response.content
        if not isinstance(text, bytes) or html:
            text = str(text)
            content = content.decode(response.charset)
            text_repr = "'%s'" % text
        else:
            text_repr = repr(text)
        if html:
            content = assert_and_parse_html(
                self, content, None, "Response's content is not valid HTML:"
            )
            text = assert_and_parse_html(
                self, text, None, "Second argument is not valid HTML:"
            )
        real_count = content.count(text)
        return (text_repr, real_count, msg_prefix)

    def assertContains(
        self, response, text, count=None, status_code=200, msg_prefix="", html=False
    ):
        """
        Assert that a response indicates that some content was retrieved
        successfully, (i.e., the HTTP status code was as expected) and that
        ``text`` occurs ``count`` times in the content of the response.
        If ``count`` is None, the count doesn't matter - the assertion is true
        if the text occurs at least once in the response.
        """
        text_repr, real_count, msg_prefix = self._assert_contains(
            response, text, status_code, msg_prefix, html
        )

        if count is not None:
            self.assertEqual(
                real_count,
                count,
                msg_prefix
                + "Found %d instances of %s in response (expected %d)"
                % (real_count, text_repr, count),
            )
        else:
            self.assertTrue(
                real_count != 0, msg_prefix + "Couldn't find %s in response" % text_repr
            )

    def assertNotContains(
        self, response, text, status_code=200, msg_prefix="", html=False
    ):
        """
        Assert that a response indicates that some content was retrieved
        successfully, (i.e., the HTTP status code was as expected) and that
        ``text`` doesn't occur in the content of the response.
        """
        text_repr, real_count, msg_prefix = self._assert_contains(
            response, text, status_code, msg_prefix, html
        )

        self.assertEqual(
            real_count, 0, msg_prefix + "Response should not contain %s" % text_repr
        )

    def _check_test_client_response(self, response, attribute, method_name):
        """
        Raise a ValueError if the given response doesn't have the required
        attribute.
        """
        if not hasattr(response, attribute):
            raise ValueError(
                f"{method_name}() is only usable on responses fetched using "
                "the Django test Client."
            )

    def _assert_form_error(self, form, field, errors, msg_prefix, form_repr):
        if not form.is_bound:
            self.fail(
                f"{msg_prefix}The {form_repr} is not bound, it will never have any "
                f"errors."
            )

        if field is not None and field not in form.fields:
            self.fail(
                f"{msg_prefix}The {form_repr} does not contain the field {field!r}."
            )
        if field is None:
            field_errors = form.non_field_errors()
            failure_message = f"The non-field errors of {form_repr} don't match."
        else:
            field_errors = form.errors.get(field, [])
            failure_message = (
                f"The errors of field {field!r} on {form_repr} don't match."
            )

        self.assertEqual(field_errors, errors, msg_prefix + failure_message)

    # RemovedInDjango50Warning: When the deprecation ends, remove the
    # decorator.
Calc

{%load static%}

<!DOCTYPE html>
<html lang="en" data-theme="light">
<head>
    <link rel="stylesheet" href="{% static 'calculators-style.css' %}">
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Calculators</title>
</head>
<body>
    <!-- Header -->
    <header>
        <div class="container header-content">
            <a href="{%url 'index' %}" class="logo">
            <img src="{% static 'images/logo.jpg' %}" class="logo"></a> 
            <div class="mobile-toggle">☰</div>
            <nav>
                <ul>
                    <li><a href="{%url 'index' %}">Home</a></li>
                    <li><a href="{%url 'about' %}">About Us</a></li>
                    <li><a href="{%url 'products' %}">Products</a></li>
                    <li><a href="{%url 'contact' %}">Contact</a></li>
                    <li><a href="{%url 'calculators' %}" class="active">Calculators</a></li>
                    {%if user.is_authenticated%}
                        <li><a href="{%url 'dashboard' %}">Member's Dashboard</a></li>
                        <li><a href="{%url 'logout'%}">Logout</a></li>
                    {%else%}
                        <li><a href="{%url 'registration'%}">Login or Signup</a></li><li></li>
                    {%endif%}
                        <button class="theme-toggle" id="theme-toggle">
                            <span class="icon">☀️</span>
                            <span class="toggle-text">Dark Mode</span>
                        </button>
                    </li>
                </ul>
            </nav>
        </div>
    </header>

    <!-- Page Header -->
    <section class="page-header">
        <div class="container">
            <h1>Sustainability Calculators</h1>
            <ul class="breadcrumb">
                <li><a href="{%url 'index' %}">Home</a></li>
                <li>></li>
                <li>Calculators</li>
            </ul>
        </div>
    </section>

    <!-- Calculators Section -->
    <section class="calculators-section">
        <div class="container">
            <div class="calculators-grid">
                <!-- Carbon Footprint Calculator -->
                <div class="calculator">
                    <h2>Carbon Footprint Calculator</h2>
                    <p>Calculate your approximate carbon footprint based on your daily activities and consumption patterns.</p>
                    
                    <form id="carbon-form">
                        <div class="form-group">
                            <label for="transportation">Daily Transportation Method:</label>
                            <select id="transportation" name="transportation">
                                <option value="car">Car (Gasoline)</option>
                                <option value="electric-car">Electric Car</option>
                                <option value="bus">Public Bus</option>
                                <option value="train">Train/Subway</option>
                                <option value="bicycle">Bicycle/Walk</option>
                            </select>
                        </div>
                        
                        <div class="form-group">
                            <label for="commute">Average Daily Commute (miles):</label>
                            <input type="number" id="commute" name="commute" placeholder="Enter miles" min="0">
                        </div>
                        
                        <div class="form-group">
                            <label for="electricity">Monthly Electricity Usage (kWh):</label>
                            <input type="number" id="electricity" name="electricity" placeholder="Enter kWh" min="0">
                        </div>
                        
                        <div class="form-group">
                            <label for="diet">Diet Type:</label>
                            <select id="diet" name="diet">
                                <option value="meat-rich">Meat in Most Meals</option>
                                <option value="meat-moderate">Moderate Meat Consumption</option>
                                <option value="vegetarian">Vegetarian</option>
                                <option value="vegan">Vegan</option>
                            </select>
                        </div>
                        
                        <div class="form-group">
                            <label for="flights">Number of Flights per Year:</label>
                            <input type="number" id="flights" name="flights" placeholder="Enter number of flights" min="0">
                        </div>
                        
                        <div class="button-group">
                            <button type="button" class="primary-btn" id="calculate-carbon">Calculate Carbon Footprint</button>
                            <button type="reset" class="secondary-btn">Reset Calculator</button>
                        </div>
                    </form>
                    
                    <div class="results" id="carbon-results">
                        <h3>Your Carbon Footprint Results</h3>
                        <p><strong>Total Carbon Footprint:</strong> <span id="total-carbon"></span> tons CO₂e per year</p>
                        <p><strong>Transportation:</strong> <span id="transport-carbon"></span> tons CO₂e</p>
                        <p><strong>Home Energy:</strong> <span id="energy-carbon"></span> tons CO₂e</p>
                        <p><strong>Diet:</strong> <span id="diet-carbon"></span> tons CO₂e</p>
                        <p><strong>Air Travel:</strong> <span id="flight-carbon"></span> tons CO₂e</p>
                        
                        <div class="tips">
                            <h4>How to Reduce Your Carbon Footprint</h4>
                            <ul id="carbon-tips">
                                <!-- Tips will be added dynamically -->
                            </ul>
                        </div>
                    </div>
                </div>
                
                <!-- Energy Usage Calculator -->
                <div class="calculator">
                    <h2>Energy Usage Calculator</h2>
                    <p>Estimate your household or business energy consumption and find ways to improve efficiency.</p>
                    
                    <form id="energy-form">
                        <div class="form-group">
                            <label for="property-type">Property Type:</label>
                            <select id="property-type" name="property-type">
                                <option value="medium-house">Medium House</option>
                                <option value="small-house">Small House</option>
                                <option value="large-house">Large House</option>
                                <option value="apartment">Apartment</option>
                                <option value="business">Business</option>
                            </select>
                        </div>
                        
                        <div class="form-group">
                            <label for="property-size">Property Size (sq. ft):</label>
                            <input type="number" id="property-size" name="property-size" value="1200" min="0">
                        </div>
                        
                        <div class="form-group">
                            <label for="occupants">Number of Occupants:</label>
                            <input type="number" id="occupants" name="occupants" value="4" min="1">
                        </div>
                        
                        <div class="form-group">
                            <label for="heating-system">Primary Heating System:</label>
                            <select id="heating-system" name="heating-system">
                                <option value="natural-gas">Natural Gas</option>
                                <option value="electric">Electric</option>
                                <option value="oil">Oil</option>
                                <option value="propane">Propane</option>
                                <option value="heat-pump">Heat Pump</option>
                            </select>
                        </div>
                        
                        <div class="form-group">
                            <label for="cooling-months">Months of AC/Cooling Usage:</label>
                            <input type="number" id="cooling-months" name="cooling-months" value="3" min="0" max="12">
                        </div>
                        
                        <div class="button-group">
                            <button type="button" class="primary-btn" id="calculate-energy">Calculate Energy Usage</button>
                            <button type="reset" class="secondary-btn">Reset Calculator</button>
                        </div>
                    </form>
                    
                    <div class="results" id="energy-results">
                        <h3>Estimated Energy Usage</h3>
                        <p><strong>Estimated Annual Energy Consumption:</strong> <span id="total-energy"></span> kWh</p>
                        <p><strong>Estimated Monthly Energy Cost:</strong> £<span id="monthly-cost"></span></p>
                        <p><strong>Energy Usage Breakdown:</strong></p>
                        <p>Heating: <span id="heating-percent"></span>%</p>
                        <p>Cooling: <span id="cooling-percent"></span>%</p>
                        <p>Appliances & Lighting: <span id="appliances-percent"></span>%</p>
                        <p>Hot Water: <span id="water-percent"></span>%</p>
                        
                        <div class="tips">
                            <h4>Energy Efficiency Tips</h4>
                            <ul id="energy-tips">
                            </ul>
                        </div>
                    </div>
                </div>
            </div>
        </div>
    </section>

    <!-- Footer-->

    <footer>
        <div class="footer-content">
            <div class="footer-section">
                <h3>Blue Waves</h3>
                <p>Your trusted partner for innovative solutions since 2010. We're dedicated to helping businesses grow and succeed.</p>
            </div>
            <div class="footer-section">
                <h3>Quick Links</h3>
                <ul>
                    <li><a href="{% url 'index' %}">Home</a></li>
                    <li><a href="{% url 'about' %}">About Us</a></li>
                    <li><a href="{% url 'products' %}">Products</a></li>
                    <li><a href="{% url 'contact' %}">Contact</a></li>
                    <li><a href="{% url 'calculators' %}">Calculators</a></li>
                    {% if user.is_authenticated %}
                        <li><a href="{% url 'dashboard' %}">Member's Dashboard</a></li>
                    {% endif %}
                </ul>
            </div>
            <div class="footer-section">
                <h3>Contact Us</h3>
                <p>123 Business Avenue<br>
                Tech City, TC 12345<br>
                info@bluewaves.com<br>
                (123) 456-7890</p>
            </div>
        </div>
        <div class="copyright">
            © 2025 Rolsa Technologies. All rights reserved.
        </div>
    </footer>
    <script>
        // Carbon Footprint Calculator
        document.getElementById('calculate-carbon').addEventListener('click', function() {
            calculateCarbonFootprint();
        });

        function calculateCarbonFootprint() {
            // Get input values
            const transportation = document.getElementById('transportation').value;
            const commute = parseFloat(document.getElementById('commute').value) || 0;
            const electricity = parseFloat(document.getElementById('electricity').value) || 0;
            const diet = document.getElementById('diet').value;
            const flights = parseFloat(document.getElementById('flights').value) || 0;
            
            // Calculate carbon for transportation (tons CO2e per year)
            let transportCarbon = 0;
            switch(transportation) {
                case 'car':
                    transportCarbon = commute * 365 * 0.000404; // ~404g CO2 per mile
                    break;
                case 'electric-car':
                    transportCarbon = commute * 365 * 0.000202; // ~202g CO2 per mile
                    break;
                case 'bus':
                    transportCarbon = commute * 365 * 0.000299; // ~299g CO2 per mile
                    break;
                case 'train':
                    transportCarbon = commute * 365 * 0.000159; // ~159g CO2 per mile
                    break;
                case 'bicycle':
                    transportCarbon = 0; // No emissions
                    break;
            }
            
            // Calculate carbon for electricity (tons CO2e per year)
            const energyCarbon = electricity * 12 * 0.000454; // ~454g CO2 per kWh (US average)
            
            // Calculate carbon for diet (tons CO2e per year)
            let dietCarbon = 0;
            switch(diet) {
                case 'meat-rich':
                    dietCarbon = 2.5; // tons CO2e per year
                    break;
                case 'meat-moderate':
                    dietCarbon = 1.7;
                    break;
                case 'vegetarian':
                    dietCarbon = 1.4;
                    break;
                case 'vegan':
                    dietCarbon = 1.1;
                    break;
            }
            
            // Calculate carbon for flights (tons CO2e)
            const flightCarbon = flights * 0.6; // Average of 0.6 tons CO2e per flight
            
            // Total carbon footprint
            const totalCarbon = transportCarbon + energyCarbon + dietCarbon + flightCarbon;
            
            // Display results
            document.getElementById('total-carbon').textContent = totalCarbon.toFixed(2);
            document.getElementById('transport-carbon').textContent = transportCarbon.toFixed(2);
            document.getElementById('energy-carbon').textContent = energyCarbon.toFixed(2);
            document.getElementById('diet-carbon').textContent = dietCarbon.toFixed(2);
            document.getElementById('flight-carbon').textContent = flightCarbon.toFixed(2);
            
            // Show results
            document.getElementById('carbon-results').style.display = 'block';
            
            // Generate carbon reduction tips
            generateCarbonTips(transportation, commute, electricity, diet, flights);
        }
        
        function generateCarbonTips(transportation, commute, electricity, diet, flights) {
            const tipsList = document.getElementById('carbon-tips');
            tipsList.innerHTML = ''; // Clear previous tips
            
            // Transportation tips
            if (transportation === 'car' && commute > 10) {
                addTip(tipsList, 'Consider carpooling or using public transportation for your commute to reduce emissions.');
            }
            if (transportation === 'car') {
                addTip(tipsList, 'Switching to an electric or hybrid vehicle could reduce your transportation emissions by up to 50%.');
            }
            
            // Electricity tips
            if (electricity > 500) {
                addTip(tipsList, 'Switch to energy-efficient LED bulbs and ENERGY STAR appliances to reduce electricity consumption.');
                addTip(tipsList, 'Consider installing solar panels to generate renewable electricity for your home.');
            }
            
            // Diet tips
            if (diet === 'meat-rich' || diet === 'meat-moderate') {
                addTip(tipsList, 'Reducing meat consumption, especially beef, can significantly lower your carbon footprint.');
            }
            
            // Flight tips
            if (flights > 2) {
                addTip(tipsList, 'Consider taking fewer flights or purchasing carbon offsets for necessary air travel.');
            }
            
            // General tips
            addTip(tipsList, 'Plant trees or support reforestation projects to offset your carbon emissions.');
        }
        
        function addTip(list, text) {
            const li = document.createElement('li');
            li.textContent = text;
            list.appendChild(li);
        }
        
        // Energy Usage Calculator
        document.getElementById('calculate-energy').addEventListener('click', function() {
            calculateEnergyUsage();
        });
        
        function calculateEnergyUsage() {
            // Get input values
            const propertyType = document.getElementById('property-type').value;
            const propertySize = parseFloat(document.getElementById('property-size').value) || 0;
            const occupants = parseFloat(document.getElementById('occupants').value) || 1;
            const heatingSystem = document.getElementById('heating-system').value;
            const coolingMonths = parseFloat(document.getElementById('cooling-months').value) || 0;
            
            // Base energy usage by property type (kWh per year per sq ft)
            let baseEnergy = 0;
            switch(propertyType) {
                case 'small-house':
                    baseEnergy = 7;
                    break;
                case 'medium-house':
                    baseEnergy = 9;
                    break;
                case 'large-house':
                    baseEnergy = 11;
                    break;
                case 'apartment':
                    baseEnergy = 6;
                    break;
                case 'business':
                    baseEnergy = 14;
                    break;
            }
            
            // Heating system efficiency factor
            let heatingFactor = 1;
            switch(heatingSystem) {
                case 'natural-gas':
                    heatingFactor = 1.0;
                    break;
                case 'electric':
                    heatingFactor = 1.2;
                    break;
                case 'oil':
                    heatingFactor = 1.3;
                    break;
                case 'propane':
                    heatingFactor = 1.1;
                    break;
                case 'heat-pump':
                    heatingFactor = 0.7;
                    break;
            }
            
            // Cooling energy usage based on months of usage
            const coolingFactor = coolingMonths / 12 * 0.3;
            
            // Occupancy factor
            const occupancyFactor = 0.6 + (occupants * 0.1);
            
            // Calculate total energy usage
            const totalEnergy = propertySize * baseEnergy * heatingFactor * (1 + coolingFactor) * occupancyFactor;
            
            // Calculate monthly cost (average $0.15 per kWh)
            const monthlyCost = (totalEnergy * 0.15) / 12;
            
            // Calculate energy breakdown percentages
            const heatingPercent = Math.round(45 * heatingFactor);
            const coolingPercent = Math.round(10 * (coolingMonths / 3));
            const waterPercent = Math.round(15 * (occupants / 3));
            const appliancesPercent = 100 - heatingPercent - coolingPercent - waterPercent;
            
            // Display results
            document.getElementById('total-energy').textContent = Math.round(totalEnergy);
            document.getElementById('monthly-cost').textContent = monthlyCost.toFixed(2);
            document.getElementById('heating-percent').textContent = heatingPercent;
            document.getElementById('cooling-percent').textContent = coolingPercent;
            document.getElementById('water-percent').textContent = waterPercent;
            document.getElementById('appliances-percent').textContent = appliancesPercent;
            
            // Show results
            document.getElementById('energy-results').style.display = 'block';
            
            // Generate energy saving tips
            generateEnergySavingTips(propertyType, heatingSystem, coolingMonths, occupants);
        }
        
        function generateEnergySavingTips(propertyType, heatingSystem, coolingMonths, occupants) {
            const tipsList = document.getElementById('energy-tips');
            tipsList.innerHTML = ''; // Clear previous tips
            
            // Heating tips
            if (heatingSystem === 'electric' || heatingSystem === 'oil') {
                addTip(tipsList, 'Consider upgrading to a more efficient heating system like a heat pump to save energy.');
            }
            
            addTip(tipsList, 'Improve insulation in walls, attic, and floors to reduce heating and cooling needs.');
            
            // Cooling tips
            if (coolingMonths > 3) {
                addTip(tipsList, 'Install ceiling fans to reduce air conditioning usage.');
                addTip(tipsList, 'Use programmable thermostats to optimize cooling when you need it most.');
            }
            
            // General tips
            addTip(tipsList, 'Replace old appliances with ENERGY STAR rated models to reduce electricity consumption.');
            addTip(tipsList, 'Switch to LED lighting throughout your property.');
            
            if (occupants > 3) {
                addTip(tipsList, 'Install low-flow showerheads and faucets to reduce hot water usage.');
            }
            
            // Property-specific tips
            if (propertyType === 'business') {
                addTip(tipsList, 'Consider energy management systems to control lighting and HVAC during off-hours.');
            }
        }
        
        // Reset form functionality
        document.querySelectorAll('button[type="reset"]').forEach(button => {
            button.addEventListener('click', function() {
                const form = this.closest('form');
                const results = form.id === 'carbon-form' ? 
                    document.getElementById('carbon-results') : 
                    document.getElementById('energy-results');
                
                results.style.display = 'none';
                form.reset();
            });
        });
        
        // Theme toggle functionality
        document.getElementById('theme-toggle').addEventListener('click', function() {
            const html = document.documentElement;
            const themeIcon = document.querySelector('.theme-toggle .icon');
            const themeText = document.querySelector('.theme-toggle .toggle-text');
            
            if (html.getAttribute('data-theme') === 'light') {
                html.setAttribute('data-theme', 'dark');
                themeIcon.textContent = '🌙';
                themeText.textContent = 'Light Mode';
            } else {
                html.setAttribute('data-theme', 'light');
                themeIcon.textContent = '☀️';
                themeText.textContent = 'Dark Mode';
            }
        });
        
        // Mobile menu toggle
        document.querySelector('.mobile-toggle').addEventListener('click', function() {
            document.querySelector('nav ul').classList.toggle('show');
        });
    </script>
</body>
</html>

Cs

 /* Global Styles */
 :root {
    /* Light Theme (default) */
    --primary-blue: #1a4b8c;
    --secondary-blue: #2c7bb6;
    --light-blue: #a8d0e6;
    --dark-blue: #0d2b4d;
    --accent-blue: #3498db;
    --text-color: #333;
    --background-color: #f5f9fc;
    --white: #ffffff;
    --team-bg: #ffffff;
    --card-bg: #ffffff;
    --card-shadow: rgba(0, 0, 0, 0.05);
    --header-shadow: rgba(0, 0, 0, 0.2);
    --footer-border: rgba(255, 255, 255, 0.1);
    --footer-bg: #121212;
    --footer-text: #f5f5f5;
}

/* Dark Theme */
html[data-theme='dark'] {
    --primary-blue: #1a4b8c;
    --secondary-blue: #2c7bb6;
    --light-blue: #a8d0e6;
    --dark-blue: #0d2b4d;
    --accent-blue: #3498db;
    --text-color: #e0e0e0;
    --background-color: #121212;
    --white: #1e1e1e;
    --team-bg: #1e1e1e;
    --card-bg: #2a2a2a;
    --footer-bg: #000000;
    --footer-text: #f5f5f5;
    --feature-shadow: rgba(0, 0, 0, 0.2);
    --feature-hover-shadow: rgba(0, 0, 0, 0.4);
    --card-shadow: rgba(0, 0, 0, 0.2);
    --header-shadow: rgba(0, 0, 0, 0.4);
    --footer-border: rgba(255, 255, 255, 0.05);
}

* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
    font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
}

body {
    background-color: var(--background-color);
    color: var(--text-color);
    line-height: 1.6;
    transition: background-color 0.3s ease, color 0.3s ease;
}

/* Layout */
.container {
    width: 100%;
    max-width: 1200px;
    margin: 0 auto;
    padding: 0 20px;
}

/* Header */
header {
    background-color: var(--primary-blue);
    color: var(--white);
    padding: 20px 0;
    box-shadow: 0 2px 10px var(--header-shadow);
    position: sticky;
    top: 0;
    z-index: 100;
    transition: background-color 0.3s ease;
}

.header-content {
    display: flex;
    justify-content: space-between;
    align-items: center;
}

.logo {
    width: 100px;
    height: auto;
    border-radius: 15px;
    padding: 5px;
}

/* Navigation */
nav ul {
    display: flex;
    list-style: none;
    align-items: center;
}

nav ul li {
    margin-left: 20px;
}

nav ul li a {
    color: var(--white);
    text-decoration: none;
    font-weight: 500;
    transition: color 0.3s;
    position: relative;
    padding-bottom: 5px;
}

nav ul li a:hover {
    color: var(--light-blue);
}

nav ul li a.active {
    color: var(--light-blue);
}

nav ul li a.active::after {
    content: '';
    position: absolute;
    bottom: 0;
    left: 0;
    width: 100%;
    height: 2px;
    background-color: var(--light-blue);
}

.mobile-toggle {
    display: none;
    font-size: 24px;
    cursor: pointer;
    color: var(--white);
}

/* Theme Toggle Button */
.theme-toggle {
    background: none;
    border: none;
    cursor: pointer;
    display: flex;
    align-items: center;
    color: var(--white);
    font-size: 14px;
    padding: 5px 10px;
    border-radius: 20px;
    background-color: rgba(255, 255, 255, 0.1);
    transition: background-color 0.3s;
}

.theme-toggle:hover {
    background-color: rgba(255, 255, 255, 0.2);
}

.theme-toggle .icon {
    margin-right: 5px;
    font-size: 16px;
}

/* Page Header */
.page-header {
    background: linear-gradient(135deg, var(--primary-blue), var(--secondary-blue));
    color: var(--white);
    padding: 60px 0;
    text-align: center;
    transition: background 0.3s ease;
}

.page-header h1 {
    font-size: 42px;
    margin-bottom: 15px;
}

.breadcrumb {
    display: flex;
    justify-content: center;
    list-style: none;
}

.breadcrumb li {
    margin: 0 5px;
}

.breadcrumb li a {
    color: var(--light-blue);
    text-decoration: none;
}

.breadcrumb li a:hover {
    text-decoration: underline;
}

/* Calculator Section */


.calculators-section {
    padding: 60px 0;
}

.calculators-grid {
    display: grid;
    grid-template-columns: 1fr 1fr;
    gap: 30px;
    margin-top: 40px;
}

.calculator {
    background-color: var(--card-bg);
    border-radius: 15px;
    box-shadow: 0 10px 30px var(--card-shadow);
    padding: 30px;
    transition: transform 0.3s ease, box-shadow 0.3s ease;
}

.calculator:hover {
    transform: translateY(-5px);
    box-shadow: 0 15px 40px var(--card-shadow);
}

.calculator h2 {
    color: var(--primary-blue);
    margin-top: 0;
    padding-bottom: 10px;
    border-bottom: 2px solid var(--light-blue);
    font-size: 24px;
}

.calculator p {
    color: var(--text-color);
    font-size: 14px;
    line-height: 1.5;
    margin-bottom: 20px;
}

.form-group {
    margin-bottom: 15px;
}

.form-group label {
    display: block;
    font-weight: 600;
    margin-bottom: 5px;
    color: var(--text-color);
    font-size: 14px;
}

.form-group select, .form-group input {
    width: 100%;
    padding: 12px;
    border: 1px solid var(--light-blue);
    border-radius: 8px;
    background-color: var(--white);
    color: var(--text-color);
    font-size: 14px;
    transition: all 0.3s ease;
}

.form-group select:focus, .form-group input:focus {
    border-color: var(--secondary-blue);
    outline: none;
    box-shadow: 0 0 0 3px rgba(44, 123, 182, 0.2);
}

.button-group {
    display: flex;
    gap: 10px;
    margin-top: 20px;
}

button {
    padding: 12px 20px;
    border: none;
    border-radius: 8px;
    cursor: pointer;
    font-weight: 600;
    font-size: 14px;
    transition: all 0.3s ease;
}

.primary-btn {
    background-color: var(--primary-blue);
    color: white;
    flex: 3;
}

.secondary-btn {
    background-color: #f0f0f0;
    color: var(--text-color);
    flex: 2;
}

.primary-btn:hover {
    background-color: var(--dark-blue);
}

.secondary-btn:hover {
    background-color: #e0e0e0;
}

.results {
    margin-top: 20px;
    padding: 20px;
    background-color: rgba(168, 208, 230, 0.2);
    border-radius: 8px;
    display: none;
}

.results h3 {
    color: var(--primary-blue);
    margin-top: 0;
    margin-bottom: 15px;
}

.results p {
    margin: 5px 0;
}

.note {
    font-size: 12px;
    color: #888;
    margin-top: 15px;
    font-style: italic;
}

.tips {
    margin-top: 15px;
    padding: 15px;
    background-color: rgba(52, 152, 219, 0.1);
    border-radius: 8px;
}

.tips h4 {
    margin-top: 0;
    color: var(--primary-blue);
    margin-bottom: 10px;
}

.tips ul {
    margin: 0;
    padding-left: 20px;
}

.tips li {
    margin-bottom: 5px;
    font-size: 13px;
}

/* Responsive adjustments */
@media (max-width: 992px) {
    .calculators-grid {
        grid-template-columns: 1fr;
        gap: 40px;
    }
}
/* Footer */
footer {
    background-color: var(--footer-bg);
    color: var(--footer-text);
    padding: 50px 0 20px;
}

.footer-content {
    display: grid;
    grid-template-columns: repeat(3, 1fr);
    gap: 30px;
    max-width: 1200px;
    margin: 0 auto;
    padding: 0 20px;
}

.footer-section h3 {
    margin-bottom: 20px;
    position: relative;
    padding-bottom: 10px;
    font-size: 1.2rem;
    color: #fff;
    border-bottom: 1px solid rgba(255, 255, 255, 0.2);
    display: inline-block;
}

.footer-section p {
    line-height: 1.6;
    color: rgba(255, 255, 255, 0.8);
}

.footer-section ul {
    list-style: none;
    padding: 0;
}

.footer-section ul li {
    margin-bottom: 10px;
}

.footer-section ul li a {
    color: rgba(255, 255, 255, 0.8);
    text-decoration: none;
    transition: color 0.3s;
}

.footer-section ul li a:hover {
    color: #fff;
    text-decoration: underline;
}

.copyright {
    text-align: center;
    padding-top: 40px;
    margin-top: 40px;
    border-top: 1px solid rgba(255, 255, 255, 0.1);
    font-size: 0.9rem;
    color: rgba(255, 255, 255, 0.7);
}

@media screen and (max-width: 768px) {
    .footer-content {
        grid-template-columns: 1fr;
    }
}
/* Responsive Styles */
@media (max-width: 992px) {
    .calculators-grid {
        grid-template-columns: 1fr;
        gap: 40px;
    }
}

@media (max-width: 768px) {
    .mobile-toggle {
        display: block;
    }
    
    nav ul {
        position: absolute;
        top: 70px;
        left: 0;
        right: 0;
        background-color: var(--primary-blue);
        flex-direction: column;
        padding: 20px;
        display: none;
        box-shadow: 0 5px 10px rgba(0, 0, 0, 0.1);
    }
    
    nav ul.show {
        display: flex;
    }
    
    nav ul li {
        margin: 15px 0;
    }
    
    .page-header h1 {
        font-size: 32px;
    }
}

@media (max-width: 480px) {
    .page-header h1 {
        font-size: 28px;
    }
}


        """
        Assert that a field named "field" on the given form object has specific
        errors.

        errors can be either a single error message or a list of errors
        messages. Using errors=[] test that the field has no errors.

        You can pass field=None to check the form's non-field errors.
        """
        if errors is None:
            warnings.warn(
                "Passing errors=None to assertFormError() is deprecated, use "
                "errors=[] instead.",
                RemovedInDjango50Warning,
                stacklevel=2,
            )
            errors = []

        if msg_prefix:
            msg_prefix += ": "
        errors = to_list(errors)
        self._assert_form_error(form, field, errors, msg_prefix, f"form {form!r}")

    # RemovedInDjango51Warning.
    def assertFormsetError(self, *args, **kw):
        warnings.warn(
            "assertFormsetError() is deprecated in favor of assertFormSetError().",
            category=RemovedInDjango51Warning,
            stacklevel=2,
        )
        return self.assertFormSetError(*args, **kw)

    # RemovedInDjango50Warning: When the deprecation ends, remove the
    # decorator.
    @_AssertFormErrorDeprecationHelper.patch_signature
    def assertFormSetError(self, formset, form_index, field, errors, msg_prefix=""):
        """
        Similar to assertFormError() but for formsets.

        Use form_index=None to check the formset's non-form errors (in that
        case, you must also use field=None).
        Otherwise use an integer to check the formset's n-th form for errors.

        Other parameters are the same as assertFormError().
        """
        if errors is None:
            warnings.warn(
                "Passing errors=None to assertFormSetError() is deprecated, "
                "use errors=[] instead.",
                RemovedInDjango50Warning,
                stacklevel=2,
            )
            errors = []

        if form_index is None and field is not None:
            raise ValueError("You must use field=None with form_index=None.")

        if msg_prefix:
            msg_prefix += ": "
        errors = to_list(errors)

        if not formset.is_bound:
            self.fail(
                f"{msg_prefix}The formset {formset!r} is not bound, it will never have "
                f"any errors."
            )
        if form_index is not None and form_index >= formset.total_form_count():
            form_count = formset.total_form_count()
            form_or_forms = "forms" if form_count > 1 else "form"
            self.fail(
                f"{msg_prefix}The formset {formset!r} only has {form_count} "
                f"{form_or_forms}."
            )
        if form_index is not None:
            form_repr = f"form {form_index} of formset {formset!r}"
            self._assert_form_error(
                formset.forms[form_index], field, errors, msg_prefix, form_repr
            )
        else:
            failure_message = f"The non-form errors of formset {formset!r} don't match."
            self.assertEqual(
                formset.non_form_errors(), errors, msg_prefix + failure_message
            )

    def _get_template_used(self, response, template_name, msg_prefix, method_name):
        if response is None and template_name is None:
            raise TypeError("response and/or template_name argument must be provided")

        if msg_prefix:
            msg_prefix += ": "

        if template_name is not None and response is not None:
            self._check_test_client_response(response, "templates", method_name)

        if not hasattr(response, "templates") or (response is None and template_name):
            if response:
                template_name = response
                response = None
            # use this template with context manager
            return template_name, None, msg_prefix

        template_names = [t.name for t in response.templates if t.name is not None]
        return None, template_names, msg_prefix

    def _assert_template_used(self, template_name, template_names, msg_prefix, count):
        if not template_names:
            self.fail(msg_prefix + "No templates used to render the response")
        self.assertTrue(
            template_name in template_names,
            msg_prefix + "Template '%s' was not a template used to render"
            " the response. Actual template(s) used: %s"
            % (template_name, ", ".join(template_names)),
        )

        if count is not None:
            self.assertEqual(
                template_names.count(template_name),
                count,
                msg_prefix + "Template '%s' was expected to be rendered %d "
                "time(s) but was actually rendered %d time(s)."
                % (template_name, count, template_names.count(template_name)),
            )

    def assertTemplateUsed(
        self, response=None, template_name=None, msg_prefix="", count=None
    ):
        """
        Assert that the template with the provided name was used in rendering
        the response. Also usable as context manager.
        """
        context_mgr_template, template_names, msg_prefix = self._get_template_used(
            response,
            template_name,
            msg_prefix,
            "assertTemplateUsed",
        )
        if context_mgr_template:
            # Use assertTemplateUsed as context manager.
            return _AssertTemplateUsedContext(
                self, context_mgr_template, msg_prefix, count
            )

        self._assert_template_used(template_name, template_names, msg_prefix, count)

    def assertTemplateNotUsed(self, response=None, template_name=None, msg_prefix=""):
        """
        Assert that the template with the provided name was NOT used in
        rendering the response. Also usable as context manager.
        """
        context_mgr_template, template_names, msg_prefix = self._get_template_used(
            response,
            template_name,
            msg_prefix,
            "assertTemplateNotUsed",
        )
        if context_mgr_template:
            # Use assertTemplateNotUsed as context manager.
            return _AssertTemplateNotUsedContext(self, context_mgr_template, msg_prefix)

        self.assertFalse(
            template_name in template_names,
            msg_prefix
            + "Template '%s' was used unexpectedly in rendering the response"
            % template_name,
        )

    @contextmanager
    def _assert_raises_or_warns_cm(
        self, func, cm_attr, expected_exception, expected_message
    ):
        with func(expected_exception) as cm:
            yield cm
        self.assertIn(expected_message, str(getattr(cm, cm_attr)))

    def _assertFooMessage(
        self, func, cm_attr, expected_exception, expected_message, *args, **kwargs
    ):
        callable_obj = None
        if args:
            callable_obj, *args = args
        cm = self._assert_raises_or_warns_cm(
            func, cm_attr, expected_exception, expected_message
        )
        # Assertion used in context manager fashion.
        if callable_obj is None:
            return cm
        # Assertion was passed a callable.
        with cm:
            callable_obj(*args, **kwargs)

    def assertRaisesMessage(
        self, expected_exception, expected_message, *args, **kwargs
    ):
        """
        Assert that expected_message is found in the message of a raised
        exception.

        Args:
            expected_exception: Exception class expected to be raised.
            expected_message: expected error message string value.
            args: Function to be called and extra positional args.
            kwargs: Extra kwargs.
        """
        return self._assertFooMessage(
            self.assertRaises,
            "exception",
            expected_exception,
            expected_message,
            *args,
            **kwargs,
        )

    def assertWarnsMessage(self, expected_warning, expected_message, *args, **kwargs):
        """
        Same as assertRaisesMessage but for assertWarns() instead of
        assertRaises().
        """
        return self._assertFooMessage(
            self.assertWarns,
            "warning",
            expected_warning,
            expected_message,
            *args,
            **kwargs,
        )

    # A similar method is available in Python 3.10+.
    if not PY310:

        @contextmanager
        def assertNoLogs(self, logger, level=None):
            """
            Assert no messages are logged on the logger, with at least the
            given level.
            """
            if isinstance(level, int):
                level = logging.getLevelName(level)
            elif level is None:
                level = "INFO"
            try:
                with self.assertLogs(logger, level) as cm:
                    yield
            except AssertionError as e:
                msg = e.args[0]
                expected_msg = (
                    f"no logs of level {level} or higher triggered on {logger}"
                )
                if msg != expected_msg:
                    raise e
            else:
                self.fail(f"Unexpected logs found: {cm.output!r}")

    def assertFieldOutput(
        self,
        fieldclass,
        valid,
        invalid,
        field_args=None,
        field_kwargs=None,
        empty_value="",
    ):
        """
        Assert that a form field behaves correctly with various inputs.

        Args:
            fieldclass: the class of the field to be tested.
            valid: a dictionary mapping valid inputs to their expected
                    cleaned values.
            invalid: a dictionary mapping invalid inputs to one or more
                    raised error messages.
            field_args: the args passed to instantiate the field
            field_kwargs: the kwargs passed to instantiate the field
            empty_value: the expected clean output for inputs in empty_values
        """
        if field_args is None:
            field_args = []
        if field_kwargs is None:
            field_kwargs = {}
        required = fieldclass(*field_args, **field_kwargs)
        optional = fieldclass(*field_args, **{**field_kwargs, "required": False})
        # test valid inputs
        for input, output in valid.items():
            self.assertEqual(required.clean(input), output)
            self.assertEqual(optional.clean(input), output)
        # test invalid inputs
        for input, errors in invalid.items():
            with self.assertRaises(ValidationError) as context_manager:
                required.clean(input)
            self.assertEqual(context_manager.exception.messages, errors)

            with self.assertRaises(ValidationError) as context_manager:
                optional.clean(input)
            self.assertEqual(context_manager.exception.messages, errors)
        # test required inputs
        error_required = [required.error_messages["required"]]
        for e in required.empty_values:
            with self.assertRaises(ValidationError) as context_manager:
                required.clean(e)
            self.assertEqual(context_manager.exception.messages, error_required)
            self.assertEqual(optional.clean(e), empty_value)
        # test that max_length and min_length are always accepted
        if issubclass(fieldclass, CharField):
            field_kwargs.update({"min_length": 2, "max_length": 20})
            self.assertIsInstance(fieldclass(*field_args, **field_kwargs), fieldclass)

    def assertHTMLEqual(self, html1, html2, msg=None):
        """
        Assert that two HTML snippets are semantically the same.
        Whitespace in most cases is ignored, and attribute ordering is not
        significant. The arguments must be valid HTML.
        """
        dom1 = assert_and_parse_html(
            self, html1, msg, "First argument is not valid HTML:"
        )
        dom2 = assert_and_parse_html(
            self, html2, msg, "Second argument is not valid HTML:"
        )

        if dom1 != dom2:
            standardMsg = "%s != %s" % (safe_repr(dom1, True), safe_repr(dom2, True))
            diff = "\n" + "\n".join(
                difflib.ndiff(
                    str(dom1).splitlines(),
                    str(dom2).splitlines(),
                )
            )
            standardMsg = self._truncateMessage(standardMsg, diff)
            self.fail(self._formatMessage(msg, standardMsg))

    def assertHTMLNotEqual(self, html1, html2, msg=None):
        """Assert that two HTML snippets are not semantically equivalent."""
        dom1 = assert_and_parse_html(
            self, html1, msg, "First argument is not valid HTML:"
        )
        dom2 = assert_and_parse_html(
            self, html2, msg, "Second argument is not valid HTML:"
        )

        if dom1 == dom2:
            standardMsg = "%s == %s" % (safe_repr(dom1, True), safe_repr(dom2, True))
            self.fail(self._formatMessage(msg, standardMsg))

    def assertInHTML(self, needle, haystack, count=None, msg_prefix=""):
        needle = assert_and_parse_html(
            self, needle, None, "First argument is not valid HTML:"
        )
        haystack = assert_and_parse_html(
            self, haystack, None, "Second argument is not valid HTML:"
        )
        real_count = haystack.count(needle)
        if count is not None:
            self.assertEqual(
                real_count,
                count,
                msg_prefix
                + "Found %d instances of '%s' in response (expected %d)"
                % (real_count, needle, count),
            )
        else:
            self.assertTrue(
                real_count != 0, msg_prefix + "Couldn't find '%s' in response" % needle
            )

    def assertJSONEqual(self, raw, expected_data, msg=None):
        """
        Assert that the JSON fragments raw and expected_data are equal.
        Usual JSON non-significant whitespace rules apply as the heavyweight
        is delegated to the json library.
        """
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            self.fail("First argument is not valid JSON: %r" % raw)
        if isinstance(expected_data, str):
            try:
                expected_data = json.loads(expected_data)
            except ValueError:
                self.fail("Second argument is not valid JSON: %r" % expected_data)
        self.assertEqual(data, expected_data, msg=msg)

    def assertJSONNotEqual(self, raw, expected_data, msg=None):
        """
        Assert that the JSON fragments raw and expected_data are not equal.
        Usual JSON non-significant whitespace rules apply as the heavyweight
        is delegated to the json library.
        """
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            self.fail("First argument is not valid JSON: %r" % raw)
        if isinstance(expected_data, str):
            try:
                expected_data = json.loads(expected_data)
            except json.JSONDecodeError:
                self.fail("Second argument is not valid JSON: %r" % expected_data)
        self.assertNotEqual(data, expected_data, msg=msg)

    def assertXMLEqual(self, xml1, xml2, msg=None):
        """
        Assert that two XML snippets are semantically the same.
        Whitespace in most cases is ignored and attribute ordering is not
        significant. The arguments must be valid XML.
        """
        try:
            result = compare_xml(xml1, xml2)
        except Exception as e:
            standardMsg = "First or second argument is not valid XML\n%s" % e
            self.fail(self._formatMessage(msg, standardMsg))
        else:
            if not result:
                standardMsg = "%s != %s" % (
                    safe_repr(xml1, True),
                    safe_repr(xml2, True),
                )
                diff = "\n" + "\n".join(
                    difflib.ndiff(xml1.splitlines(), xml2.splitlines())
                )
                standardMsg = self._truncateMessage(standardMsg, diff)
                self.fail(self._formatMessage(msg, standardMsg))

    def assertXMLNotEqual(self, xml1, xml2, msg=None):
        """
        Assert that two XML snippets are not semantically equivalent.
        Whitespace in most cases is ignored and attribute ordering is not
        significant. The arguments must be valid XML.
        """
        try:
            result = compare_xml(xml1, xml2)
        except Exception as e:
            standardMsg = "First or second argument is not valid XML\n%s" % e
            self.fail(self._formatMessage(msg, standardMsg))
        else:
            if result:
                standardMsg = "%s == %s" % (
                    safe_repr(xml1, True),
                    safe_repr(xml2, True),
                )
                self.fail(self._formatMessage(msg, standardMsg))


class TransactionTestCase(SimpleTestCase):
    # Subclasses can ask for resetting of auto increment sequence before each
    # test case
    reset_sequences = False

    # Subclasses can enable only a subset of apps for faster tests
    available_apps = None

    # Subclasses can define fixtures which will be automatically installed.
    fixtures = None

    databases = {DEFAULT_DB_ALIAS}
    _disallowed_database_msg = (
        "Database %(operation)s to %(alias)r are not allowed in this test. "
        "Add %(alias)r to %(test)s.databases to ensure proper test isolation "
        "and silence this failure."
    )

    # If transactions aren't available, Django will serialize the database
    # contents into a fixture during setup and flush and reload them
    # during teardown (as flush does not restore data from migrations).
    # This can be slow; this flag allows enabling on a per-case basis.
    serialized_rollback = False

    def _pre_setup(self):
        """
        Perform pre-test setup:
        * If the class has an 'available_apps' attribute, restrict the app
          registry to these applications, then fire the post_migrate signal --
          it must run with the correct set of applications for the test case.
        * If the class has a 'fixtures' attribute, install those fixtures.
        """
        super()._pre_setup()
        if self.available_apps is not None:
            apps.set_available_apps(self.available_apps)
            setting_changed.send(
                sender=settings._wrapped.__class__,
                setting="INSTALLED_APPS",
                value=self.available_apps,
                enter=True,
            )
            for db_name in self._databases_names(include_mirrors=False):
                emit_post_migrate_signal(verbosity=0, interactive=False, db=db_name)
        try:
            self._fixture_setup()
        except Exception:
            if self.available_apps is not None:
                apps.unset_available_apps()
                setting_changed.send(
                    sender=settings._wrapped.__class__,
                    setting="INSTALLED_APPS",
                    value=settings.INSTALLED_APPS,
                    enter=False,
                )
            raise
        # Clear the queries_log so that it's less likely to overflow (a single
        # test probably won't execute 9K queries). If queries_log overflows,
        # then assertNumQueries() doesn't work.
        for db_name in self._databases_names(include_mirrors=False):
            connections[db_name].queries_log.clear()

    @classmethod
    def _databases_names(cls, include_mirrors=True):
        # Only consider allowed database aliases, including mirrors or not.
        return [
            alias
            for alias in connections
            if alias in cls.databases
            and (
                include_mirrors
                or not connections[alias].settings_dict["TEST"]["MIRROR"]
            )
        ]

    def _reset_sequences(self, db_name):
        conn = connections[db_name]
        if conn.features.supports_sequence_reset:
            sql_list = conn.ops.sequence_reset_by_name_sql(
                no_style(), conn.introspection.sequence_list()
            )
            if sql_list:
                with transaction.atomic(using=db_name):
                    with conn.cursor() as cursor:
                        for sql in sql_list:
                            cursor.execute(sql)

    def _fixture_setup(self):
        for db_name in self._databases_names(include_mirrors=False):
            # Reset sequences
            if self.reset_sequences:
                self._reset_sequences(db_name)

            # Provide replica initial data from migrated apps, if needed.
            if self.serialized_rollback and hasattr(
                connections[db_name], "_test_serialized_contents"
            ):
                if self.available_apps is not None:
                    apps.unset_available_apps()
                connections[db_name].creation.deserialize_db_from_string(
                    connections[db_name]._test_serialized_contents
                )
                if self.available_apps is not None:
                    apps.set_available_apps(self.available_apps)

            if self.fixtures:
                # We have to use this slightly awkward syntax due to the fact
                # that we're using *args and **kwargs together.
                call_command(
                    "loaddata", *self.fixtures, **{"verbosity": 0, "database": db_name}
                )

    def _should_reload_connections(self):
        return True

    def _post_teardown(self):
        """
        Perform post-test things:
        * Flush the contents of the database to leave a clean slate. If the
          class has an 'available_apps' attribute, don't fire post_migrate.
        * Force-close the connection so the next test gets a clean cursor.
        """
        try:
            self._fixture_teardown()
            super()._post_teardown()
            if self._should_reload_connections():
                # Some DB cursors include SQL statements as part of cursor
                # creation. If you have a test that does a rollback, the effect
                # of these statements is lost, which can affect the operation of
                # tests (e.g., losing a timezone setting causing objects to be
                # created with the wrong time). To make sure this doesn't
                # happen, get a clean connection at the start of every test.
                for conn in connections.all(initialized_only=True):
                    conn.close()
        finally:
            if self.available_apps is not None:
                apps.unset_available_apps()
                setting_changed.send(
                    sender=settings._wrapped.__class__,
                    setting="INSTALLED_APPS",
                    value=settings.INSTALLED_APPS,
                    enter=False,
                )

    def _fixture_teardown(self):
        # Allow TRUNCATE ... CASCADE and don't emit the post_migrate signal
        # when flushing only a subset of the apps
        for db_name in self._databases_names(include_mirrors=False):
            # Flush the database
            inhibit_post_migrate = (
                self.available_apps is not None
                or (  # Inhibit the post_migrate signal when using serialized
                    # rollback to avoid trying to recreate the serialized data.
                    self.serialized_rollback
                    and hasattr(connections[db_name], "_test_serialized_contents")
                )
            )
            call_command(
                "flush",
                verbosity=0,
                interactive=False,
                database=db_name,
                reset_sequences=False,
                allow_cascade=self.available_apps is not None,
                inhibit_post_migrate=inhibit_post_migrate,
            )

    # RemovedInDjango51Warning.
    def assertQuerysetEqual(self, *args, **kw):
        warnings.warn(
            "assertQuerysetEqual() is deprecated in favor of assertQuerySetEqual().",
            category=RemovedInDjango51Warning,
            stacklevel=2,
        )
        return self.assertQuerySetEqual(*args, **kw)

    def assertQuerySetEqual(self, qs, values, transform=None, ordered=True, msg=None):
        values = list(values)
        items = qs
        if transform is not None:
            items = map(transform, items)
        if not ordered:
            return self.assertDictEqual(Counter(items), Counter(values), msg=msg)
        # For example qs.iterator() could be passed as qs, but it does not
        # have 'ordered' attribute.
        if len(values) > 1 and hasattr(qs, "ordered") and not qs.ordered:
            raise ValueError(
                "Trying to compare non-ordered queryset against more than one "
                "ordered value."
            )
        return self.assertEqual(list(items), values, msg=msg)

    def assertNumQueries(self, num, func=None, *args, using=DEFAULT_DB_ALIAS, **kwargs):
        conn = connections[using]

        context = _AssertNumQueriesContext(self, num, conn)
        if func is None:
            return context

        with context:
            func(*args, **kwargs)


def connections_support_transactions(aliases=None):
    """
    Return whether or not all (or specified) connections support
    transactions.
    """
    conns = (
        connections.all()
        if aliases is None
        else (connections[alias] for alias in aliases)
    )
    return all(conn.features.supports_transactions for conn in conns)


class TestData:
    """
    Descriptor to provide TestCase instance isolation for attributes assigned
    during the setUpTestData() phase.

    Allow safe alteration of objects assigned in setUpTestData() by test
    methods by exposing deep copies instead of the original objects.

    Objects are deep copied using a memo kept on the test case instance in
    order to maintain their original relationships.
    """

    memo_attr = "_testdata_memo"

    def __init__(self, name, data):
        self.name = name
        self.data = data

    def get_memo(self, testcase):
        try:
            memo = getattr(testcase, self.memo_attr)
        except AttributeError:
            memo = {}
            setattr(testcase, self.memo_attr, memo)
        return memo

    def __get__(self, instance, owner):
        if instance is None:
            return self.data
        memo = self.get_memo(instance)
        data = deepcopy(self.data, memo)
        setattr(instance, self.name, data)
        return data

    def __repr__(self):
        return "<TestData: name=%r, data=%r>" % (self.name, self.data)


class TestCase(TransactionTestCase):
    """
    Similar to TransactionTestCase, but use `transaction.atomic()` to achieve
    test isolation.

    In most situations, TestCase should be preferred to TransactionTestCase as
    it allows faster execution. However, there are some situations where using
    TransactionTestCase might be necessary (e.g. testing some transactional
    behavior).

    On database backends with no transaction support, TestCase behaves as
    TransactionTestCase.
    """

    @classmethod
    def _enter_atomics(cls):
        """Open atomic blocks for multiple databases."""
        atomics = {}
        for db_name in cls._databases_names():
            atomic = transaction.atomic(using=db_name)
            atomic._from_testcase = True
            atomic.__enter__()
            atomics[db_name] = atomic
        return atomics

    @classmethod
    def _rollback_atomics(cls, atomics):
        """Rollback atomic blocks opened by the previous method."""
        for db_name in reversed(cls._databases_names()):
            transaction.set_rollback(True, using=db_name)
            atomics[db_name].__exit__(None, None, None)

    @classmethod
    def _databases_support_transactions(cls):
        return connections_support_transactions(cls.databases)

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        if not cls._databases_support_transactions():
            return
        cls.cls_atomics = cls._enter_atomics()

        if cls.fixtures:
            for db_name in cls._databases_names(include_mirrors=False):
                try:
                    call_command(
                        "loaddata",
                        *cls.fixtures,
                        **{"verbosity": 0, "database": db_name},
                    )
                except Exception:
                    cls._rollback_atomics(cls.cls_atomics)
                    raise
        pre_attrs = cls.__dict__.copy()
        try:
            cls.setUpTestData()
        except Exception:
            cls._rollback_atomics(cls.cls_atomics)
            raise
        for name, value in cls.__dict__.items():
            if value is not pre_attrs.get(name):
                setattr(cls, name, TestData(name, value))

    @classmethod
    def tearDownClass(cls):
        if cls._databases_support_transactions():
            cls._rollback_atomics(cls.cls_atomics)
            for conn in connections.all(initialized_only=True):
                conn.close()
        super().tearDownClass()

    @classmethod
    def setUpTestData(cls):
        """Load initial data for the TestCase."""
        pass

    def _should_reload_connections(self):
        if self._databases_support_transactions():
            return False
        return super()._should_reload_connections()

    def _fixture_setup(self):
        if not self._databases_support_transactions():
            # If the backend does not support transactions, we should reload
            # class data before each test
            self.setUpTestData()
            return super()._fixture_setup()

        if self.reset_sequences:
            raise TypeError("reset_sequences cannot be used on TestCase instances")
        self.atomics = self._enter_atomics()

    def _fixture_teardown(self):
        if not self._databases_support_transactions():
            return super()._fixture_teardown()
        try:
            for db_name in reversed(self._databases_names()):
                if self._should_check_constraints(connections[db_name]):
                    connections[db_name].check_constraints()
        finally:
            self._rollback_atomics(self.atomics)

    def _should_check_constraints(self, connection):
        return (
            connection.features.can_defer_constraint_checks
            and not connection.needs_rollback
            and connection.is_usable()
        )

    @classmethod
    @contextmanager
    def captureOnCommitCallbacks(cls, *, using=DEFAULT_DB_ALIAS, execute=False):
        """Context manager to capture transaction.on_commit() callbacks."""
        callbacks = []
        start_count = len(connections[using].run_on_commit)
        try:
            yield callbacks
        finally:
            while True:
                callback_count = len(connections[using].run_on_commit)
                for _, callback, robust in connections[using].run_on_commit[
                    start_count:
                ]:
                    callbacks.append(callback)
                    if execute:
                        if robust:
                            try:
                                callback()
                            except Exception as e:
                                logger.error(
                                    f"Error calling {callback.__qualname__} in "
                                    f"on_commit() (%s).",
                                    e,
                                    exc_info=True,
                                )
                        else:
                            callback()

                if callback_count == len(connections[using].run_on_commit):
                    break
                start_count = callback_count


class CheckCondition:
    """Descriptor class for deferred condition checking."""

    def __init__(self, *conditions):
        self.conditions = conditions

    def add_condition(self, condition, reason):
        return self.__class__(*self.conditions, (condition, reason))

    def __get__(self, instance, cls=None):
        # Trigger access for all bases.
        if any(getattr(base, "__unittest_skip__", False) for base in cls.__bases__):
            return True
        for condition, reason in self.conditions:
            if condition():
                # Override this descriptor's value and set the skip reason.
                cls.__unittest_skip__ = True
                cls.__unittest_skip_why__ = reason
                return True
        return False


def _deferredSkip(condition, reason, name):
    def decorator(test_func):
        nonlocal condition
        if not (
            isinstance(test_func, type) and issubclass(test_func, unittest.TestCase)
        ):

            @wraps(test_func)
            def skip_wrapper(*args, **kwargs):
                if (
                    args
                    and isinstance(args[0], unittest.TestCase)
                    and connection.alias not in getattr(args[0], "databases", {})
                ):
                    raise ValueError(
                        "%s cannot be used on %s as %s doesn't allow queries "
                        "against the %r database."
                        % (
                            name,
                            args[0],
                            args[0].__class__.__qualname__,
                            connection.alias,
                        )
                    )
                if condition():
                    raise unittest.SkipTest(reason)
                return test_func(*args, **kwargs)

            test_item = skip_wrapper
        else:
            # Assume a class is decorated
            test_item = test_func
            databases = getattr(test_item, "databases", None)
            if not databases or connection.alias not in databases:
                # Defer raising to allow importing test class's module.
                def condition():
                    raise ValueError(
                        "%s cannot be used on %s as it doesn't allow queries "
                        "against the '%s' database."
                        % (
                            name,
                            test_item,
                            connection.alias,
                        )
                    )

            # Retrieve the possibly existing value from the class's dict to
            # avoid triggering the descriptor.
            skip = test_func.__dict__.get("__unittest_skip__")
            if isinstance(skip, CheckCondition):
                test_item.__unittest_skip__ = skip.add_condition(condition, reason)
            elif skip is not True:
                test_item.__unittest_skip__ = CheckCondition((condition, reason))
        return test_item

    return decorator


def skipIfDBFeature(*features):
    """Skip a test if a database has at least one of the named features."""
    return _deferredSkip(
        lambda: any(
            getattr(connection.features, feature, False) for feature in features
        ),
        "Database has feature(s) %s" % ", ".join(features),
        "skipIfDBFeature",
    )


def skipUnlessDBFeature(*features):
    """Skip a test unless a database has all the named features."""
    return _deferredSkip(
        lambda: not all(
            getattr(connection.features, feature, False) for feature in features
        ),
        "Database doesn't support feature(s): %s" % ", ".join(features),
        "skipUnlessDBFeature",
    )


def skipUnlessAnyDBFeature(*features):
    """Skip a test unless a database has any of the named features."""
    return _deferredSkip(
        lambda: not any(
            getattr(connection.features, feature, False) for feature in features
        ),
        "Database doesn't support any of the feature(s): %s" % ", ".join(features),
        "skipUnlessAnyDBFeature",
    )


class QuietWSGIRequestHandler(WSGIRequestHandler):
    """
    A WSGIRequestHandler that doesn't log to standard output any of the
    requests received, so as to not clutter the test result output.
    """

    def log_message(*args):
        pass


class FSFilesHandler(WSGIHandler):
    """
    WSGI middleware that intercepts calls to a directory, as defined by one of
    the *_ROOT settings, and serves those files, publishing them under *_URL.
    """

    def __init__(self, application):
        self.application = application
        self.base_url = urlparse(self.get_base_url())
        super().__init__()

    def _should_handle(self, path):
        """
        Check if the path should be handled. Ignore the path if:
        * the host is provided as part of the base_url
        * the request's path isn't under the media path (or equal)
        """
        return path.startswith(self.base_url[2]) and not self.base_url[1]

    def file_path(self, url):
        """Return the relative path to the file on disk for the given URL."""
        relative_url = url[len(self.base_url[2]) :]
        return url2pathname(relative_url)

    def get_response(self, request):
        from django.http import Http404

        if self._should_handle(request.path):
            try:
                return self.serve(request)
            except Http404:
                pass
        return super().get_response(request)

    def serve(self, request):
        os_rel_path = self.file_path(request.path)
        os_rel_path = posixpath.normpath(unquote(os_rel_path))
        # Emulate behavior of django.contrib.staticfiles.views.serve() when it
        # invokes staticfiles' finders functionality.
        # TODO: Modify if/when that internal API is refactored
        final_rel_path = os_rel_path.replace("\\", "/").lstrip("/")
        return serve(request, final_rel_path, document_root=self.get_base_dir())

    def __call__(self, environ, start_response):
        if not self._should_handle(get_path_info(environ)):
            return self.application(environ, start_response)
        return super().__call__(environ, start_response)


class _StaticFilesHandler(FSFilesHandler):
    """
    Handler for serving static files. A private class that is meant to be used
    solely as a convenience by LiveServerThread.
    """

    def get_base_dir(self):
        return settings.STATIC_ROOT

    def get_base_url(self):
        return settings.STATIC_URL


class _MediaFilesHandler(FSFilesHandler):
    """
    Handler for serving the media files. A private class that is meant to be
    used solely as a convenience by LiveServerThread.
    """

    def get_base_dir(self):
        return settings.MEDIA_ROOT

    def get_base_url(self):
        return settings.MEDIA_URL


class LiveServerThread(threading.Thread):
    """Thread for running a live HTTP server while the tests are running."""

    server_class = ThreadedWSGIServer

    def __init__(self, host, static_handler, connections_override=None, port=0):
        self.host = host
        self.port = port
        self.is_ready = threading.Event()
        self.error = None
        self.static_handler = static_handler
        self.connections_override = connections_override
        super().__init__()

    def run(self):
        """
        Set up the live server and databases, and then loop over handling
        HTTP requests.
        """
        if self.connections_override:
            # Override this thread's database connections with the ones
            # provided by the main thread.
            for alias, conn in self.connections_override.items():
                connections[alias] = conn
        try:
            # Create the handler for serving static and media files
            handler = self.static_handler(_MediaFilesHandler(WSGIHandler()))
            self.httpd = self._create_server(
                connections_override=self.connections_override,
            )
            # If binding to port zero, assign the port allocated by the OS.
            if self.port == 0:
                self.port = self.httpd.server_address[1]
            self.httpd.set_app(handler)
            self.is_ready.set()
            self.httpd.serve_forever()
        except Exception as e:
            self.error = e
            self.is_ready.set()
        finally:
            connections.close_all()

    def _create_server(self, connections_override=None):
        return self.server_class(
            (self.host, self.port),
            QuietWSGIRequestHandler,
            allow_reuse_address=False,
            connections_override=connections_override,
        )

    def terminate(self):
        if hasattr(self, "httpd"):
            # Stop the WSGI server
            self.httpd.shutdown()
            self.httpd.server_close()
        self.join()


class LiveServerTestCase(TransactionTestCase):
    """
    Do basically the same as TransactionTestCase but also launch a live HTTP
    server in a separate thread so that the tests may use another testing
    framework, such as Selenium for example, instead of the built-in dummy
    client.
    It inherits from TransactionTestCase instead of TestCase because the
    threads don't share the same transactions (unless if using in-memory sqlite)
    and each thread needs to commit all their transactions so that the other
    thread can see the changes.
    """

    host = "localhost"
    port = 0
    server_thread_class = LiveServerThread
    static_handler = _StaticFilesHandler

    @classproperty
    def live_server_url(cls):
        return "http://%s:%s" % (cls.host, cls.server_thread.port)

    @classproperty
    def allowed_host(cls):
        return cls.host

    @classmethod
    def _make_connections_override(cls):
        connections_override = {}
        for conn in connections.all():
            # If using in-memory sqlite databases, pass the connections to
            # the server thread.
            if conn.vendor == "sqlite" and conn.is_in_memory_db():
                connections_override[conn.alias] = conn
        return connections_override

    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        cls._live_server_modified_settings = modify_settings(
            ALLOWED_HOSTS={"append": cls.allowed_host},
        )
        cls._live_server_modified_settings.enable()
        cls.addClassCleanup(cls._live_server_modified_settings.disable)
        cls._start_server_thread()

    @classmethod
    def _start_server_thread(cls):
        connections_override = cls._make_connections_override()
        for conn in connections_override.values():
            # Explicitly enable thread-shareability for this connection.
            conn.inc_thread_sharing()

        cls.server_thread = cls._create_server_thread(connections_override)
        cls.server_thread.daemon = True
        cls.server_thread.start()
        cls.addClassCleanup(cls._terminate_thread)

        # Wait for the live server to be ready
        cls.server_thread.is_ready.wait()
        if cls.server_thread.error:
            raise cls.server_thread.error

    @classmethod
    def _create_server_thread(cls, connections_override):
        return cls.server_thread_class(
            cls.host,
            cls.static_handler,
            connections_override=connections_override,
            port=cls.port,
        )

    @classmethod
    def _terminate_thread(cls):
        # Terminate the live server's thread.
        cls.server_thread.terminate()
        # Restore shared connections' non-shareability.
        for conn in cls.server_thread.connections_override.values():
            conn.dec_thread_sharing()


class SerializeMixin:
    """
    Enforce serialization of TestCases that share a common resource.

    Define a common 'lockfile' for each set of TestCases to serialize. This
    file must exist on the filesystem.

    Place it early in the MRO in order to isolate setUpClass()/tearDownClass().
    """

    lockfile = None

    def __init_subclass__(cls, /, **kwargs):
        super().__init_subclass__(**kwargs)
        if cls.lockfile is None:
            raise ValueError(
                "{}.lockfile isn't set. Set it to a unique value "
                "in the base class.".format(cls.__name__)
            )

    @classmethod
    def setUpClass(cls):
        cls._lockfile = open(cls.lockfile)
        cls.addClassCleanup(cls._lockfile.close)
        locks.lock(cls._lockfile, locks.LOCK_EX)
        super().setUpClass()
