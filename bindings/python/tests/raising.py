"""How a suite expects an exception: by its class and its whole message."""

import re
from typing import TypeVar

import pytest

# The mark of a number in a message template.
NUMBER = "{n}"

# A type variable, since the test of each wheel runs the suites on Python 3.10 too.
E = TypeVar("E", bound=BaseException)


def raises(exception: type[E], message: str) -> pytest.RaisesExc[E]:
    """Expect an exception of the class, or of a subclass, whose message is exactly the text."""
    return pytest.raises(exception, match=rf"\A{re.escape(message)}\Z")


def shape_pattern(template: str) -> str:
    """The anchored pattern of a template: its text exactly, with a decimal number at each mark."""
    text = template.replace(NUMBER, "")
    if any(bad in text for bad in ("{", "}", "|", ".*", "\\")):
        raise ValueError(f"a template marks only numbers, as {NUMBER}: {template!r}")
    # An ASCII class, since \d also matches the digits of other scripts.
    pattern = "[0-9]+".join(re.escape(part) for part in template.split(NUMBER))
    return rf"\A{pattern}\Z"


def raises_shape(exception: type[E], template: str) -> pytest.RaisesExc[E]:
    """Expect a message equal to the template, with any number at each {n} of the template."""
    return pytest.raises(exception, match=shape_pattern(template))
