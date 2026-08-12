#!/usr/bin/env python3
"""Preserve primary and cleanup failures across supported Python runtimes."""
from __future__ import annotations

import builtins
import contextlib
import os
from collections.abc import Iterator


class _CompatibleCleanupFailureGroup(BaseException):
    """Python 3.10 fallback carrying every independent failure."""

    def __init__(self, message: str, exceptions: list[BaseException]) -> None:
        super().__init__(message)
        self.exceptions = tuple(exceptions)


CleanupFailureGroup = getattr(
    builtins, "BaseExceptionGroup", _CompatibleCleanupFailureGroup,
)


def raise_failures(
    message: str,
    primary: BaseException | None,
    cleanup_failures: list[BaseException],
) -> None:
    """Raise one failure directly or preserve all failures in a group."""
    failures = ([primary] if primary is not None else []) + cleanup_failures
    if not failures:
        return
    if len(failures) == 1:
        failure = failures[0]
        raise failure.with_traceback(failure.__traceback__)
    raise CleanupFailureGroup(message, failures) from None


@contextlib.contextmanager
def closing_fd(descriptor: int, message: str) -> Iterator[int]:
    """Close an FD while preserving both an active operation and close failure."""
    primary: BaseException | None = None
    try:
        yield descriptor
    except BaseException as error:
        primary = error
    close_failures: list[BaseException] = []
    try:
        os.close(descriptor)
    except BaseException as close_error:
        close_failures.append(close_error)
    raise_failures(message, primary, close_failures)
