"""Event loop using a proactor and related classes.

A proactor is a "notify-on-completion" multiplexer.  Currently a
proactor is only implemented on Windows with IOCP.
"""

import sys
from collections.abc import Mapping
from socket import socket
from typing import Any, ClassVar, Literal

from . import base_events, constants, events, futures, streams, transports

__all__ = ("BaseProactorEventLoop",)

class _ProactorBasePipeTransport(transports._FlowControlMixin, transports.BaseTransport):
    """Base class for pipe and socket transports."""

    def __init__(
        self,
        loop: events.AbstractEventLoop,
        sock: socket,
        protocol: streams.StreamReaderProtocol,
        waiter: futures.Future[Any] | None = None,
        extra: Mapping[Any, Any] | None = None,
        server: events.AbstractServer | None = None,
    ) -> None: ...
    def __del__(self) -> None: ...

class _ProactorReadPipeTransport(_ProactorBasePipeTransport, transports.ReadTransport):
    """Transport for read pipes."""

    if sys.version_info >= (3, 10):
        def __init__(
            self,
            loop: events.AbstractEventLoop,
            sock: socket,
            protocol: streams.StreamReaderProtocol,
            waiter: futures.Future[Any] | None = None,
            extra: Mapping[Any, Any] | None = None,
            server: events.AbstractServer | None = None,
            buffer_size: int = 65536,
        ) -> None: ...
    else:
        def __init__(
            self,
            loop: events.AbstractEventLoop,
            sock: socket,
            protocol: streams.StreamReaderProtocol,
            waiter: futures.Future[Any] | None = None,
            extra: Mapping[Any, Any] | None = None,
            server: events.AbstractServer | None = None,
        ) -> None: ...

class _ProactorBaseWritePipeTransport(_ProactorBasePipeTransport, transports.WriteTransport):
    """Transport for write pipes."""

class _ProactorWritePipeTransport(_ProactorBaseWritePipeTransport): ...

class _ProactorDuplexPipeTransport(_ProactorReadPipeTransport, _ProactorBaseWritePipeTransport, transports.Transport):
    """Transport for duplex pipes."""

class _ProactorSocketTransport(_ProactorReadPipeTransport, _ProactorBaseWritePipeTransport, transports.Transport):
    """Transport for connected sockets."""

    _sendfile_compatible: ClassVar[constants._SendfileMode]
    def __init__(
        self,
        loop: events.AbstractEventLoop,
        sock: socket,
        protocol: streams.StreamReaderProtocol,
        waiter: futures.Future[Any] | None = None,
        extra: Mapping[Any, Any] | None = None,
        server: events.AbstractServer | None = None,
    ) -> None: ...
    def _set_extra(self, sock: socket) -> None: ...
    def can_write_eof(self) -> Literal[True]: ...

class BaseProactorEventLoop(base_events.BaseEventLoop):
    def __init__(self, proactor: Any) -> None: ...
    async def sock_recv(self, sock: socket, n: int) -> bytes: ...
