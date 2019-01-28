import socket
from typing import Optional, Tuple
from nagini_contracts.contracts import *
from nagini_contracts.io_contracts import *
from nagini_contracts.obligations import MustTerminate


MAX_INT = 4294967295


@IOOperation
def UDP_send_int(
        t_pre: Place,
        addr: str,
        port: int,
        value: int,
        t_post: Place = Result()) -> bool:
    Terminates(True)

@IOOperation
def UDP_receive_int_nonblocking(
        t_pre: Place,
        port: int,
        res: Optional[int] = Result(),
        t_post: Place = Result()) -> bool:
    Terminates(True)

@IOOperation
def UDP_receive_int_blocking(
        t_pre: Place,
        port: int,
        res: int = Result(),
        t_post: Place = Result()) -> bool:
    Terminates(False)


@ContractOnly
def send_int(t1: Place, send_socket: socket.socket, to_send: int) -> Place:
    IOExists1(Place)(lambda t_post: (
        Requires(to_send >= 0 and to_send < MAX_INT),
        Requires(MustTerminate(1)),
        Requires(token(t1)),
        Requires(Acc(send_socket.type, 1 / 4) and Acc(send_socket.family, 1 / 4)),
        Requires(Acc(send_socket.peer(), 1/4)),
        Requires(send_socket.family is socket.AF_INET),
        Requires(send_socket.type is socket.SOCK_DGRAM),
        Requires(UDP_send_int(t1, send_socket.getpeername()[0], send_socket.getpeername()[1], to_send, t_post)),
        Ensures(Result() is t_post),
        Ensures(Acc(send_socket.type, 1 / 4) and Acc(send_socket.family, 1 / 4)),
        Ensures(Acc(send_socket.peer(), 1 / 4)),
    ))
    # send_socket.send(to_send.to_bytes(4, "big"))


@ContractOnly
def receive_int(t1: Place, rec_socket: socket.socket) -> Tuple[Place, int]:
    IOExists2(Optional[int], Place)(lambda res, t_post: (
        Requires(Acc(rec_socket.timeout(), 1/2)),
        Requires(Acc(rec_socket.type, 1 / 4) and Acc(rec_socket.family, 1 / 4)),
        Requires(Acc(rec_socket.sock(), 1 / 4)),
        Requires(Implies(not rec_socket.getblocking(), MustTerminate(1))),
        Requires(token(t1)),
        Requires(rec_socket.family is socket.AF_INET),
        Requires(rec_socket.type is socket.SOCK_DGRAM),
        Requires(not rec_socket.getblocking()),
        Requires(UDP_receive_int_nonblocking(t1, rec_socket.getsockname()[1], res, t_post)),
        Ensures(Acc(rec_socket.timeout(), 1 / 2)),
        Ensures(Acc(rec_socket.type, 1 / 4) and Acc(rec_socket.family, 1 / 4)),
        Ensures(Acc(rec_socket.sock(), 1 / 4)),
        Ensures(Result()[0] is t_post and Result()[1] is res and Result()[1] >= 0 and Result()[1] < MAX_INT and token(t_post)),
        Exsures(socket.timeout, Acc(rec_socket.timeout(), 1 / 2)),
        Exsures(socket.timeout, Acc(rec_socket.type, 1 / 4) and Acc(rec_socket.family, 1 / 4)),
        Exsures(socket.timeout, Acc(rec_socket.sock(), 1 / 4)),
        Exsures(socket.timeout, Result()[0] is t_post and res is None and token(t_post)),
    ))
    # msg = rec_socket.recv(4)
    # received_id = int.from_bytes(msg, "big")  # lets say this requires not none or whatever and doesnt fail
    # return received_id