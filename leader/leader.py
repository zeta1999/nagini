import socket
import sys

from typing import NamedTuple, Optional, Tuple
from nagini_contracts.contracts import *
from nagini_contracts.io_contracts import *
from nagini_contracts.obligations import MustTerminate
from nagini_contracts.adt import ADT
from int_socket import send_int, receive_int, UDP_receive_int, UDP_send_int, MAX_INT


class LocalState(ADT):
    pass

class State(LocalState, NamedTuple('State', [('winner', bool),
                                             ('ibuf', PSet[int]),
                                             ('obuf', PSet[int])])):
    pass

@IOOperation
def set_up_init_io(
        t_pre: Place,
        t_post: Place = Result()) -> bool:
    Terminates(True)

@ContractOnly
def set_up_init(t_pre: Place, ) -> Place:
    IOExists1(Place)(lambda t_post: (
        Requires(MustTerminate(1)),
        Requires(token(t_pre, 1) and set_up_init_io(t_pre, t_post)),
        Ensures(Result() is t_post and token(t_post))
    ))

@IOOperation
def accept_io(
        t_pre: Place,
        msg: int,
        t_post: Place = Result()) -> bool:
    Terminates(True)

@ContractOnly
def accept(t_pre: Place, msg: int) -> Place:
    IOExists1(Place)(lambda t_post: (
        Requires(MustTerminate(1)),
        Requires(token(t_pre, 1) and accept_io(t_pre, msg, t_post)),
        Ensures(Result() is t_post and token(t_post))
    ))

@IOOperation
def reject_io(
        t_pre: Place,
        t_post: Place = Result()) -> bool:
    Terminates(True)

@ContractOnly
def reject(t_pre: Place) -> Place:
    IOExists1(Place)(lambda t_post: (
        Requires(MustTerminate(1)),
        Requires(token(t_pre, 1) and reject_io(t_pre, t_post)),
        Ensures(Result() is t_post and token(t_post))
    ))

@IOOperation
def elect_io(
        t_pre: Place,
        t_post: Place = Result()) -> bool:
    Terminates(True)

@ContractOnly
def elect(t_pre: Place) -> Place:
    IOExists1(Place)(lambda t_post: (
        Requires(MustTerminate(1)),
        Requires(token(t_pre, 1) and elect_io(t_pre, t_post)),
        Ensures(Result() is t_post and token(t_post))
    ))

@IOOperation
def P(t: Place, id: int, port: int, next_host: str, next_port: int,
      s: State) -> bool:
    Terminates(False)
    return IOExists6(Place, Place, Place, int, Place, Place)(
        lambda t1, t2, t4, rres, t5, t6: (
            # Event set_up_init
            set_up_init_io(t, t1) and
            P(t1, id, port, next_host, next_port, State(s.winner, s.ibuf, s.obuf + PSet(id)))
            and
            # Event accept
            IOForall(int, lambda msg: (
                Implies(
                    msg in s.ibuf and id < msg,
                    accept_io(t, msg, t2) and
                    P(t2, id, port, next_host, next_port, State(s.winner, s.ibuf, s.obuf + PSet(msg)))
                )
            ))
            and
            # # Event reject
            # Implies(
            #     len(s.ibuf) > 0 and id > s.ibuf[0],
            #     reject_io(t, t3) and
            #     P(t3, id, port, next_host, next_port, State(s.set_up, s.winner, s.ibuf.drop(1), s.obuf))
            # )
            # and
            # Event elect
            Implies(
                id in s.ibuf,
                elect_io(t, t4) and
                P(t4, id, port, next_host, next_port, State(True, s.ibuf, s.obuf))
            )
            and
            # Event receive
            UDP_receive_int(t, port, rres, t5) and
            P(t5, id, port, next_host, next_port, State(s.winner, s.ibuf + PSet(rres), s.obuf))
            # TODO: receive event should always receive something
            and
            # Event send
            IOForall(int, lambda msg:(
                Implies(
                    msg in s.obuf,
                    UDP_send_int(t, next_host, next_port, msg, t6) and
                    P(t6, id, port, next_host, next_port,
                      State(s.winner, s.ibuf, s.obuf))
                )
            ))
        )
    )

EMPTY = PSet()  # type: PSet[int]

INIT_STATE = State(False, EMPTY, EMPTY)







def main(t: Place, in_host: str, in_port: int, out_host: str, out_port: int, my_id: int) -> Place:
    Requires(my_id >= 0 and my_id < MAX_INT)
    Requires(token(t) and P(t, my_id, in_port, out_host, out_port, INIT_STATE))
    Ensures(token(Result(), 5))
    s = INIT_STATE
    Open(P(t, my_id, in_port, out_host, out_port, INIT_STATE))
    rec_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    rec_socket.settimeout(0.5)
    send_socket = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

    rec_socket.bind((in_host, in_port))
    send_socket.connect((out_host, out_port))

    to_send = my_id

    t = set_up_init(t)

    s = State(s.winner, s.ibuf, s.obuf + PSet(my_id))
    Open(P(t, my_id, in_port, out_host, out_port, s))
    t, succ = try_send_int(t, send_socket, to_send)
    while True:
        Invariant(token(t, 5) and P(t, my_id, in_port, out_host, out_port, s))
        Invariant(to_send >= 0 and to_send < MAX_INT)
        Invariant(Acc(rec_socket.timeout(), 1 / 2) and Acc(rec_socket.sock(), 1 / 2))
        Invariant(Acc(rec_socket.family, 1/2) and Acc(rec_socket.type, 1/2))
        Invariant(Acc(send_socket.timeout(), 1 / 2) and Acc(send_socket.peer(), 1 / 2))
        Invariant(Acc(send_socket.family, 1 / 2) and Acc(send_socket.type, 1 / 2))
        Invariant(rec_socket.family is socket.AF_INET and rec_socket.type is socket.SOCK_DGRAM)
        Invariant(send_socket.family is socket.AF_INET and send_socket.type is socket.SOCK_DGRAM)
        Invariant(not rec_socket.getblocking() and rec_socket.getsockname()[1] is in_port)
        Invariant(send_socket.getpeername()[0] is out_host and send_socket.getpeername()[1] is out_port)
        Invariant(to_send in s.obuf and to_send >= my_id)

        Open(P(t, my_id, in_port, out_host, out_port, s))
        t, msg = try_receive_int(t, rec_socket)
        if msg is not None:
            s = State(s.winner, s.ibuf + PSet(msg), s.obuf)
            Open(P(t, my_id, in_port, out_host, out_port, s))
        if msg is not None:
            if msg == my_id:
                # YAY, I AM THE LEADER, WHAT SHOULD I DO HERE?
                t = elect(t)
                break
            elif msg > to_send:
                t = accept(t, msg)
                to_send = msg
                s = State(s.winner, s.ibuf, s.obuf + PSet(msg))
                Open(P(t, my_id, in_port, out_host, out_port, s))
        t, success = try_send_int(t, send_socket, to_send)
        if success:
            Open(P(t, my_id, in_port, out_host, out_port, s))
        else:
            Assume(False)
    return t


def try_receive_int(t: Place, rec_socket: socket.socket) -> Tuple[Place, Optional[int]]:
    IOExists2(int, Place)(lambda res, t_post: (
        Requires(Acc(rec_socket.timeout(), 1 / 2)),
        Requires(Acc(rec_socket.type, 1 / 4) and Acc(rec_socket.family, 1 / 4)),
        Requires(Acc(rec_socket.sock(), 1 / 4)),
        Requires(Implies(not rec_socket.getblocking(), MustTerminate(3))),
        Requires(token(t, 3)),
        Requires(rec_socket.family is socket.AF_INET),
        Requires(rec_socket.type is socket.SOCK_DGRAM),
        Requires(not rec_socket.getblocking()),
        Requires(
            UDP_receive_int(t, rec_socket.getsockname()[1], res, t_post)),
        Ensures(Acc(rec_socket.timeout(), 1 / 2)),
        Ensures(Acc(rec_socket.type, 1 / 4) and Acc(rec_socket.family, 1 / 4)),
        Ensures(Acc(rec_socket.sock(), 1 / 4)),
        Ensures((Result()[0] is t_post and Result()[1] is res and token(t_post)) if Result()[1] is not None else token(t, 2)),
        Ensures(Implies(Result()[1] is not None, res >= 0 and res < MAX_INT))
    ))
    try:
        p, r = receive_int(t, rec_socket)
        res = (p, r)  # type: Tuple[Place, Optional[int]]
        return res
    except socket.timeout as e:
        rese = t, None  # type: Tuple[Place, Optional[int]]
        return rese



def try_send_int(t: Place, send_socket: socket.socket, to_send: int) -> Tuple[Place, bool]:
    IOExists1(Place)(lambda t_post: (
        Requires(to_send >= 0 and to_send < MAX_INT),
        Requires(MustTerminate(3)),
        Requires(token(t, 3)),
        Requires(Acc(send_socket.type, 1 / 4) and Acc(send_socket.family, 1 / 4)),
        Requires(Acc(send_socket.peer(), 1 / 4)),
        Requires(send_socket.family is socket.AF_INET),
        Requires(send_socket.type is socket.SOCK_DGRAM),
        Requires(
            UDP_send_int(t, send_socket.getpeername()[0], send_socket.getpeername()[1],
                         to_send, t_post)),
        Ensures(Result()[0] is t_post and token(t_post) if Result()[1] else token(t, 2)),
        Ensures(Acc(send_socket.type, 1 / 4) and Acc(send_socket.family, 1 / 4)),
        Ensures(Acc(send_socket.peer(), 1 / 4)),
    ))
    try:
        t_res = send_int(t, send_socket, to_send)
        return t_res, True
    except ConnectionRefusedError as e:
        return t, False  # TODO: give send perm back


# TODO: back in with global IO spec based on args.
# IN_HOST = sys.argv[1]
# IN_PORT = int(sys.argv[2])
#
# OUT_HOST = sys.argv[3]
# OUT_PORT = int(sys.argv[4])
#
# MY_ID = int(sys.argv[5])
#
# if __name__ == '__main__':
#     main(IN_HOST, IN_PORT, OUT_HOST, OUT_PORT, MY_ID)