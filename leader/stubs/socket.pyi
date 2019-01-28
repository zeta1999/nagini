from typing import Optional, Tuple
from nagini_contracts.contracts import *

AF_INET = 2
SOCK_DGRAM = 2


class timeout(Exception):
    pass


class socket():

    def __init__(self, family: int = -1, type: int = -1, proto: int = -1, fileno : object =None) -> None:
        self.family = family
        self.type = type
        Ensures(Acc(self.timeout()))
        Ensures(Acc(self.type, 1/2) and self.type is type)
        Ensures(Acc(self.family, 1/2) and self.family is family)
        Ensures(self.sock() and self.peer())

    def settimeout(self, timeout: Optional[float]) -> None:
        Requires(Acc(self.timeout()))
        Ensures(Acc(self.timeout()))
        Ensures(self.gettimeout() is timeout)

    @Predicate
    def timeout(self) -> bool:
        return True

    @Pure
    @ContractOnly
    def gettimeout(self) -> Optional[float]:
        Requires(Acc(self.timeout()))

    def setblocking(self, flag: bool) -> None:
        Requires(Acc(self.timeout()))
        Ensures(Acc(self.timeout()))
        Ensures(self.gettimeout() is (None if flag else 0.0))

    @Pure
    @ContractOnly
    def getblocking(self) -> bool:
        Requires(Acc(self.timeout()))
        Ensures(Result() is (self.gettimeout() is None))

    @Predicate
    def sock(self) -> bool:
        return True

    @Pure
    @ContractOnly
    def getsockname(self) -> Tuple[str, int]:
        Requires(Acc(self.sock(), 1/8))

    def bind(self, address: Tuple[str, int]) -> None:
        Requires(self.sock())
        Ensures(Acc(self.sock(), 1/2))
        Ensures(self.getsockname() is address)

    @Predicate
    def peer(self) -> bool:
        return True

    def connect(self, address: Tuple[str, int]) -> None:
        Requires(self.peer())
        Ensures(Acc(self.peer(), 1/2))
        Ensures(self.getpeername() is address)

    @Pure
    @ContractOnly
    def getpeername(self) -> Tuple[str, int]:
        Requires(Acc(self.peer(), 1/8))

    def recv(self, buffersize: int, flags : object = None) -> bytes:
        pass

    def send(self, data : bytes, flags: object =None) -> int:
        pass