from nagini_contracts.contracts import *


class Super:
    def some_function(self, a: int) -> int:
        return a


class Sub(Super):
    #:: ExpectedOutput(invalid.program:invalid.override)
    def some_function(self, c: int) -> int:
        return c