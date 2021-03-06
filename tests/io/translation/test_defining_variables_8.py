# Any copyright is dedicated to the Public Domain.
# http://creativecommons.org/publicdomain/zero/1.0/

from nagini_contracts.contracts import Result
from nagini_contracts.io_contracts import *


@IOOperation
def test_io(
        t_pre: Place,
        result: int = Result(),
        ) -> bool:
    Terminates(True)


@IOOperation
def test_io2(
        t_pre: Place,
        value: int,
        ) -> bool:
    Terminates(True)
    #:: ExpectedOutput(invalid.program:invalid.io_operation.body.variable_not_existential)
    return test_io(t_pre, value)
