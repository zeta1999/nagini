from py2viper_contracts.contracts import Result
from py2viper_contracts.io import *
from typing import Tuple


@IOOperation
def read_int_io(
        t_pre: Place,
        result: int = Result(),
        t_post: Place = Result(),
        ) -> bool:
    Terminates(True)


def test(t1: Place) -> None:

    #:: ExpectedOutput(invalid.program:invalid.get_ghost_output.target_not_variable)
    t2, t3 = GetGhostOutput(read_int_io(t1), 't_post')  # type: Tuple[Place, Place]
