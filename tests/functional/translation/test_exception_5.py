# Any copyright is dedicated to the Public Domain.
# http://creativecommons.org/publicdomain/zero/1.0/

def test() -> None:
    try:
        raise Exception()
    finally:
        raise Exception()
        #:: ExpectedOutput(type.error:dead.code)
        a = 2
