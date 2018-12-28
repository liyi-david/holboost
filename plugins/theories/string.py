from kernel.macro import Macro
from kernel.term import Construct, Ind, Apply

from .bool import true, false

_coq_string_type  = Ind('Coq.Strings.String.string', 0)
_coq_string_cons  = Construct('Coq.Strings.String.string', 0, 1)
_coq_string_empty = Construct('Coq.Strings.String.string', 0, 0)
_coq_ascii        = Construct('Coq.Strings.Ascii.ascii', 0, 0)


def to_ascii(c):
    bits, c = [], ord(c)
    for i in range(8):
        bits.append(false if c % 2 == 0 else true)
        c >>= 1

    assert c == 0, "cannot unfold non-ascii strings"

    return Apply(
            _coq_ascii, *bits
            )


def from_ascii(a):
    if isinstance(a, Apply) and a.func == _coq_ascii:
        code = 0
        for b in reversed(a.args):
            code <<= 1
            if b == true:
                code += 1
            elif b != false:
                raise Macro.MacroFoldFailure

        return chr(code)

    raise Macro.MacroFoldFailure


class StringType(Macro):

    __instance = None

    def __new__(cls):
        if cls.__instance is None:
            cls.__instance = super(StringType, cls).__new__(cls)

        return cls.__instance

    def unfold(self):
        return _coq_string_type

    def render(self, environment=None, debug=False):
        return "string"

    def __call__(self, val):
        return StringValue(val)



class StringValue(Macro):

    def __init__(self, val):
        self.val = val

    def unfold(self):
        coqs = _coq_string_empty
        for c in reversed(self.val):
            coqs = Apply(
                    _coq_string_cons,
                    to_ascii(c),
                    coqs
                    )

        return coqs

    @classmethod
    def fold(cls, t):
        s = ""
        while isinstance(t, Apply) and t.func == _coq_string_cons:
            s += from_ascii(t.args[0])
            t = t.args[1]

        if t == _coq_string_empty:
            return string(s)
        else:
            raise Macro.MacroFoldFailure


    def type(self, environment=None, debug=False):
        return string

    def render(self, environment=None, debug=False):
        return "\"%s\"" % self.val

StringValue.register()
string = StringType()
