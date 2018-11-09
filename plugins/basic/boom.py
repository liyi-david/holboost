from kernel.dsl import DSL, DSLParsingFailure
from kernel.macro import Macro
from lark import Lark

from .preprocessor import preprocess, PTransformer as Transformer
from .logic import land, lor, lnot, imply

from plugins.theories import nat, integer

boom_grammar = """

constr:
    --- precedence constr
    | constr "->" constr        -> imply
    ---
    | constr "/\\\\" constr     -> land
    | constr "\\/" constr       -> lor
    ---
    | constr ">=" constr        -> ge
    | constr ">"  constr        -> gt
    | constr "<=" constr        -> le
    | constr "<"  constr        -> lt
    | constr "="  constr        -> eq
    ---
    | "~" constr                -> lnot
    | CNAME                     -> ident
    | NAT                       -> nat
    | INT                       -> int
    | "(" constr ")"            -> atomic
    --- precedence end

NAT: /[0-9]+/

INT.2: /-?[0-9]+Z/ | /-[0-9]+/

%import common.NUMBER
%import common.ESCAPED_STRING
%import common.WS
%import common.CNAME
%ignore WS

"""
def unaryopr(f):

    def checked_f(s, matches):
        assert len(matches) == 1, "invalid number of operands: %d, 1 excepted" % len(matches)
        t ,= matches
        return f(s, t)

    return checked_f

def binaryopr(f):

    # signature of f is: Transformer -> T -> T -> T
    def checked_f(s, matches):
        assert len(matches) == 2, "invalid number of operands: %d, 2 excepted" % len(matches)
        l, r = matches
        return f(s, l, r)

    return checked_f

def macroopr(f):

    def checked_f(s, matches):
        if len(matches) != 0:
            assert all(map(lambda m: type(m) is type(matches[0]), matches)) and isinstance(matches[0], Macro), \
                    "types of all operands must be the same Macro"

        return f(s, matches)

    return checked_f


class BoomTransformer(Transformer):

    def __init__(self, env):
        self.env = env

    # ============================= primitive values ==========================

    @unaryopr
    def nat(self, val):
        return nat(int(val))

    @unaryopr
    def int(self, val):
        val = str(val).replace('Z', '')
        return integer(int(val))

    @unaryopr
    def ident(self, name):
        try:
            return self.env[name].term()
        except:
            raise DSLParsingFailure("%s is not a valid identifier." % name)

    # ================================= operators =============================

    @binaryopr
    def land(self, l, r):
        return land(l, r)

    @binaryopr
    def lor(self, l, r):
        return lor(l, r)

    def lnot(self, t):
        t ,= t
        return lnot(t)

    @macroopr
    @binaryopr
    def ge(self, l, r):
        return l.type()._ge(l, r)

    @macroopr
    @binaryopr
    def gt(self, l, r):
        return l.type()._gt(l, r)

    @macroopr
    @binaryopr
    def le(self, l, r):
        return l.type()._le(l, r)

    @macroopr
    @binaryopr
    def lt(self, l, r):
        return l.type()._lt(l, r)

    @macroopr
    @binaryopr
    def eq(self, l, r):
        return l.type()._eq(l, r)

    @binaryopr
    def imply(self, l, r):
        return imply(l, r)


class BoomLanguage(DSL):

    parser = None
    grammar = None

    @classmethod
    def name(cls):
        # the default dsl
        return ""

    @classmethod
    def parse(cls, content, env):
        if cls.parser is None:
            cls.grammar = preprocess(boom_grammar)
            cls.parser = Lark(cls.grammar, start="constr")

        ptree = cls.parser.parse(content)
        return BoomTransformer(env).transform(ptree)
