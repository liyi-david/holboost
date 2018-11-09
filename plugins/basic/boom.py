from kernel.dsl import DSL, DSLParsingFailure
from lark import Lark

from .preprocessor import preprocess, PTransformer as Transformer
from .logic import land, lor, lnot

boom_grammar = """

constr:
    --- precedence constr
    | constr "/\\\\" constr     -> land
    | constr "\\/" constr       -> lor
    ---
    | "~" constr                -> lnot
    | CNAME                     -> ident
    --- precedence end

%import common.NUMBER
%import common.ESCAPED_STRING
%import common.WS
%import common.CNAME
%ignore WS

"""

class BoomTransformer(Transformer):

    def __init__(self, env):
        self.env = env

    def ident(self, matches):
        name ,= matches
        try:
            return self.env[name].term()
        except:
            raise DSLParsingFailure("%s is not a valid identifier." % name)

    def land(self, matches):
        return land(matches[0], matches[1])

    def lor(self, matches):
        return lor(matches[0], matches[1])

    def lnot(self, matches):
        t ,= matches
        return lnot(t)


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
