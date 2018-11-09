# lark grammar
from lark import Lark
from plugins.basic.preprocessor import preprocess

grammar = """

program: directive*

directive:
    | import
    | typedef
    | function
    | automaton
    | system

import:
    | "import" term [ "as" identifier ] ";"     -> alias_import
    | "from" term "import" term ";"             -> partial_import

typedef: "typedef" type "as" identifier ";"

function: \
    "function" identifier "(" (param ("," param)*)? ")" (":" type)? function_body

function_body:
    | ";"                           -> empty

automaton:
    | "automaton" identifier "(" (param ("," param)*)? ")" "{" "}"

system:
    | "system"

param: identifiers ":" type

type:
    --- precedence type
    | type "," type                 -> pair
    ---
    | "int"                         -> int_type
    | "char"                        -> char_type
    | "double"                      -> double_type
    | "bool"                        -> bool_type
    --- precedence end

term:
    --- precedence term
    | term "," term                 -> pair
    ---
    | term "+" term                 -> add
    | term "-" term                 -> minus
    ---
    | term "*" term                 -> times
    | term "/" term                 -> div
    ---
    | "!" term                      -> not
    | "-" term                      -> negative
    | "(" term ")"                  -> atomic       <precedence reset>
    | "[" term "]"                  -> list
    | value                         -> value
    --- precedence end

value:
    | CNAME                         -> identifier
    | NUMBER                        -> number
    | ESCAPED_STRING                -> string

identifier:
    | CNAME

identifiers: identifier ("," identifier)*

%import common.NUMBER
%import common.ESCAPED_STRING
%import common.WS
%import common.CNAME
%ignore WS
"""

grammar = preprocess(grammar)

test_term = """
1 + -2 * (3.2 + "a") / !b, 2, 3
"""

test_type = """
int, int, char
"""

test_program = """
import sync;

typedef int as _int;

function x (a:int, b:char) : int;

function y ();
"""

parser = Lark(grammar, start='program')
print(parser.parse(test_program).pretty())
