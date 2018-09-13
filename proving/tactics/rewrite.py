from kernel.term import *
from proving.tactics.equality import Equality

# this line is required, otherwise this will not be loaded automatically
autoload = True

def is_equality_relation(term):
    # according to coq's implementation, there are two types of equality, they are
    # setoid equality and leibniz equality
    if isinstance(term, Ind):
        # for leibniz equality
        # FIXME
        return term.mutind_name == "Coq.Init.Logic.eq"

    return False

def obtain_equality(term):
    if isinstance(term, Apply) and is_equality_relation(term.func):
        return [], term
    elif isinstance(term, Prod):
        result = obtain_equality(term.body)
        if result is None:
            return None
        else:
            # result = (prods, term)
            return ([(term.arg_name, term.arg_type)] + result[0], result[1])
    else:
        return None

def generate_task_equality(task: 'Task'):
    equalities = {}
    for name, const in [ *task.constants.items(), *task.context_variables.items() ]:
        result = obtain_equality(const.type)
        if result is not None:
            prods, term = result
            # how may arguments exactly follow the eq relation?
            equalities[name] = Equality(prods, term.func, term.args[-2], term.args[-1])

    return equalities

def run(task: 'Task'):
    print(task)
    for eq in generate_task_equality(task).values():
        print(eq)
