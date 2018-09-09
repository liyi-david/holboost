"""
interpretations are used to handle the cases where we do not want to use low level concepts in Coq, Isabella, etc. for example,
natural numbers in Coq are represented by unary terms, e.g. 3 = (S (S (S O))). This may simplifies mathematical reasoning in Coq,
but it of course makes it harder to reason program properties. Instead, we want to use a natural number term as its interpretation.

"""
import abc

class Interpretation(abc.ABC):
    pass
