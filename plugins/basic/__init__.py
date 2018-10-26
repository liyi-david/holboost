from kernel.term import *

# some global shortcuts
Prop = Sort.mkProp()
Set = Sort.mkSet()
Type = lambda univ: Sort.mkType(univ)

# term constructors
def imply(A, B):
    return Prod(None, A, B)
