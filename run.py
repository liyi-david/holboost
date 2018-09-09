from kernel.term import *
from kernel.primitive import *
from kernel.vernac import *

p = Prod('a', PROP, SET)

declare_variable('v', p)
show('v')

l = Lambda('a', SET, Numeric(1))
print(l.str())
