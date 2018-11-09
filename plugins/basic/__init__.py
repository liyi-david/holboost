from kernel.term import *

from .boom import BoomLanguage

# some global shortcuts
Prop = Sort.mkProp()
Set = Sort.mkSet()
Type = lambda univ: Sort.mkType(univ)

# register the language
BoomLanguage.register()
