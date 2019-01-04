from .rewrite import RewriteProof
from .intro import IntroTactic
from .unfold import UnfoldTactic
from .simpl import SimplTactic

IntroTactic.register()
UnfoldTactic.register()
SimplTactic.register()
