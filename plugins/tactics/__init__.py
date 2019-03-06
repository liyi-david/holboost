from .intro import IntroTactic
from .unfold import UnfoldTactic
from .simpl import SimplTactic
from .induction import InductionTactic
from .apply import ApplyTactic

IntroTactic.register()
UnfoldTactic.register()
SimplTactic.register()
InductionTactic.register()
ApplyTactic.register()
