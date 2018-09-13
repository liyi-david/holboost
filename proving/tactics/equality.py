class Equality:
    def __init__(self, prods, equality_type, equality_left, equality_right):
        """
        for a simple equality lemma : forall x:nat, x = x, it's corresponding fields are:
            - prods = [ x:nat ]
            - equality_type = "=", i.e. Coq.Init.Logic.eq
            - equality_left = _REL_0_
            - equality_right = _REL_0
        """
        self.prods = prods
        self.equality = equality_type
        self.equality_left = equality_left
        self.equality_right = equality_right

    def __str__(self):
        return "(...) %s = %s, where = defined by %s" % (
                self.equality_left,
                self.equality_right,
                self.equality
                )
