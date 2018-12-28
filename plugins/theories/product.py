from kernel.term import Apply, Const, Construct, Ind

fst = Const("Coq.Init.Datatypes.fst")
snd = Const("Coq.Init.Datatypes.snd")
pair = Construct("Coq.Init.Datatypes.prod", 0, 0)
prod = Ind("Coq.Init.Datatypes.prod", 0)


def tuple(*elems) -> 'Term':
    assert len(elems) > 1, "cannot construct an empty or singeleton tuple"

    t = None
    for elem in reversed(elems):
        if t is None:
            t = elem
        else:
            t = Apply(pair, elem, t)

    return t


def tuple_nth(t: 'Term', n: int, typ: 'Term' = None) -> 'Term':

    """
    this function automatically generates the nth operator based on a set
    of fst/snd operations
    """

    is_tuple = False
    if typ is not None:
        is_tuple = isinstance(typ, Apply) and typ.func == prod
    else:
        is_tuple = isinstance(t, Apply) and t.func == pair

    if is_tuple:
        fst_type, snd_type = (t if typ is None else typ).args[0:2]
        if n == 0:
            # in this case we are obtaining a middle element in the tuple
            return Apply(fst, fst_type, snd_type, t)
        else:
            return tuple_nth(
                    Apply(snd, fst_type, snd_type, t),
                    n - 1,
                    snd_type
                    )
    else:
        assert n == 0, "you can only obtain the 0th element in a non-tuple"
        return t
