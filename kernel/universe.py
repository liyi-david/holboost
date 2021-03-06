"""
support universes in python, currently only template polymorphism is supported
"""
from enum import Enum, unique
from itertools import product
import abc


class UniverseInconsistencyError(TypeError):
    pass


class Level(metaclass=abc.ABCMeta):
    def __init__(self):
        pass

    def __hash__(self):
        return id(self)

    @abc.abstractmethod
    def __le__(self, lvl):
        pass

    def __ge__(self, lvl):
        return lvl <= self

    def __lt__(self, lvl):
        return self <= lvl and self != lvl

    def __gt__(self, lvl):
        return self >= lvl and self != lvl

    def __eq__(self, lvl):
        return self >= lvl and self <= lvl

    def __ne__(self, lvl):
        return not (self == lvl)


class LevelConstraint:

    @unique
    class ExprType(Enum):
        leq = "<="
        lt = "<"
        eq = "=="

    def __init__(self, l, opr, r):
        self.l = l
        self.r = r
        self.opr = LevelConstraint.ExprType(opr)

    def __eq__(self, lc):
        return self.l == lc.l and self.opr == lc.opr and self.r == lc.r

    def __str__(self):
        return "%s %s %s" % (str(self.l), self.opr.value, str(self.r))

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        return str(self)

    def to_json(self):
        return {
                "left": self.l.to_json(),
                "opr": self.opr.value,
                "right": self.r.to_json()
                }


class Universe:
    def __init__(self, exprs):
        """
        @param exprs: a dictionary that maps levels to their offsets
        """
        self.exprs = exprs

    @classmethod
    def from_level(cls, level, offset):
        assert isinstance(level, Level)
        return Universe(
                { level : offset }
                )

    def singleton(self):
        return len(self.exprs) == 1

    def __add__(self, n):
        newexprs = {}
        for level in self.exprs:
            if level is NativeLevels.Prop():
                newexprs[NativeLevels.Set()] = self.exprs[level] + n
            else:
                newexprs[level] = self.exprs[level] + n

        return Universe(newexprs)

    @classmethod
    def union(cls, u1, u2):
        if u1 is None and u2 is None:
            raise TypeError
        elif u1 is None:
            return u2
        elif u2 is None:
            return u1

        exprs = {}
        for level, offset in list(u1.exprs.items()) + list(u2.exprs.items()):
            if level not in exprs:
                exprs[level] = offset
            else:
                exprs[level] = max(exprs[level], offset)

        return Universe(exprs)

    # the following overwritten functions are used to generate universe constraints (i.e. level constraints)
    def __le__(self, univ):
        constraints = []
        assert univ.singleton(), "cannot do comparison like ... <= max(..., ..., ...)"

        for l, r in product(self.exprs, univ.exprs):
            offl, offr = self.exprs[l], univ.exprs[r]
            """
            suppose the the left expr is (l, offl), right expr is (r, offr)
            l + offl <= r + offr
            """

            if r is NativeLevels.Set() and offr == 1:
                # FIXME this is a hack to handle template polymorphism in inductives
                pass
            elif l == r:
                if offl > offr:
                    raise UniverseInconsistencyError("%s, %s" % (self, univ))
                else:
                    pass
            elif l in (NativeLevels.Set(), NativeLevels.Prop()):
                if r in (NativeLevels.Set(), NativeLevels.Prop()):
                    if offl > offr:
                        # raise UniverseInconsistencyError("%s, %s" % (self, univ))
                        pass
                    else:
                        pass
                else:
                    # r is a level variable
                    if offr - offl + 1 < 0:
                        # e.g. Set + 1 + n <= Top.? + n ( + m )
                        # offl = n + 1
                        # offr = m + n
                        # offr - offl = m - 1
                        # m >= 0
                        raise UniverseInconsistencyError("%s, %s" % (self, univ))
            elif r in (NativeLevels.Set(), NativeLevels.Prop()):
                raise Exception("cannot resolve %s <= %s" % (str(self), str(univ)))
            else:
                # both l and r are level variables
                if offl == offr:
                    constraints.append(LevelConstraint(l, "<=", r))
                elif offl == offr + 1:
                    constraints.append(LevelConstraint(l, "<", r))
                else:
                    raise UniverseInconsistencyError("%s, %s" % (self, univ))


        return set(constraints)

    def __lt__(self, univ):
        raise Exception("unimplemented")

        return set(constraints)

    def __eq__(self, univ):
        raise Exception("unimplemented yet")

    @staticmethod
    def from_json(json):
        assert isinstance(json, list)
        exprs = {
                CoqLevel.from_json(level): index for (level, index) in json
                }
        return Universe(exprs)

    def __str__(self):
        return ",".join(map(
            lambda lvl: str(lvl) + ("" if self.exprs[lvl] == 0 else "+" + str(self.exprs[lvl])),
            self.exprs
            ))


class UniverseInstance:
    def __init__(self, levels):
        if isinstance(levels, Level):
            self.levels = [levels]
        else:
            self.levels = levels

    @staticmethod
    def from_json(json):
        if json is None:
            json = []

        assert isinstance(json, list)
        return UniverseInstance(
                list(map(CoqLevel.from_json, json))
                )

    def to_json(self):
        return list(map(lambda level: level.to_json(), self.levels))

    def __str__(self):
        if len(self.levels) > 0:
            return "@{" + ",".join(map(lambda lvl: str(lvl), self.levels)) + "}"
        else:
            return ""


"""
different kind of levels
"""

# native levels
class NativeLevels:
    """
    this is native levels used in holboost
    """

    class Set(Level):
        __instance = None

        def __new__(cls):
            if cls.__instance is None:
                cls.__instance = object.__new__(cls)

            return cls.__instance

        def __le__(self, level):
            return level is not NativeLevels.Prop()


        def __str__(self):
            return "Set"

        def to_json(self):
            return [ "Set" ]

    class Prop(Level):
        __instance = None

        def __new__(cls):
            if cls.__instance is None:
                cls.__instance = object.__new__(cls)

            return cls.__instance

        def __le__(self, level):
            return True

        def __str__(self):
            return "Prop"

        def to_json(self): return [ "Prop" ]


    class Variable(Level):
        def __init__(self, id=None):
            self.id = id

        def __le__(self, level):
            raise UniverseInconsistencyError

        def __str__(self):
            return str(self.id)

        def to_json(self):
            return [ self.id ]

# coq levels
class CoqLevel(Level):
    def __init__(self, dirpath: list=[], offset: int=0, isprop=False, isset=False, var=None):
        # a coq level can be either Prop, Set, Level or Var
        # plz refer to `kernel/univ.ml(i)` for further information
        self.isprop = isprop
        self.isset = isset
        self.dirpath = dirpath
        self.offset = offset
        self.var = var

    @staticmethod
    def from_json(json):
        if json is None:
            json = []

        if len(json) == 1:
            if json[0] == "Prop":
                return NativeLevels.Prop()
            elif json[0] == "Set":
                return NativeLevels.Set()
            elif json[0].startswith("Var("):
                return NativeLevels.Variable(int(json[0][4:-1]))
        # the list at least includes one path element and an offset
        # we dont render error message bug debug information since this assertion shall not failed
        # in production environment
        assert isinstance(json, list) and len(json) >= 2, json
        return CoqLevel(json[:-1], int(json[-1]))

    def to_json(self):
        if self.isprop:
            return ["Prop"]
        elif self.isset:
            return ["Set"]
        elif self.var is not None:
            return [self.var]
        else:
            return self.dirpath + [self.offset]

    def __hash__(self):
        return id(self)

    def __eq__(self, lvl):
        return isinstance(lvl, CoqLevel) and str(self) == str(lvl)

    def __le__(self, lvl):
        return False

    def __str__(self):
        if self.isprop:
            return "Prop"
        elif self.isset:
            return "Set"
        elif self.var is not None:
            return "Var(%d)" % self.var
        else:
            return ".".join(self.dirpath) + "." + str(self.offset)
