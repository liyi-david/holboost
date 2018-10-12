"""
support universes in python, currently only template polymorphism is supported
"""

import abc

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


class Universe:
    def __init__(self, exprs):
        self.exprs = exprs

    def __add__(self, n):
        newexprs = {
                lvl : self.exprs[lvl] + 1 for lvl in self.exprs
                }
        return Universe(newexprs)

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
        self.levels = levels

    @staticmethod
    def from_json(json):
        assert isinstance(json, list)
        return UniverseInstance(
                list(map(CoqLevel.from_json, json))
                )

    def to_json(self):
        return list(map(lambda level: level.to_json(), self.levels))

    def __str__(self):
        return ",".join(map(lambda lvl: str(lvl), self.levels))


"""
different kind of levels
"""

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
        if len(json) == 1:
            if json[0] == "Prop":
                return CoqLevel(isprop=True)
            elif json[0] == "Set":
                return CoqLevel(isset=True)
            elif json[0].startswith("Var("):
                return CoqLevel(var=int(json[0][4:-1]))
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

    def __le__(self, lvl):
        return True

    def __str__(self):
        if self.isprop:
            return "Prop"
        elif self.isset:
            return "Set"
        elif self.var is not None:
            return "Var(%d)" % self.var
        else:
            return ".".join(self.dirpath) + "." + str(self.offset)
