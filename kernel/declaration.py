from kernel.term import Construct, Ind, Binding, Term, Prod, Sort, SortEnum
from kernel.universe import Universe, NativeLevels
from kernel.universe import Universe, NativeLevels


class Constant:
    def __init__(self, name: 'str', typ: 'Term', body=None, is_builtin=False):
        self.name = name
        self.typ = typ
        self.body = body
        self.is_builtin=is_builtin

    def type(self, environment=None, context=[]):
        return self.typ

    def __str__(self):
        if self.body is None:
            return "%s: %s" % (self.name, self.type)
        else:
            return "%s: %s := %s" % (self.name, self.type, self.body)


class MutInductive:

    class Constructor:
        def __init__(self, name: 'str', typ: 'Term'):
            self.name = name
            # the reason we use typ instead of type here is a consideration for dependent types
            self.typ = typ
            self.ind = None

        def __str__(self):
            return repr(self)

        def __repr__(self):
            return "%s : %s" % (self.name, self.type())

        @classmethod
        def from_json(cls, json_item):
            return cls(
                    json_item['constructor_name'],
                    Term.from_json(json_item['constructor_type'])
                    )

        def type(self, environment=None, context=[]):
            return self.typ.rels_subst([self.ind.as_term()])

    class Inductive:
        def __init__(self, name: 'str', context, arity, constructors):
            self.name = name
            self.context = context
            self.arity = arity
            self.raw_arity = None
            self.mutind = None
            self.constructors = constructors
            for c in self.constructors:
                c.ind = self

        def __repr__(self):
            return "<inductive %s : %s>" % (self.name, self.type())

        def __str__(self):
            return "%s :\n" % self.name + \
                    "\tCONTEXT: %s\n" % (self.context) + \
                    "\tARITY  : %s\n" % self.arity + \
                    "---\n" + \
                    "\n".join(map(lambda c: "\t| " + str(c), self.constructors))

        @classmethod
        def from_json(cls, json_item):
            context = list(map(Binding.from_json, json_item['context']))

            # FIXME that is weird!
            if json_item['arity']['type'] == "template":
                arity = Term.from_json(json_item['arity']['arity'])
            else:
                arity = Term.from_json(json_item['arity']['arity'])

            ind = cls(
                    json_item['ind_name'],
                    context,
                    arity,
                    list(map(MutInductive.Constructor.from_json, json_item['constructors']))
                    )

            ind.raw_arity = Term.from_json(json_item['arity']['arity'])
            return ind

        def as_term(self):
            return Ind(self.mutind.name, self.mutind.inds.index(self))

        def type(self, environment=None, context=[]):
            typ = self.arity

            # for binding in reversed(self.context):
                # if isinstance(binding.type, Sort) and binding.type.sort == SortEnum.type:
                    # # template polymorphism
                    # binding_type = Sort.mkType(Universe.from_level(NativeLevels.Set(), 1))
                # else:
                    # binding_type = binding.type

                # typ = Prod(None, binding_type, typ)

            return typ

        def render(self, environment=None):
            return "%s := \n%s" % (
                    self.type(environment).render(environment),
                    "\n| ".join(map(lambda c: c.name + ": " + c.type(environment).render(environment), self.constructors))
                    )


    def __init__(self, name: 'str', inds: 'Inductive list', is_builtin=False):
        self.name = name
        self.inds = inds
        for i in self.inds:
            i.mutind = self

        self.is_builtin=is_builtin

    def __str__(self):
        s = "Mut-Inductive %s:\n\n" % self.name
        for i in self.inds:
            s += "[%d] " % self.inds.index(i)
            s += str(i)
            s += "\n"

        return s

    def __repr__(self):
        return "<mut-inductive %s with %d inductives>" % (self.name, len(self.inds))
