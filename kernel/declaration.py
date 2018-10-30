from kernel.term import Construct, Ind, Binding, Term, Prod, Sort, SortEnum
from kernel.universe import Universe, NativeLevels
from kernel.universe import Universe, NativeLevels


class Constant:
    def __init__(self, name: 'str', type: 'Term', body=None, is_builtin=False):
        self.name = name
        self.type = type
        self.body = body
        self.is_builtin=is_builtin

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
            self.mutind = None
            self.constructors = constructors
            for c in self.constructors:
                c.ind = self

        @classmethod
        def from_json(cls, json_item):
            context = list(map(Binding.from_json, json_item['context']))

            # FIXME that is weird!
            if json_item['arity']['type'] == "template":
                arity = Term.from_json(json_item['arity']['arity'])
                for binding in context:
                    if isinstance(binding.type, Sort) and binding.type.sort == SortEnum.type:
                        arity = arity.body
            else:
                arity = Term.from_json(json_item['arity']['arity'])

            return cls(
                    json_item['ind_name'],
                    context,
                    arity,
                    list(map(MutInductive.Constructor.from_json, json_item['constructors']))
                    )

        def as_term(self):
            return Ind(self.mutind.name, self.mutind.inds.index(self))

        def type(self, environment=None, context=[]):
            typ = self.arity
            for binding in reversed(self.context):
                if isinstance(binding.type, Sort) and binding.type.sort == SortEnum.type:
                    # template polymorphism
                    binding_type = Sort.mkType(Universe.from_level(NativeLevels.Set(), 1))
                else:
                    binding_type = binding.type

                typ = Prod(None, binding_type, typ)

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

