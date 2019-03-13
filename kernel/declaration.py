from kernel.term import Construct, Ind, Binding, Term, Prod, Sort, SortEnum, Var, Const
from kernel.universe import Universe, NativeLevels
from kernel.universe import Universe, NativeLevels


class Constant:
    def __init__(self, name: 'str', typ: 'Term', json_body=None, is_builtin=False):
        self.name = name
        self.typ = typ
        self.json_body = json_body
        self.is_builtin=is_builtin

    @property
    def body(self):
        print('body rendered.')
        if self.json_body is None:
            return None

        return Term.from_json(self.json_body)

    def type(self, environment=None, context=[]):
        return self.typ

    def term(self):
        return Const(self.name)

    @classmethod
    def from_json(cls, json_item):
        return Constant(
                json_item['name'],
                Term.from_json(json_item['type']),
                None if 'body' not in json_item else json_item['body'],
                json_item['is_builtin']
                )

    def render(self, task):
        if self.body is None:
            return "Declaration %s\n\n\t: %s\n" % (self.name, self.type(task))
        else:
            return "Definition %s\n\n\t:  %s\n\t:= %s\n" % (self.name, self.type(task), self.body)

    def __str__(self):
        return self.render(None)


class Variable(Constant):
    def __init__(self, name: 'str', typ: 'Term'):
        Constant.__init__(self, name, typ)

    def term(self):
        return Var(self.name)

    @classmethod
    def from_json(cls, json_item):
        return Variable(
                json_item['name'],
                Term.from_json(json_item['type'])
                )


class MutInductive:

    class Constructor:
        def __init__(self, name: 'str', typ: 'Term'):
            self.name = name
            # the reason we use typ instead of type here is a consideration for dependent types
            self.typ = typ
            self.ind = None

        def term(self):
            return Construct(
                    self.ind.mutind.name,
                    self.ind.mutind.inds.index(self.ind),
                    self.ind.constructors.index(self)
                    )

        def __str__(self):
            return repr(self)

        def __repr__(self):
            return "%s : %s" % (self.name, self.type())

        @classmethod
        def from_json(cls, json_item):
            return cls(
                    json_item['name'],
                    Term.from_json(json_item['type'])
                    )

        def type(self, environment=None, context=[]):
            return self.typ.rels_subst([self.ind.term()])

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

        def term(self):
            return Ind(self.mutind.name, self.mutind.inds.index(self))

        def __repr__(self):
            return "<inductive %s : %s>" % (self.name, self.type())

        def __str__(self):
            str_constructors = "\n".join(map(lambda c: "\t| " + str(c), self.constructors))
            if len(self.constructors) == 0:
                str_constructors = "\tNO CONSTRUCTORS GIVEN."
            return "%s :\n" % self.name + \
                    "\tCONTEXT: %s\n" % (self.context) + \
                    "\tARITY  : %s\n" % self.arity + \
                    "---\n" + str_constructors

        @classmethod
        def from_json(cls, json_item):
            context = list(map(Binding.from_json, json_item['context']))

            # FIXME that is weird!
            if json_item['arity']['type'] == "template":
                arity = Term.from_json(json_item['arity']['arity'])
            else:
                arity = Term.from_json(json_item['arity']['arity'])

            ind = cls(
                    json_item['name'],
                    context,
                    arity,
                    list(map(MutInductive.Constructor.from_json, json_item['constructors']))
                    )

            ind.raw_arity = Term.from_json(json_item['arity']['arity'])
            return ind

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

    @classmethod
    def from_json(cls, json_item):
        return cls(
                json_item['name'],
                [ cls.Inductive.from_json(ind) for ind in json_item['inds'] ],
                json_item['is_builtin']
                )
