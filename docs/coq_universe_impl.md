

in the pCIC theory, levels of types are defined as

    Type : Type(1) : Type(2) : ...

I want to repeat thie in Coq, so I implemented a function

    Definition typ {T:Type} (_:T) := T.

that returns the type of a term.

When I define a new type universe in Coq, i.e.

    Definition T0 := Type.

The universe of this type is `Top.5`, which can be confirmed by `Boom Print T0`.
And if we want to know the type of T0, we define

    Definition T1 := typ T0.

And find that type of T1 is `Top.1`, i.e. T1 is a type that belongs to the firstly
declared type universe.


sorts
===

primitive types (here types) are called sorts in Coq, including `Set`, `Prop` and `Type`. `Type`s are declared together with their universes.

inductives
---

definitions of inductives includes:

1. name of the inductive
2. context of the inductive
3. arity of the inductive
4.

template polymorphism in inductives
---

consider the following definition in Coq

    Variable ft : Type -> Type.
    Inductive T : Type := tt : Type -> T.

and check the type of them, we have

    ft: Type{Top.a} -> Type{Top.b}

and 

    T: Type{Set + 1}

if we apply `ft` to `T` (in the early version of holboost), it reports universe inconsisency. Clearly, there is no guarantee that `Set + 1 <= Top.a`.
Such inconsisency leads to the template polymorphism in inductives, i.e. the arity of an inductive can be replaced by any `Type`.


known bug
===

1. polymorphic variables are not working properly, e.g.

        Section A.
            Polymorphic Variable T:Type.
            Boom Check T.

    you will find that T is still declared with a statically initialized universe, e.g. `Type@{Top.xx}`

