

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


universe constraints
---


