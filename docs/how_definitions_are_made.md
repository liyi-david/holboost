

1. when a definition is given by the user, it will be parsed as a vernacular command and passed to the `do_definition` function in `vernac/command.ml, 147`
2. first the definition will be interpreted, in this step the following things are done:

    - generating const entry, including the checked term, side effect, etc. where side effect is represented by `Safe_typing.private_constants`
        - if it is in program mode, side effect is disabled
        - `Safe_typing.private_constants = Entries.side_effect`
        -
    - generating evar map
    - generating universe levels (if `Type`s are used in the expression)
    - imps?

3. the checked definition is passed to `DeclareDef.declare_definition`
4. invoke `interp/declare.ml` to declare the constant
