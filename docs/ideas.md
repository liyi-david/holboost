some ideas about proof
---

consider we have a macro called `proved`, or in holboost called interpretation, it can be used to represent a proof, or instantiated formula, e.g.

    goal: nat
    goal: #(proved nat 1) where

        its type is nat, and its value is 1 (proof)

    goal is proved


designs of extensible term systems (macors)
--

- Interpretation
    
    - CoqProvable
    - CoqCompatible
    - SMTProvable
    - ...


how rewrite command can be integrated as a normal proofview
---

- first make the target formula (to rewrite) as a goal (in the proofview)
- implement intro
