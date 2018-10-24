how proofs are completed (Qed)
===

steps
---

1. `parsing/g_proofs.ml4` Qed vernac is parsed
2. `vernac/vernacentries.ml` vernac Qed is interpreted and `vernac_end_proof` is called
3. `vernac/lemmas.ml` save_proof is called. when the goal is proved, this function takes its proof object and terminator (line 514)
4. `vernac/lemmas.ml`

    - if the proof is empty and given explicitly, the kernel will accept it (this could be used by smt solvers?)
    - otherwise the terminator is applied and check whether the proof is correct
    - TODO where are the terminators ????
