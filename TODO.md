- (fixme) export mutinds
- (done) loading test scripts
- (done, we do not really have to think about it!) consider how to deal with implicit arguments
- (done) write coq rewrite tactic
- (done) finish rewriting functions
- (done) json exporter
- (done) feed back terms to coq
- notation as lazy-evaluation system
    ```
    e.g. Notation(2) ---expand---> Apply(S, Notation(1))
    ...
    ```
- (done) add types in pattern
- (do not need anymore) simplify the term
- (done) rewrite all ocaml source files with yojson to avoid manual encoding errors
- (done) rewrite a better log system with levels in Top
- (done) the sync system is still not working
- (done) problem in type universe
- (done) modeling side effects (as a method of Term)
    

- check patterns in forall, make sure that bounded variables cannot be matched
- feedback exceptions when parsing or running commands
- further optmization through local pipe/file
- write a help document for the tool
- consider figuring out which libraries are buffered (when we import non-init libs, e.g. ZArith, it is extremely important since they are big!)
