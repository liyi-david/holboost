Require Import ZArith.
Require Import Holboost.plugin.

Open Scope Z_scope.

Definition hundred := 100.
Boom ExtractConstantBody On.

Boom Print hundred.
Boom Remote "__task__['hundred'].body.fold()".

Definition add := 2 + 5.
Boom Remote "__task__['add'].body.fold()".
