Require Import ZArith.
Require Import Holboost.plugin.

Open Scope Z_scope.

Definition hundred := 100.

Boom Print hundred.
Boom Remote "task['hundred'].body.autofold()".

Definition add := 2 + 5.
Boom Remote "task['add'].body.autofold()".
