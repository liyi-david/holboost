Require Import Holboost.plugin.

Inductive I1 : Set := i1
    with I2 : Set := i2 : I1 -> I2.

Boom Print I2.
