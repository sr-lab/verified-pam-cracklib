Require Import Coq.Arith.Arith.

Module NatNotations.
  
  Notation "a >? b" := (negb (a <=? b)) (at level 70).
  Notation "a >=? b" := (negb (a <? b)) (at level 70).

End NatNotations.