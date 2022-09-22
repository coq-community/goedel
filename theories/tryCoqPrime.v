From Coqprime Require Import NatAux.

Goal divide 3 6. 
Proof. now exists 2. Qed.

Goal ~ divide 0 1.
Proof. intros [q Hq]. discriminate.  Qed.

From Coqprime Require Import ZCAux. 

Goal (3 | 6).
Proof. now exists 2. Qed.


