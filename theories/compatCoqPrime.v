From Coq Require Import Arith.
From Coq Require Import Wf_nat.
From Coq Require Import ZArith.
From Coq Require Import Peano_dec.
From Coq Require Import ZArith_dec.

From Coqprime  Require Import NatAux ZCAux ZCmisc ZSum Pmod Ppow.
(* should be removed later ! *)
(* From Pocklington Require gcd divides  prime modprime.  *)



(** * Compatibility lemmas (provisional) *)

(** more general than [NatAux] lemma *)

Lemma divide_le1 d n : (0 < n)%nat ->  divide d n -> (d <= n)%nat.
Proof.
  destruct n. 
  - inversion 1.
  - destruct n.
    + intros _ [q Hq]; destruct (Nat.eq_mul_1 d q)
        as [[H1 H'1] _];
        [now symmetry| subst; apply le_n].
    + intros; apply NatAux.divide_le; auto with arith.
Qed. 



Locate divide. 
(*  Z.divide = fun x y : Z => exists z : Z, y = z * x
     : Z -> Z -> Prop
 *)
Locate divide. 

Lemma zdivdiv_compat (a b: Z) :
  Z.divide a b -> divide (Z.abs_nat a) (Z.abs_nat b).
Proof.
  intros [q Hq]; exists (Z.abs_nat q); subst.
  now rewrite Zabs2Nat.inj_mul, Nat.mul_comm.
Qed.

Lemma divZdiv_compat (a b: nat) :
  divide a  b -> Z.divide (Z.of_nat a) (Z.of_nat b). 
Proof.
  intros [q Hq]; exists (Z.of_nat q); subst.
  now rewrite Nat2Z.inj_mul, Z.mul_comm. 
Qed. 



Definition CoPrime (a b : nat) :=
  Zis_gcd (Z.of_nat a) (Z.of_nat b) 1%Z.



Lemma coPrimeSym : forall a b : nat, CoPrime a b -> CoPrime b a.
Proof. intros; apply Zis_gcd_sym; assumption. Qed.

(** Gauss theorem *)
Lemma coPrimeMult :
  forall a b c : nat, CoPrime a b -> divide a (b * c) -> divide a c.
Proof. 
  unfold CoPrime; intros a b c H H0; apply   divZdiv_compat in H0. 
  rewrite <- (Zabs2Nat.id a), <- (Zabs2Nat.id c);
    apply zdivdiv_compat.
  apply Gauss with (Z.of_nat b). 
  - now rewrite <- Nat2Z.inj_mul. 
  - apply H. 
Qed. 

(* same proof script as in [chRem] *)
Lemma coPrimeMult2 :
  forall a b c : nat,
    CoPrime a b -> divide a c -> divide b c -> divide (a * b) c.
Proof.
  intros a b c H H0 [x H1].
  assert (divide a x).
  { eapply coPrimeMult with (1:= H); now rewrite <- H1. }
  destruct H2 as [x0 H2]; exists x0; subst; ring.   
Qed.


Lemma ltgt1 : forall a b : nat, (a < b -> b > 0)%nat. 
Proof. intros a b Hab; eapply Nat.le_lt_trans with a;
         auto with arith.
Qed.

Notation minus1 := Z.sub_cancel_r.


Lemma chRem2 :
  forall b1 r1 b2 r2 q : Z,
    (0 <= r1)%Z ->
    (0 <= r2)%Z ->
    (r1 < q)%Z -> (r2 < q)%Z -> (b1 * q + r1)%Z = (b2 * q + r2)%Z ->
    r1 = r2.
Proof. 
  intros ? ? ? ? ? H H0 H1 H2 H3;
    specialize (Z.div_mod_unique q b1 b2 r1 r2) as H4. 
  destruct H4; subst. 
  - left; lia. 
  - left; lia. 
  -  now repeat rewrite (Z.mul_comm q).
  -  reflexivity.
Qed. 
Search Z.of_nat Logic.eq. 

Notation Z_of_nat_inj := Nat2Z.inj. 

Open Scope nat_scope. 
Lemma uniqueRem :
 forall r1 r2 b : nat,
 b > 0 ->
 forall a : nat,
 (exists q : nat, a = q * b + r1 /\ b > r1) ->
 (exists q : nat, a = q * b + r2 /\ b > r2) -> r1 = r2.
Proof. 
  intros r1 r2 b Hb a [q1 [Hq1 Hq1']] [q2 [Hq2 Hq2']].
  apply Nat2Z.inj; eapply chRem2.
  1, 2: apply Nat2Z.is_nonneg.
  apply Nat2Z.inj_lt.
  apply Hq1'. 
  apply Nat2Z.inj_lt; assumption. 
  rewrite Hq1 in Hq2. 
  repeat rewrite <- Znat.inj_mult.
  repeat rewrite <- Znat.inj_plus.
  rewrite  Nat2Z.inj_iff.  apply Hq2.
Qed.

Lemma modulo : (* same script as [chRem] *)
  forall b : nat,
    b > 0 ->
    forall a : nat, {p : nat * nat
                    | a = fst p * b + snd p /\ b > snd p}.
Proof.
  intros b H a; apply (gt_wf_rec a).
  intros n H0 .
  destruct (le_lt_dec b n) as [Hle | Hlt].
  - assert (n > n - b).
    { unfold gt in |- *; apply lt_minus; assumption. }
    destruct (H0 _ H1) as [[a1 b0] p].
    simpl in p;  exists (S a1, b0); simpl in |- *.
    destruct p as (H2, H3).
    split.
    + rewrite <- Nat.add_assoc, <- H2.
      now apply le_plus_minus.
    + assumption.
  -  exists (0, n);   simpl in |- *; now split.
Qed.


(* same script as in [chRem] *)

Lemma chRem1 :
 forall b : nat,  b > 0 -> forall a : Z,
     {p : Z * nat | snd p < b /\
                      Z.of_nat (snd p) = (fst p * Z.of_nat b + a)%Z}.
Proof.
  intros b H a.
  assert
    (H0: forall a' : Z,
        (a' >= 0)%Z ->
        {p : Z * nat | snd p < b /\
                         Z.of_nat (snd p) =
                           (fst p * Z.of_nat b + a')%Z}).
  { intros a' H0; set (A := Z.to_nat a') in *.
    induction (modulo b H A) as [x p].
    destruct x as (a0, b0).
    exists ((- Z.of_nat a0)%Z, b0).
    destruct p as (H1, H2).
    split.
    - apply H2.
    - rewrite <- (Z2Nat.id a'). 
      + simpl fst ; simpl snd. 
        rewrite Zopp_mult_distr_l_reverse.
        rewrite Z.add_comm.
        fold (Z.of_nat (Z.to_nat a') - Z.of_nat a0 * Z.of_nat b)%Z
          in |- *.
        apply Zplus_minus_eq.
        rewrite <- Znat.inj_mult.
        rewrite <- Znat.inj_plus.
        apply Znat.inj_eq.
        apply H1.
      + auto.
        now rewrite <- Z.ge_le_iff.
  }
  destruct (Z_ge_lt_dec a 0).
  + apply H0; assumption.
  + assert (a + Z.of_nat b * - a >= 0)%Z.
    induction b as [| b Hrecb].
    * elim (lt_irrefl _ H).
    * rewrite Znat.inj_S.
      rewrite Z.mul_comm.
      rewrite <- Zmult_succ_r_reverse.
      fold (- a * Z.of_nat b - a)%Z in |- *.
      rewrite Zplus_minus.
      replace 0%Z with (0 * Z.of_nat b)%Z.
      apply Zmult_ge_compat_r.
      rewrite (Zminus_diag_reverse a).
      rewrite <- (Zplus_0_l (- a)).
      unfold Zminus in |- *.
      apply Z.le_ge.
      apply Zplus_le_compat_r.
      apply Zlt_le_weak.
      assumption.
      replace 0%Z with (Z.of_nat 0).
      apply Znat.inj_ge.
      unfold ge in |- *.
      apply le_O_n.
      auto.
      auto.
    * induction (H0 _ H1) as [x [H2 H3]].
      induction x as (a0, b1).
      exists ((a0 - a)%Z, b1).
      split.
      -- simpl in |- *; apply H2.
      -- cbv beta iota zeta delta [fst snd] in |- *.
         cbv beta iota zeta delta [fst snd] in H3.
         rewrite H3.
         rewrite (Zplus_comm a).
         rewrite Zplus_assoc.
         apply Zplus_eq_compat.
         rewrite Zmult_minus_distr_r.
         unfold Zminus in |- *.
         apply Zplus_eq_compat.
         reflexivity.
         rewrite Z.mul_comm.
         apply Zopp_mult_distr_l_reverse.
         reflexivity.
Qed.


(*
Lemma Zis_gcd_compat a b x y :
  y = Z.of_nat x -> 
  (Pocklington.gcd.gcd (Z.of_nat a) (Z.of_nat b) x <->
     Zis_gcd (Z.of_nat a) (Z.of_nat b) y).
  unfold Pocklington.gcd.gcd.  
  split.
  

   - destruct 1. constructor. 
     subst y.      
     destruct H0. 
    Search Z.abs_nat Z.of_nat.
    rewrite  Zabs2Nat.id in H, H0.
    now apply divZdiv_compat.
    subst. 
 destruct H0. 
 rewrite  Zabs2Nat.id in H, H0.
 now apply divZdiv_compat.
intros. 
specialize (H1 (Z.abs_nat x0)). 
subst y.



Abort.   
 *)
