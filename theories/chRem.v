From Coq Require Import Arith.
From Coq Require Import Wf_nat.
From Coq Require Import ZArith.
From Coq Require Import Peano_dec.
From Coq Require Import ZArith_dec.


(* should be removed later ! *)
From Pocklington Require gcd divides natZ prime modprime. 
From Coq Require Import Max.



From Coqprime
  Require Import NatAux ZCAux ZCmisc ZSum Pmod Ppow.

Lemma divide_le d n (* compatibility with CoqPrime *)
  : (0 < n)%nat ->
    Pocklington.divides.Divides d n ->
    (d <= n)%nat.
Proof.
  destruct n. 
  - inversion 1.
  - destruct n.
    + intros _ [q Hq]; destruct (Nat.eq_mul_1 d q)
        as [[H1 H'1] _];
        [now symmetry| subst; apply le_n].
    + intros; apply NatAux.divide_le; auto with arith.
Qed. 


(* provisional *)

Lemma divides_compat x y : Pocklington.divides.Divides x y <->
                             divide x y. 
Proof. split; intros [q Hq]; now exists q. Qed. 


Definition CoPrime (a b : nat) :=
  Pocklington.gcd.gcd (Z.of_nat a) (Z.of_nat b) 1.

(* Should be:
   Zis_gcd (Z.of_nat a) (Z.of_nat b) 1%Z. *)

Lemma coPrimeSym : forall a b : nat, CoPrime a b -> CoPrime b a.
Proof. intros; now apply Pocklington.gcd.gcd_sym. Qed.

Lemma coPrimeMult :
  forall a b c : nat, CoPrime a b -> divide a (b * c) -> divide a c.
Proof.
  intros ? ? ? H H0; unfold CoPrime in H.
  induction a as [| a Hreca].
  - (* a = 0 *)
    induction H0 as (x, H0).
    cbn in H0. rewrite Nat.eq_mul_0 in H0. (* b = O \/ c = O *)
    destruct H0 as [H1 | H1].
    + rewrite H1 in H; unfold gcd.gcd in H.
      induction H as (H, H2).
      assert (2 <= 1)%nat.
      { apply H2;split; cbn.
        1,2: exists 0%nat; now rewrite Nat.mul_comm.
      }
      destruct (le_Sn_n _ H0).
    + exists 0%nat; now rewrite H1.
  - clear Hreca;
      assert (H1: (S a > 0)%nat) by apply gt_Sn_O.
    destruct (Pocklington.gcd.gcd_lincomb_nat _ _ _ H1 H)
      as [x [x0 H2]].
    destruct H0 as [x1 H0].
    assert
      ((1 * Z.of_nat c)%Z =
         (Z.of_nat (S a) * (x * Z.of_nat c + Z.of_nat x1 * x0))%Z).
    { rewrite (Z.mul_comm (Z.of_nat (S a))).
      rewrite  Z.mul_add_distr_r.
      rewrite (Z.mul_comm (x * Z.of_nat c)).
      rewrite (Z.mul_comm (Z.of_nat x1 * x0)).
      repeat rewrite Z.mul_assoc.
      rewrite <- Znat.inj_mult.
      rewrite <- H0.
      rewrite Znat.inj_mult.
      rewrite (Z.mul_comm (Z.of_nat b)).
      rewrite <- (Z.mul_assoc (Z.of_nat c)).
      rewrite (Z.mul_comm (Z.of_nat c)).
      rewrite  <- Z.mul_add_distr_r.
      now rewrite <- H2.
    }
    rewrite Zmult_1_l in H3.
    assert (Pocklington.divides.ZDivides (Z.of_nat (S a)) (Z.of_nat c)).
    { now exists (x * Z.of_nat c + Z.of_nat x1 * x0)%Z. }
    clear H2 H3 x x0.
    rewrite <- (Znat.Zabs2Nat.id (S a)).
    rewrite <- (Znat.Zabs2Nat.id c).
    now apply Pocklington.divides.zdivdiv.
Qed.




Lemma coPrimeMult2 :
  forall a b c : nat,
    CoPrime a b -> divide a c -> divide b c -> divide (a * b) c.
Proof.
  intros a b c H H0 [x H1].
  assert (Pocklington.divides.Divides a x).
  { eapply coPrimeMult with (1:= H); now rewrite <- H1. }
  destruct H2 as [x0 H2]; exists x0; subst; ring.   
Qed.

Lemma ltgt1 : forall a b : nat, (a < b -> b > 0)%nat. 
Proof. lia. Qed.

Lemma minus1 : forall a b c : Z, (a - c)%Z = (b - c)%Z -> a = b.
Proof. lia. Qed.

Lemma chRem2 :
  forall b1 r1 b2 r2 q : Z,
    (0 <= r1)%Z ->
    (0 <= r2)%Z ->
    (r1 < q)%Z -> (r2 < q)%Z -> (b1 * q + r1)%Z = (b2 * q + r2)%Z ->
    r1 = r2.
Proof.
  intros * H H0 H1 H2 H3.
  assert (H4: ((b1 - b2) * q)%Z = (r2 - r1)%Z) by
    (rewrite  Z.mul_sub_distr_r; lia).
  induction (Zle_or_lt 0 (b1 - b2)) as [H5 | H5].
  induction (Zle_lt_or_eq _ _ H5) as [H6 | H6].
  assert (H7: (1 <= b1 - b2)%Z).
  { replace 1%Z with (Z.succ 0).
    apply Zlt_le_succ.
    assumption.
    auto.
  }
  assert (H8:(q <= r2 - r1)%Z).
  { replace q with (1 * q)%Z.
    rewrite <- H4.
    apply Zmult_le_compat_r.
    assumption.
    eapply Z.le_trans.
    apply H.
    apply Zlt_le_weak.
    assumption.
    apply Zmult_1_l.
  }
  set (A1 := Zplus_lt_le_compat r2 q (- r1) 0 H2) in *.
  assert (H9:(r2 - r1 < q)%Z).
  { replace q with (q + 0)%Z.
    unfold Zminus in |- *.
    apply A1.
    eapply (fun a b : Z => Zplus_le_reg_l a b r1).
    rewrite Zplus_opp_r.
    rewrite <- Zplus_0_r_reverse.
    assumption.
    rewrite <- Zplus_0_r_reverse.
    reflexivity.
  }
  elim (Zle_not_lt q (r2 - r1)).
  assumption.
  assumption.
  rewrite <- H6 in H4.
  rewrite Z.mul_comm in H4.
  rewrite <- Zmult_0_r_reverse in H4.
  rewrite <- (Zplus_opp_r r2) in H4.
  unfold Zminus in H4.
  apply Z.opp_inj.
  symmetry  in |- *.
  eapply Zplus_reg_l.
  apply H4.
  assert (H6:(1 <= b2 - b1)%Z).
  { replace 1%Z with (Z.succ 0).
    apply Zlt_le_succ.
    apply (Zplus_lt_reg_l 0 (b2 - b1) b1).
    rewrite Zplus_minus.
    rewrite <- Zplus_0_r_reverse.
    apply (Zplus_lt_reg_l b1 b2 (- b2)).
    rewrite Zplus_opp_l.
    rewrite Zplus_comm.
    unfold Zminus in H5.
    assumption.
    auto.
  }
  assert (H7: ((b2 - b1) * q)%Z = (r1 - r2)%Z) by
    ( rewrite Z.mul_sub_distr_r ; lia ).
  assert (H8:(q <= r1 - r2)%Z).
  { replace q with (1 * q)%Z.
    rewrite <- H7.
    apply Zmult_le_compat_r.
    assumption.
    eapply Z.le_trans.
    apply H.
    apply Zlt_le_weak.
    assumption.
    apply Zmult_1_l.
  }
  set (A1 := Zplus_lt_le_compat r1 q (- r2) 0 H1) in *.
  assert (H9:(r1 - r2 < q)%Z).
  { replace q with (q + 0)%Z.
    unfold Zminus in |- *.
    apply A1.
    eapply (fun a b : Z => Zplus_le_reg_l a b r2).
    rewrite Zplus_opp_r.
    rewrite <- Zplus_0_r_reverse.
    assumption.
    rewrite <- Zplus_0_r_reverse.
    reflexivity.
  }
  elim (Zle_not_lt q (r1 - r2)).
  assumption.
  assumption.
Qed.

Lemma Z_of_nat_inj: forall a b : nat, Z.of_nat a = Z.of_nat b -> a = b.
Proof. lia. Qed.

Open Scope nat_scope. 

Lemma uniqueRem :
 forall r1 r2 b : nat,
 b > 0 ->
 forall a : nat,
 (exists q : nat, a = q * b + r1 /\ b > r1) ->
 (exists q : nat, a = q * b + r2 /\ b > r2) -> r1 = r2.
Proof.
intros.
induction H0 as (x, H0); induction H0 as (H0, H2).
induction H1 as (x0, H1); induction H1 as (H1, H3).
apply Z_of_nat_inj.
eapply chRem2.
replace 0%Z with (Z.of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z.of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply H2.
apply Znat.inj_lt.
apply H3.
repeat rewrite <- Znat.inj_mult.
repeat rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
transitivity a.
symmetry  in |- *.
apply H0.
apply H1.
Qed.

Lemma modulo :
 forall b : nat,
 b > 0 ->
 forall a : nat, {p : nat * nat | a = fst p * b + snd p /\ b > snd p}.
Proof.
intros.
apply (gt_wf_rec a).
intros.
induction (le_lt_dec b n).
assert (n > n - b).
unfold gt in |- *.
apply lt_minus.
assumption.
assumption.
induction (H0 _ H1).
induction x as (a1, b0).
simpl in p.
exists (S a1, b0).
simpl in |- *.
induction p as (H2, H3).
split.
rewrite <- Nat.add_assoc.
rewrite <- H2.
apply le_plus_minus.
assumption.
assumption.
exists (0, n).
simpl in |- *.
split.
reflexivity.
assumption.
Qed.


Lemma chRem1 :
 forall b : nat,
 b > 0 ->
 forall a : Z,
 {p : Z * nat | snd p < b /\ Z.of_nat (snd p) = (fst p * Z.of_nat b + a)%Z}.
Proof.
intros.
assert
 (forall a' : Z,
  (a' >= 0)%Z ->
  {p : Z * nat | snd p < b /\ Z.of_nat (snd p) = (fst p * Z.of_nat b + a')%Z}).
intros.
set (A := Z.abs_nat a') in *.
induction (modulo b H A).
induction x as (a0, b0).
exists ((- Z.of_nat a0)%Z, b0).
induction p as (H1, H2).
split.
apply H2.
rewrite <- (Pocklington.natZ.inj_abs_pos a').
replace (fst ((- Z.of_nat a0)%Z, b0)) with (- Z.of_nat a0)%Z.
replace (snd ((- Z.of_nat a0)%Z, b0)) with b0.
rewrite Zopp_mult_distr_l_reverse.
rewrite Zplus_comm.
fold (Z.of_nat (Z.abs_nat a') - Z.of_nat a0 * Z.of_nat b)%Z in |- *.
apply Zplus_minus_eq.
rewrite <- Znat.inj_mult.
rewrite <- Znat.inj_plus.
apply Znat.inj_eq.
apply H1.
auto.
auto.
assumption.

induction (Z_ge_lt_dec a 0).
apply H0.
assumption.
assert (a + Z.of_nat b * - a >= 0)%Z.
induction b as [| b Hrecb].
elim (lt_irrefl _ H).
rewrite Znat.inj_S.
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
induction (H0 _ H1).
induction p as (H2, H3).
induction x as (a0, b1).
exists ((a0 - a)%Z, b1).
split.
simpl in |- *.
apply H2.
cbv beta iota zeta delta [fst snd] in |- *.
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

Lemma gcd_lincomb_nat_dec :
 forall x y d : nat,
 x > 0 ->
 Pocklington.gcd.gcd (Z.of_nat x) (Z.of_nat y) d ->
 {a : Z * Z | Z.of_nat d = (Z.of_nat x * fst a + Z.of_nat y * snd a)%Z}.
Proof.
   unfold Pocklington.gcd.LinComb in |- *. intro x.
   apply (lt_wf_rec x). intros X IH. intros.
   elim (modulo X H y). intro z. 
   elim z.
   intros q r.
   clear z.
   simpl in |- *.   
   case r.

   (* case r = 0 *)

   intros.
   induction p as (H1, H2).
   rewrite <- plus_n_O in H1.
   exists (1%Z, 0%Z).
   replace (fst (1%Z, 0%Z)) with 1%Z.
   replace (snd (1%Z, 0%Z)) with 0%Z.
   rewrite <- Zmult_0_r_reverse. rewrite <- Zplus_0_r_reverse.
   rewrite Z.mul_comm. rewrite Zmult_1_l.
   apply Znat.inj_eq.
   apply (Pocklington.gcd.euclid_gcd d X (Z.of_nat y) (Z.of_nat X) (Z.of_nat q) 0).
   rewrite <- Zplus_0_r_reverse. rewrite <- Znat.inj_mult. apply Znat.inj_eq. assumption.
   apply Pocklington.gcd.gcd_sym. assumption. apply Pocklington.gcd.gcd_0_l. assumption.
   auto.
   auto.

   (* case r > 0 *)
   intro r1. intros.
   induction p as (H1, H2).
   elim (IH (S r1) H2 X d).
   intro z.
   elim z.
   intros delta gamma.
   clear z.
   replace (fst (delta, gamma)) with delta.
   replace (snd (delta, gamma)) with gamma.
   intros.
   exists ((gamma - Z.of_nat q * delta)%Z, delta).
   replace (fst ((gamma - Z.of_nat q * delta)%Z, delta)) with
    (gamma - Z.of_nat q * delta)%Z.
   replace (snd ((gamma - Z.of_nat q * delta)%Z, delta)) with delta.
   rewrite p. rewrite H1.
   unfold Zminus in |- *. rewrite Zmult_plus_distr_r.
   rewrite Znat.inj_plus. rewrite Zmult_plus_distr_l.
   rewrite Znat.inj_mult. rewrite <- Zopp_mult_distr_l_reverse.
   rewrite (Z.mul_assoc (Z.of_nat X)).
   rewrite (Z.mul_comm (Z.of_nat X) (- Z.of_nat q)).
   rewrite Zopp_mult_distr_l_reverse. rewrite Zopp_mult_distr_l_reverse.
   rewrite <- (Z.add_assoc (Z.of_nat X * gamma)).
   rewrite <- Znat.inj_mult.
   rewrite (Z.add_assoc (- (Z.of_nat (q * X) * delta))). 
   rewrite Zplus_opp_l. simpl in |- *. apply Z.add_comm.
auto.
auto.
auto.  
auto.
   apply gt_Sn_O.
   apply
    (Pocklington.gcd.euclid_gcd1 d (Z.of_nat y) (Z.of_nat X) (Z.of_nat q) (Z.of_nat (S r1))).
   apply Pocklington.gcd.gcd_sym. assumption.
   rewrite <- Znat.inj_mult. rewrite <- Znat.inj_plus. apply Znat.inj_eq. assumption.
Qed.

Lemma chineseRemainderTheoremHelp :
 forall x1 x2 : nat,
 CoPrime x1 x2 ->
 forall (a b : nat) (pa : a < x1) (pb : b < x2),
 a <= b ->
 {y : nat |
 y < x1 * x2 /\
 a = snd (proj1_sig (modulo x1 (ltgt1 _ _ pa) y)) /\
 b = snd (proj1_sig (modulo x2 (ltgt1 _ _ pb) y))}.
Proof.
intros.
unfold CoPrime in H.
induction (gcd_lincomb_nat_dec _ _ _ (ltgt1 _ _ pa) H).
induction x as (a0, b0).
set (A := Z.of_nat a) in *.
set (B := Z.of_nat b) in *.
set (X1 := Z.of_nat x1) in *.
set (X2 := Z.of_nat x2) in *.
set (y := (a0 * (B - A))%Z) in *.
set (z := (b0 * (A - B))%Z) in *.
set (d := (A + X1 * y)%Z) in *.
assert (d = (B + X2 * z)%Z).
unfold d in |- *.
simpl in p.
apply minus1 with (X2 * z)%Z.
rewrite (Zplus_comm B).
rewrite Zminus_plus.
unfold z in |- *.
replace (A - B)%Z with (- (B - A))%Z.
unfold Zminus in |- *.
rewrite (Z.mul_comm b0).
rewrite Zopp_mult_distr_l_reverse.
rewrite (Z.mul_comm X2).
rewrite Zopp_mult_distr_l_reverse.
rewrite Z.opp_involutive.
unfold y in |- *.
rewrite <- (Z.mul_assoc (B + - A)).
rewrite (Z.mul_comm (B + - A)).
rewrite (Z.mul_assoc X1).
rewrite (Z.mul_comm b0).
rewrite <- Z.add_assoc.
rewrite <- Zmult_plus_distr_l.
rewrite <- p.
rewrite Zmult_1_l.
fold (B - A)%Z in |- *.
apply Zplus_minus.
unfold Zminus in |- *.
rewrite Zopp_plus_distr.
rewrite Zplus_comm.
rewrite Z.opp_involutive.
reflexivity.
assert (x1 * x2 > 0).
replace 0 with (0 * x2).
unfold gt in |- *.
rewrite Nat.mul_comm.
rewrite (Nat.mul_comm x1).
induction x2 as [| x2 Hrecx2].
elim (lt_n_O _ pb).
apply mult_S_lt_compat_l.
fold (x1 > 0) in |- *.
eapply ltgt1.
apply pa.
auto.
induction (chRem1 _ H2 d).
induction p0 as (H3, H4).
induction x as (a1, b1).
exists b1.
split.
apply H3.
cbv beta iota zeta delta [snd fst] in H4.
cbv beta iota zeta delta [snd fst] in p.
split.
induction (modulo x1 (ltgt1 a x1 pa) b1).
induction x as (a2, b2).
simpl in |- *.
induction p0 as (H5, H6).
cbv beta iota zeta delta [snd fst] in H5.
rewrite H5 in H4.
unfold d in H4.
unfold A, X1 in H4.
apply Z_of_nat_inj. 
eapply chRem2.
replace 0%Z with (Z.of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z.of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply pa.
apply Znat.inj_lt.
apply H6.
rewrite Znat.inj_plus in H4.
repeat rewrite Znat.inj_mult in H4.
symmetry  in |- *.
rewrite (Zplus_comm (Z.of_nat a)) in H4.
rewrite Zplus_assoc in H4.
rewrite Z.mul_assoc in H4.
rewrite (Z.mul_comm a1) in H4.
rewrite <- (Z.mul_assoc (Z.of_nat x1)) in H4.
rewrite <- Zmult_plus_distr_r in H4.
rewrite (Z.mul_comm (Z.of_nat x1)) in H4.
apply H4.
induction (modulo x2 (ltgt1 b x2 pb) b1).
simpl in |- *.
induction x as (a2, b2).
cbv beta iota zeta delta [snd fst] in p0.
induction p0 as (H5, H6).
rewrite H5 in H4.
rewrite H1 in H4.
unfold B, X2 in H4.
apply Z_of_nat_inj. 
eapply chRem2.
replace 0%Z with (Z.of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
replace 0%Z with (Z.of_nat 0).
apply Znat.inj_le.
apply le_O_n.
auto.
apply Znat.inj_lt.
apply pb.
apply Znat.inj_lt.
apply H6.
rewrite Znat.inj_plus in H4.
repeat rewrite Znat.inj_mult in H4.
symmetry  in |- *.
rewrite (Zplus_comm (Z.of_nat b)) in H4.
rewrite Z.mul_assoc in H4.
rewrite Zplus_assoc in H4.
rewrite (Z.mul_comm a1) in H4.
rewrite (Z.mul_comm (Z.of_nat x2)) in H4.
rewrite <- Zmult_plus_distr_l in H4.
apply H4.
Qed.

Lemma chineseRemainderTheorem :
 forall x1 x2 : nat,
 CoPrime x1 x2 ->
 forall (a b : nat) (pa : a < x1) (pb : b < x2),
 {y : nat |
 y < x1 * x2 /\
 a = snd (proj1_sig (modulo x1 (ltgt1 _ _ pa) y)) /\
 b = snd (proj1_sig (modulo x2 (ltgt1 _ _ pb) y))}.
Proof.
intros.
induction (le_lt_dec a b).
apply chineseRemainderTheoremHelp.
assumption.
assumption.
assert (b <= a).
apply lt_le_weak.
assumption.
assert (CoPrime x2 x1).
apply coPrimeSym.
assumption.
induction (chineseRemainderTheoremHelp _ _ H1 b a pb pa H0).
induction p as (H2, H3).
induction H3 as (H3, H4).
exists x.
split.
rewrite Nat.mul_comm.
assumption.
split.
assumption.
assumption.
Qed.

Fixpoint prod (n:nat) (x: nat -> nat) :=
  match n with
    O => 1%nat
  | S p => x p * prod p x
  end.

Definition factorial (n : nat) : nat := prod n S.

Lemma coPrime1 : forall a : nat, CoPrime 1 a.
Proof.
  split.
  - split.
    + exists 1; trivial.
    + exists (Z.abs_nat (Z.of_nat a)); now rewrite mult_1_l.
  - intros e [H H0]; apply divide_le; [apply le_n| apply H].
Qed.

Lemma coPrimeMult3 (a b c: nat):
  a > 0 -> b > 0 -> c > 0 ->
  CoPrime a c -> CoPrime b c -> CoPrime (a * b) c.
Proof.
  intros H H0 H1 H2 H3;
    assert (H4: Pocklington.gcd.LinComb
                  (Z.of_nat 1) (Z.of_nat a) (Z.of_nat c)).
  { apply Pocklington.gcd.gcd_lincomb_nat.
    assumption.
    apply H2.
  }
  assert (H5:Pocklington.gcd.LinComb
               (Z.of_nat 1) (Z.of_nat b) (Z.of_nat c)).
  { apply Pocklington.gcd.gcd_lincomb_nat.
    assumption.
    apply H3.
  }
  destruct  H4 as [x [x0 H4]].
  destruct  H5 as [x1 [x2 H5]].
  split.
  - split.
    + exists (Z.abs_nat (Z.of_nat (a * b))).
      now rewrite Nat.mul_1_l.
    + exists (Z.abs_nat (Z.of_nat c)).
      now rewrite Nat.mul_1_l.
  - intros e [H6 H7].
    set (A := Z.of_nat a) in *.
    set (B := Z.of_nat b) in *.
    set (C := Z.of_nat c) in *.
    assert (H8:
             (1%Z =
                (A * B * (x * x1) +
                   C * (x0 * B * x1 + x2 * A * x + x0 * x2 * C))%Z)).
    {
      change  1%Z with (Z.of_nat 1 * Z.of_nat 1)%Z.
      rewrite H4 at 1.
      rewrite H5. 
      ring; reflexivity. 
    }
    assert (H9: divide e 1).
    { replace 1 with (Z.abs_nat 1).
      replace e with (Z.abs_nat (Z.of_nat e)).
      apply Pocklington.divides.zdivdiv.
      rewrite H8.
      apply Pocklington.divides.zdiv_plus_compat.
      apply Pocklington.divides.zdiv_mult_compat_l.
      apply Pocklington.divides.divzdiv.
      unfold A, B in |- *.
      rewrite <- Znat.inj_mult.
      rewrite Znat.Zabs2Nat.id.
      assumption.
      apply Pocklington.divides.zdiv_mult_compat_l.
      apply Pocklington.divides.divzdiv.
      now rewrite Znat.Zabs2Nat.id.
      apply  Znat.Zabs2Nat.id.
      reflexivity.
    }
    apply Pocklington.divides.div_le.
    apply Nat.lt_succ_diag_r.
    assumption.
Qed.

Require Import Arith. 

Search (0 < _ * _ )%nat.


Lemma prodBig1 :
 forall (n : nat) (x : nat -> nat),
 (forall z : nat, z < n -> x z > 0) -> prod n x > 0.
Proof.
intro.
induction n as [| n Hrecn].
intros.
simpl in |- *.
apply gt_Sn_n.
intros.
simpl in |- *.
apply Nat.mul_pos_pos.
apply H.
apply lt_n_Sn.
apply Hrecn.
intros.
apply H.
apply lt_S.
assumption.
Qed.

Lemma sameProd :
 forall (n : nat) (x1 x2 : nat -> nat),
 (forall z : nat, z < n -> x1 z = x2 z) -> prod n x1 = prod n x2.
Proof.
induction n as [| n Hrecn].
- intros; reflexivity. 
- intros x1 x2 H; simpl in |- *; replace (x1 n) with (x2 n).
  + f_equal; auto.
  + rewrite (H n); auto. 
Qed.

Lemma coPrimeProd :
 forall (n : nat) (x : nat -> nat),
 (forall z1 z2 : nat,
  z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
 (forall z : nat, z < S n -> x z > 0) -> CoPrime (prod n x) (x n).
Proof.
  induction n as [| n Hrecn].
  - intros; simpl in |- *; apply coPrime1.
  - intros x H H0.
    assert
      (H1: forall z1 z2 : nat,
          z1 < S n -> z2 < S n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
    { intros;apply H.
      1,2:  now apply Nat.lt_lt_succ_r.
      - assumption.
    }
    simpl in |- *; apply coPrimeMult3.
  + apply H0.
    apply Nat.lt_lt_succ_r.
    apply lt_n_Sn.
  + apply prodBig1.
    intros; apply H0.
    do 2 apply Nat.lt_lt_succ_r.
    assumption.
  + apply H0.
    apply lt_n_Sn.
  + apply H.
    apply Nat.lt_lt_succ_r.
    apply lt_n_Sn.
    apply lt_n_Sn.
    auto.
  + set
      (A1 :=
         fun a : nat =>
           match eq_nat_dec a n with
           | left _ => x (S n)
           | right _ => x a
           end) in *.
    assert (H2: CoPrime (prod n A1) (A1 n)).
    { apply Hrecn.
      intros.
      unfold A1 in |- *.
      induction (eq_nat_dec z1 n).
      + induction (eq_nat_dec z2 n).
        * elim H4.
          rewrite a0.
          assumption.
        * apply H.
          apply lt_n_Sn.
          apply Nat.lt_lt_succ_r.
          assumption.
          unfold not in |- *; intros.
          rewrite H5 in H3.
          elim (lt_irrefl _ H3).
      + induction (eq_nat_dec z2 n).
        * apply H.
          apply Nat.lt_lt_succ_r.
          assumption.
          apply lt_n_Sn.
          unfold not in |- *; intros.
          rewrite H5 in H2.
          elim (lt_irrefl _ H2).
        * apply H.
          apply Nat.lt_lt_succ_r.
          assumption.
          apply Nat.lt_lt_succ_r.
          assumption.
          assumption.
      + intros.
        unfold A1 in |- *.
        induction (eq_nat_dec z n).
        * apply H0.
          apply lt_n_Sn.
        * apply H0.
          apply Nat.lt_lt_succ_r.
          assumption.
    }
    auto.
    replace (x (S n)) with (A1 n).
    replace (prod n x) with (prod n A1).
    assumption.
    apply sameProd.
    intros.
    unfold A1 in |- *.
    induction (eq_nat_dec z n).
   * rewrite a in H3.
     elim (lt_irrefl _ H3).
   * reflexivity.
   * unfold A1 in |- *.
     induction (eq_nat_dec n n).
     -- reflexivity.
     -- elim b; reflexivity.
Qed.

Lemma divProd :
 forall (n : nat) (x : nat -> nat) (i : nat),
 i < n -> divide (x i) (prod n x).
Proof.
  induction n as [| n Hrecn].
  - intros x i H; destruct (lt_n_O _ H).
  - intros x i H; destruct (le_lt_or_eq i n).
     + now apply lt_n_Sm_le.
     + simpl in |- *.
      rewrite Nat.mul_comm.
      apply Pocklington.divides.div_mult_compat_l.
      now apply Hrecn.
    + simpl in |- *.
      apply Pocklington.divides.div_mult_compat_l.
      rewrite H0.
      apply Pocklington.divides.div_refl.
Qed.

Lemma chRem :
 forall (n : nat) (x : nat -> nat),
 (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)) ->
 forall (y : nat -> nat) (py : forall z : nat, z < n -> y z < x z),
 {a : nat |
 a < prod n x /\
 (forall (z : nat) (pz : z < n),
  y z = snd (proj1_sig (modulo (x z) (ltgt1 _ _ (py z pz)) a)))}. 
Proof.
  intro.
  induction n as [| n Hrecn].
  - intros; exists 0.
    split.
    + simpl in |- *.
      apply lt_O_Sn.
    + intros.
      elim (lt_n_O _ pz).
  - intros.
    assert
      (H0: forall z1 z2 : nat,
          z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
    { intros; apply H.
      apply Nat.lt_lt_succ_r.
      assumption.
      apply Nat.lt_lt_succ_r.
      assumption.
      assumption.
    }
    assert (H1: forall z : nat, z < n -> y z < x z).
    { intros.
      apply py.
      apply Nat.lt_lt_succ_r.
      assumption.
    }
    induction (Hrecn x H0 y H1).
    clear Hrecn; induction p as (H2, H3).
    assert (H4: CoPrime (prod n x) (x n)).
    { apply coPrimeProd.
      - apply H.
      - intros.
        eapply ltgt1.
        apply py.
        assumption.
    } assert (H5: y n < x n).
    { apply py.
      apply lt_n_Sn.
    }
    induction (chineseRemainderTheorem
                   (prod n x) (x n) H4 x0 (y n) H2 H5).
    exists x1; induction p as (H6, (H7, H8)).
    split.
    simpl in |- *.
    rewrite Nat.mul_comm.
    assumption.
    intros.
    induction (le_lt_or_eq z n).
    + assert
        (H10: y z =
                snd (proj1_sig (modulo (x z) (ltgt1 (y z) (x z)
                                                (H1 z H9)) x0)))
    by apply H3.
      induction (modulo (x z) (ltgt1 (y z) (x z) (H1 z H9)) x0).
      simpl in H10.
      induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
      simpl in |- *; rewrite H10.
      induction (modulo (prod n x) (ltgt1 x0 (prod n x) H2) x1).
      simpl in H7.
      rewrite H7 in p.
      induction p1 as (H11, H12).
      induction p as (H13, H14).
      induction p0 as (H15, H16).
      rewrite H13 in H11.
      apply uniqueRem with (x z) x1.
      apply (ltgt1 (y z) (x z) (py z pz)).
      assert (divide (x z) (prod n x)).
      { apply divProd.
        assumption.
      }
      induction H17 as (x5, H17).
      rewrite H17 in H11.
      rewrite (Nat.mul_comm (x z)) in H11.
      rewrite mult_assoc in H11.
      rewrite plus_assoc in H11.
      rewrite <- mult_plus_distr_r in H11.
      exists (fst x4 * x5 + fst x2).
      split.
      apply H11.
      assumption.
      exists (fst x3); auto.
    + induction (modulo (x z) (ltgt1 (y z) (x z) (py z pz)) x1).
      induction (modulo (x n) (ltgt1 (y n) (x n) H5) x1).
      simpl in H8.
      simpl in |- *.
      rewrite H9.
      rewrite H8.
      eapply uniqueRem.
      apply (ltgt1 (y n) (x n) H5).
      exists (fst x3).
      apply p0.
      exists (fst x2).
      rewrite H9 in p.
      assumption.
    + now apply lt_n_Sm_le.
Qed.

Lemma minusS : forall a b : nat, b - a = S b - S a.
Proof. lia. Qed.

Lemma primeDiv :
  forall a : nat, 1 < a ->
                  exists p : nat, Pocklington.prime.Prime p /\
                                    divide p a.
Proof.
  intro a; apply (lt_wf_ind a); clear a.
  intros n H H0; induction ( Pocklington.prime.primedec n).
  - exists n; split.
    + assumption.
    + exists 1; now rewrite Nat.mul_1_r.
  - induction (Pocklington.prime.nonprime_witness _ H0 H1).
    induction H2 as (H2, H3).
    induction H3 as (H3, H4).
    induction (H _ H3 H2).
    exists x0.
    induction H5 as (H5, H6).
    split.
    assumption.
    eapply  Pocklington.divides.div_trans.
    apply H6.
    assumption.
Qed.

Lemma coPrimePrime :
 forall a b : nat,
 (forall p : nat, Pocklington.prime.Prime p -> ~ divide p a \/ ~ divide p b) -> CoPrime a b.
Proof.
intros.
unfold CoPrime in |- *.
split.
split.
exists a.
rewrite mult_1_l.
apply Znat.Zabs2Nat.id.
exists b.
rewrite mult_1_l.
apply  Znat.Zabs2Nat.id.
intros.
induction H0 as (H0, H1).
rewrite  Znat.Zabs2Nat.id in H0.
rewrite  Znat.Zabs2Nat.id in H1.
induction (le_or_lt e 1).
assumption.
induction (primeDiv _ H2).
induction H3 as (H3, H4).
induction (H _ H3).
elim H5.
eapply Pocklington.divides.div_trans.
apply H4.
assumption.
elim H5.
eapply Pocklington.divides.div_trans.
apply H4.
assumption.
Qed.

Lemma coPrimeSeqHelp :
 forall c i j n : nat,
 divide (factorial n) c ->
 i < j -> i <= n -> j <= n -> CoPrime (S (c * S i)) (S (c * S j)).
Proof.
intros.
apply coPrimePrime.
intros.
induction (Pocklington.divides.divdec (S (c * S i)) p).
assert (~ divide p c).
unfold not in |- *.
intros.
assert (divide p 1).
eapply Pocklington.divides.div_plus_r.
apply Pocklington.divides.div_mult_compat_l.
apply H5.
rewrite plus_comm.
simpl in |- *.
apply H4.
induction H3 as (H3, H7).
elim (lt_not_le _ _ H3).
apply Pocklington.divides.div_le.
apply lt_n_Sn.
assumption.
induction (Pocklington.divides.divdec (S (c * S j)) p).
assert (divide p (c * (j - i))).
rewrite minusS.
rewrite Nat.mul_comm.
rewrite mult_minus_distr_r.
rewrite (Nat.mul_comm (S j)).
rewrite (Nat.mul_comm (S i)).
rewrite minusS.
apply Pocklington.divides.div_minus_compat.
assumption.
assumption.
induction (Pocklington.modprime.primedivmult _ _ _ H3 H7).
elim H5.
assumption.
assert (j - i <= n).
eapply le_trans.
apply Minus.le_minus.
assumption.
elim H5.
apply Pocklington.divides.div_trans with (factorial n).
apply Pocklington.divides.div_trans with (j - i).
assumption.
unfold factorial in |- *.
assert (1 <= j - i).
assert (j = i + (j - i)).
apply le_plus_minus.
apply lt_le_weak.
assumption.
rewrite H10 in H0.
apply lt_n_Sm_le.
apply lt_n_S.
apply plus_lt_reg_l with i.
rewrite plus_comm.
apply H0.
replace (j - i) with (S (pred (j - i))).
apply divProd.
rewrite pred_of_minus.
apply lt_S_n.
apply le_lt_n_Sm.
replace (S (j - i - 1)) with (1 + (j - i - 1)).
rewrite <- le_plus_minus.
assumption.
assumption.
auto.
induction (j - i).
elim (le_Sn_n _ H10).
rewrite <- pred_Sn.
reflexivity.
assumption.
auto.
auto.
Qed.

Definition coPrimeBeta (z c : nat) : nat := S (c * S z).

Lemma coPrimeSeq :
 forall c i j n : nat,
 divide (factorial n) c ->
 i <> j -> i <= n -> j <= n -> CoPrime (coPrimeBeta i c) (coPrimeBeta j c).
Proof.
unfold coPrimeBeta in |- *.
intros.
induction (nat_total_order _ _ H0).
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
apply coPrimeSym.
eapply coPrimeSeqHelp.
apply H.
assumption.
assumption.
assumption.
Qed.

Lemma gtBeta : forall z c : nat, coPrimeBeta z c > 0.
Proof.
unfold coPrimeBeta in |- *.
intros.
apply gt_Sn_O.
Qed.

Definition maxBeta (n : nat) (x : nat -> nat) : nat.
intros.
induction n as [| n Hrecn].
exact 0.
exact (max (x n) Hrecn).
Defined.

Lemma maxBetaLe :
 forall (n : nat) (x : nat -> nat) (i : nat), i < n -> x i <= maxBeta n x.
Proof.
simple induction n.
intros.
elim (lt_n_O _ H).
intros.
simpl in |- *.
induction (le_lt_or_eq i n0).
eapply le_trans.
apply H.
assumption.
apply le_max_r.
rewrite H1.
apply le_max_l.
apply lt_n_Sm_le.
assumption.
Qed.

Theorem divProd2 :
 forall (n : nat) (x : nat -> nat) (i : nat),
 i <= n -> divide (prod i x) (prod n x).
Proof.
simple induction n.
intros.
assert (0 = i).
apply le_n_O_eq.
assumption.
rewrite H0.
apply Pocklington.divides.div_refl.
intros.
induction (le_lt_or_eq i (S n0)).
simpl in |- *.
rewrite Nat.mul_comm.
apply Pocklington.divides.div_mult_compat_l.
apply H.
apply lt_n_Sm_le.
assumption.
rewrite H1.
apply Pocklington.divides.div_refl.
assumption.
Qed.

Theorem betaTheorem1 :
 forall (n : nat) (y : nat -> nat),
 {a : nat * nat |
 forall z : nat,
 z < n ->
 y z =
 snd (proj1_sig (modulo (coPrimeBeta z (snd a)) (gtBeta z (snd a)) (fst a)))}.
Proof.
intros.
set (c := factorial (max n (maxBeta n y))) in *.
set (x := fun z : nat => coPrimeBeta z c) in *.
assert
 (forall z1 z2 : nat, z1 < n -> z2 < n -> z1 <> z2 -> CoPrime (x z1) (x z2)).
intros.
unfold x in |- *.
eapply coPrimeSeq.
eapply Pocklington.divides.div_trans.
unfold factorial in |- *.
apply divProd2.
apply le_max_l.
unfold c, factorial in |- *.
apply Pocklington.divides.div_refl.
assumption.
apply lt_le_weak.
assumption.
apply lt_le_weak.
assumption.
assert (forall z : nat, z < n -> y z < x z).
intros.
unfold x, coPrimeBeta in |- *.
apply le_lt_n_Sm.
induction (mult_O_le c (S z)).
discriminate H1.
apply le_trans with c.
unfold c in |- *.
apply le_trans with (max n (maxBeta n y)).
apply le_trans with (maxBeta n y).
apply maxBetaLe.
assumption.
apply le_max_r.
generalize (max n (maxBeta n y)).
intros.
induction n0 as [| n0 Hrecn0].
simpl in |- *.
apply le_n_Sn.
induction n0 as [| n0 Hrecn1].
simpl in |- *.
apply le_n.
assert (factorial n0 > 0).
unfold factorial in |- *.
apply prodBig1.
intros.
apply gt_Sn_O.
simpl in |- *.
eapply le_trans with (1 + (1 + n0 * (factorial n0 + n0 * factorial n0))).
simpl in |- *.
repeat apply le_n_S.
induction (mult_O_le n0 (factorial n0 + n0 * factorial n0)).
unfold gt in H2.
assert (factorial n0 = factorial n0 + 0).
rewrite plus_comm.
auto.
assert (0 < factorial n0).
assumption.
rewrite H4 in H2.
set (A1 := factorial n0 + 0) in *.
rewrite <- H3 in H2.
unfold A1 in H2.
clear H4 A1.
assert (n0 * factorial n0 < 0).
eapply plus_lt_reg_l.
apply H2.
elim (lt_n_O _ H4).
rewrite Nat.mul_comm.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply plus_le_compat.
apply le_plus_trans.
apply lt_n_Sm_le.
apply lt_n_S.
assumption.
apply le_n.
rewrite Nat.mul_comm.
assumption.
induction (chRem _ _ H _ H0).
exists (x0, c).
intros.
induction p as (H2, H3).
rewrite (H3 z H1).
induction (modulo (x z) (ltgt1 (y z) (x z) (H0 z H1)) x0).
replace (snd (x0, c)) with c.
replace (fst (x0, c)) with x0.
induction (modulo (coPrimeBeta z c) (gtBeta z c) x0).
simpl in |- *.
eapply uniqueRem.
apply gtBeta.
unfold x in p.
exists (fst x1).
apply p.
exists (fst x2).
apply p0.
auto.
auto.
Qed.
