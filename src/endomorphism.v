(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype div ssrint.
From mathcomp Require Import ssrnum fintype ssralg ssrfun choice seq.
From mathcomp Require Import bigop intdiv finset finalg fingroup prime cyclic.
From mathcomp Require Import poly polydiv.

Require Import polyall polydec polyfrac. 
Require Import freeg ec ecpoly eceval ecorder ecdiv ecgroup.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------- *)

Section Test.

  Variable gT: finGroupType.
  Variable n : nat.
  Import FinGroup.
  Open Local Scope group_scope.
  Open Local Scope int_scope.
  
  Lemma test : forall x y : gT, 
     #[x] = n -> #[y] = n -> commute <[x]> <[y]> ->
     x \notin <[y]> -> prime n -> ((n^2)%:Z %| #|[set: gT]%G|%:Z).
  Proof.
    move=> x y order_x order_y commute_xy x_notin_y prime_n.
    have eq1_xIy: <[x]> :&: <[y]> = 1.
    apply/prime_TIg; first by rewrite -fingroup.orderE order_x.
      by apply/subsetPn; exists x; rewrite ?cycle_id.
    have := Lagrange (H := <[x]> * <[y]>) (subsetT _).
      move: (mul_cardG <[x]> <[y]>); rewrite eq1_xIy.
      rewrite cards1 muln1 /= comm_joingE; last first.
      by apply: commute_xy.
    move=> <- <-; rewrite -!fingroup.orderE order_x order_y mulnn. 
    by apply: dvdn_mulr; rewrite absz_nat.
  Qed.
  
End Test.

(* -------------------------------------------------------------- *)
Section Torsion.
  Variable K : finECUFieldType.
  Variable E : ecuType K.
  Variable n : nat.

  (* n-torsion points are points on the curve s.t. [n]p = 0 *)
  Record torsion := Torsion { tgpoint :> ec E; _ : tgpoint *+ n == 0 }.

  Canonical torsion_subType := Eval hnf in [subType for tgpoint].

  Definition torsion_eqMixin := Eval hnf in [eqMixin of torsion by <:].
  Canonical torsion_eqType := Eval hnf in EqType torsion torsion_eqMixin.

  Definition torsion_choiceMixin := [choiceMixin of torsion by <:].
  Canonical torsion_choiceType := Eval hnf in ChoiceType torsion torsion_choiceMixin.

  Definition torsion_countMixin := [countMixin of torsion by <:].
  Canonical torsion_countType := Eval hnf in CountType torsion torsion_countMixin.
  Canonical torsion_subCountType := Eval hnf in [subCountType of torsion].

  Definition torsion_finMixin := [finMixin of torsion by <:].
  Canonical torsion_finType := Eval hnf in FinType torsion torsion_finMixin.

  Lemma torsion_inj : injective tgpoint.
  Proof. exact: val_inj. Qed.

  Definition torsion_of of (phant (ec E)) := torsion.
  Identity Coercion type_torsion_of : torsion_of >-> torsion.

  (* the point at infinity as element of the torsion group *)
  Definition tg0 := @Torsion 0 (introT eqP (mul0rn _ n)).

  Lemma tgadd_interne (x y : torsion): ((x : ec E) + y) *+ n == 0.
  Proof.
    case: x y => [x z_xn] [y z_yn] /=; rewrite mulrnDl.
    by rewrite (eqP z_xn) (eqP z_yn) addr0.
  Qed.

  Definition tgadd (x y : torsion) : torsion := Torsion (tgadd_interne x y).

  Lemma tgopp_interne (x : torsion): (- (x : ec _)) *+ n == 0.
  Proof. by case: x => [x z_xn] /=; rewrite mulNrn (eqP z_xn) oppr0. Qed.

  Definition tgopp (x : torsion) : torsion := Torsion (tgopp_interne x).

  Lemma tgaddE (x y : torsion): tgadd x y = (x : ec _) + y :> ec E.
  Proof. by []. Qed.

  Lemma tgaddC: commutative tgadd.
  Proof. by move=> x y; apply/eqP; rewrite eqE /= addrC. Qed.

  Lemma tgaddA: associative tgadd.
  Proof. by move=> x y z; apply/eqP; rewrite eqE /= addrA. Qed.

  Lemma tgadd0c: left_id tg0 tgadd.
  Proof. by move=> x; apply/eqP; rewrite eqE /= add0r. Qed.

  Lemma tgaddNc: left_inverse tg0 tgopp tgadd.
  Proof. by move=> x; apply /eqP; rewrite eqE /= addNr. Qed.

  Definition tg_zmodMixin := ZmodMixin tgaddA tgaddC tgadd0c tgaddNc.
  Canonical tg_zmodType  := Eval hnf in ZmodType torsion tg_zmodMixin.  

  Lemma tgpoint_additive: additive tgpoint.
  Proof. by []. Qed.

  Canonical tgpoint_is_additive := Additive tgpoint_additive.
End Torsion.

(* -------------------------------------------------------------- *)
Section FirstPart.
  Variable K : finECUFieldType.
  Variable E : ecuType K.
  Variable n : nat.

  Hypothesis prime_n : prime n.

  Notation ntorsion := (torsion E n).

  Variable G : ntorsion.
  Hypothesis GNz : G != 0.

  Variable phi : {additive (ec E) -> (ec E)}.

  Open Local Scope int_scope.

  Hypothesis foo: ~~ ( (n ^ 2)%:Z %| #|[set: ec E]|%:Z ).

(* -------------------------------------------------------------- *)
(*        3 lemmas about torsion points to use afterwards         *)
(* -------------------------------------------------------------- *)

  Lemma torsionE : 
    forall R : ntorsion,  R *+ n == 0.
  Proof. 
    case=> R ntorsionR; by rewrite eqE /=raddfMn /=.
  Qed.

  Lemma torsionX (P : ntorsion) (k : nat):
 (tgpoint P ^+ k)%g = P *+ k.
  Proof.
    elim: k => [|k IH].
    + rewrite //=.
    + rewrite expgS IH mulrS //=.
  Qed.

  Lemma tgpointSc (P : ntorsion) (k : nat): 
    (tgpoint P) *+ k = tgpoint (P *+ k).
  Proof.
    elim: k => [|k IH].
    + rewrite //=.
    + rewrite !mulrS IH //.
  Qed.


(*=============================================================*)  
(*         First Part                                          *)
(*=============================================================*)  
  
(* <G> = {Pinf, G, [2]G, ..., [n-1]G},  G generateur d'ordre n  *)
(* <G> sousensemble de ntorsion  //  premiere inclusion         *)
(* ntorsion sousensemble de <G>  //  deuxieme inclusion         *)
(* sous condition que     n^2 ne divise pas #|E|                *)

  Lemma premiere_inclusion : 
    forall r : nat, 
      (G *+ r) *+ n = 0.
  Proof.
    by move=> r; rewrite mulrnAC (eqP (torsionE G)) mul0rn.
  Qed.

  Lemma order_torsion : 
    forall P : ntorsion, 
      P != 0 -> #[tgpoint P]%g = n.
  Proof.
    move=> P PnZ; apply: nt_prime_order => //. 
    move/eqP: (torsionE P) => P_ntorsion.
    by rewrite torsionX P_ntorsion.
  Qed.

  Lemma commute_cycles : 
    forall (A B : ntorsion), commute <[tgpoint A]> <[tgpoint B]>. 
  Proof.
  have h (A B : ntorsion) x :
  x \in (<[tgpoint A]> * <[tgpoint B]>)%g -> 
        x \in (<[tgpoint B]> * <[tgpoint A]>)%g.
  + case/mulsgP=> /= xA xB hA hB ->; suff ->: (xA * xB = xB * xA)%g.
    by apply/mem_mulg. by rewrite /mulg /= addrC.
  by move=> A B; apply/setP=> x; apply/idP/idP; apply/h.
  Qed.

  Lemma deuxieme_inclusion: 
    forall Q : ntorsion, 
      tgpoint Q \in <[tgpoint G]>%g.
  Proof.
    move : (order_torsion GNz)=> order_G. 
    move=> Q.
    case Qz: (Q==0); last first.
    + move/negbT: Qz=> Qz.
      move: (order_torsion Qz)=> order_Q.
      move: (commute_cycles Q G) => commute_QG.
      move: (test order_Q order_G commute_QG)=> useful.
      case h : (tgpoint Q \in <[tgpoint G]>%g)=> //.
      move: useful; rewrite h prime_n //=.
      move=> H; move: foo; by rewrite H.
    + rewrite (eqP Qz); apply/cycleP.
      exists 0%N; by rewrite expg0.
  Qed.

(*=============================================================*)  
(*        Second Part                                          *)
(*=============================================================*)  


  Lemma phi_torsion_restriction :
    forall (n : nat) (P : ec E), 
      P *+ n = 0 -> phi (P *+ n) = 0.
  Proof.
    by move=> k P ->; rewrite raddf0.
  Qed.


  Lemma tgphi_interne (P : ntorsion):
  (phi (tgpoint P)) *+ n == 0.
  Proof.
  move/eqP: (torsionE P)=> ntorsion_P.
  by rewrite -raddfMn /= tgpointSc ntorsion_P raddf0.
  Qed.


  Definition tgphi (P : ntorsion) : ntorsion := 
  Torsion (tgphi_interne P).

  Lemma ok_def_tgphi (P : ntorsion) :
  tgpoint (tgphi P) == phi (tgpoint P).
  Proof. done. Qed.

  Lemma final: { m : nat | forall Q : ntorsion, phi Q = Q *+ m }.
  Proof.
    have phiG_ntorsion : exists l, phi G == G *+ l.
    + move/cycleP: (deuxieme_inclusion (tgphi G)).
      case=> l; rewrite torsionX; move=> HG.
      by exists l; move: (ok_def_tgphi G); rewrite HG eq_sym.
    exists (xchoose phiG_ntorsion).
    have := xchooseP phiG_ntorsion; move: (xchoose _).
    move=> l /eqP phiG_lG Q.
    have h: exists i, (tgpoint Q == ((tgpoint G) *+ i)%g).
      by case/cycleP: (deuxieme_inclusion Q)=> i ->; exists i.
    have /eqP := xchooseP h; move: (xchoose h)=> {h} q Q_qG.
    rewrite Q_qG; have h :  phi (G *+ q) =  (phi G) *+ q.
    + by rewrite -raddfMn tgpointSc.
    by rewrite -raddfMn h phiG_lG -!tgpointSc Q_qG mulrnAC.
  Qed.

  (* The l s.t. phi Q = Q *+ l *)
  Definition phi2l := tag final.

  Lemma phi2lP (Q : ntorsion): phi Q = Q *+ phi2l.
  Proof. by move: Q; apply/(tagged final). Qed.
End FirstPart.
