(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype div ssrint ssrnum.
From mathcomp Require Import fintype ssralg ssrfun choice seq bigop intdiv.
From mathcomp Require Import finset finalg fingroup prime cyclic generic_quotient.
From mathcomp Require Import ssrnum poly polydiv.

Require Import polyall polydec polyfrac. 
Require Import freeg ec ecpoly eceval ecorder ecdiv ecgroup.
Require Import ecprojective endomorphism multiexponentiation.

Import GRing.Theory.
Import Num.Theory.
Import ProjPlane.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Section MultiexpoZ.
Variable G : zmodType.

Definition multiexpoGZ (w : nat) (n m : int) (P Q : G) : G :=
  let: (n, P) :=  match n with Posz n => (n, P) | Negz n => (n.+1, -P) end in
  let: (m, Q) :=  match m with Posz m => (m, Q) | Negz m => (m.+1, -Q) end in
  algoG G w (nat_to_bin n) (nat_to_bin m) P Q.

Lemma multiexpoGZ_correct w n m P Q : w != 0%N ->
  multiexpoGZ w n m P Q = P *~ n + Q *~ m.
Proof.
move=> nz_w; case: n m => [n|n] [m|m];
  rewrite /multiexpoGZ !(NegzE, =^~ pmulrn, =^~ nmulrn) -?mulNrn /=;
  by apply/algo_correct.
Qed.
End MultiexpoZ. 

(* -------------------------------------------------------------------- *)
Section multiexpo_projective.
(*Variable G : zmodType.*)
Variable K : finECUFieldType.
Variable E : ecuType K.

(* ================================================== *)


Lemma test: forall p :{ppoint K}, 
pponcurve E p = pponcurve E (popp p).
Proof.
elim/quotW; elim/ppind=> x y z nz_p //=. 
rewrite !piE /= /popp_r /popp_tr /pponcurve_r insubdK /=.
  by rewrite sqrrN.
by rewrite -topredE /= !xpair_eqE oppr_eq0.
Qed.

Lemma poppK: forall q :{ppoint K}, popp (popp q) = q.
Proof.
elim/quotW; elim/ppind=> x y z nz_p //=. 
rewrite piE /= /popp_r /popp_tr insubdK. 
  by rewrite opprK Point_insub.
by rewrite -topredE /= !xpair_eqE oppr_eq0.
Qed.

Lemma pponcurve_popp (p : ec_proj E): pponcurve E (popp p).
Proof. by case: p => [p Hp]; rewrite test /= poppK. Qed.

(* ================================================== *)

Lemma pponcurve_a2p: forall P, oncurve E P -> pponcurve E (a2p P).
Proof.
case=> [oncurve_inf |x y oncurve_p].
by rewrite /a2p pponcurve0.
by rewrite /a2p pponcurveP.
Qed.

Lemma tttest : forall q : {ppoint K}, ECGroup.neg (p2a (popp q)) = p2a q.
Proof.
elim/quotW; elim/ppind=> x y z nz_p //=; rewrite !piE.
rewrite /popp_r /p2a_r /= 2?ppvalK /=; last first.
  by rewrite oppr_eq0 orbF -!negb_and andbA.
by case: (z == 0) => //=; rewrite mulNr opprK.
Qed.

Lemma pponcurve_padd_ppoint: forall (p1 p2 : {ppoint K}), 
pponcurve E p1 -> pponcurve E p2 -> pponcurve E (padd E p1 p2).
Proof.
move=> p q Hp Hq.
move: (oncurve_p2a Hp)=> oncve_p.
move: (oncurve_p2a Hq)=> oncve_q.
have H_opp_q :  pponcurve E (popp q).
by rewrite -test.
move: (isomorph Hp H_opp_q).
rewrite poppK //=.
have HHq: ECGroup.neg (p2a (popp q)) = p2a q.
  by rewrite tttest.
rewrite HHq.
move: (ECGroup.addO E (p2a p) (p2a q)) => oncve_add.

move: (pponcurve_a2p oncve_add)=> HHH.
move=> Hl.
by rewrite Hl HHH.
Qed.


Lemma pponcurve_padd (p1 p2 : ec_proj E): pponcurve E (padd E p1 p2).
Proof. 
move: p1 => [p1 Hp1].
move: p2 => [p2 Hp2].
by rewrite pponcurve_padd_ppoint.
Qed.


(* ================================================== *)

Lemma isomorph_add : forall p q, 
pponcurve E p -> pponcurve E q -> 
padd E p q = a2p (ECGroup.add E (p2a p) (p2a q)).
Proof.
move=> p q pponcurve_p pponcurve_q.
move: (oncurve_p2a pponcurve_p)=> oncve_p.
move: (oncurve_p2a pponcurve_q)=> oncve_q.
have H_opp_q :  pponcurve E (popp q).
by rewrite -test.
move: (isomorph pponcurve_p H_opp_q).
rewrite poppK //=.
have HHq: ECGroup.neg (p2a (popp q)) = p2a q.
  by rewrite tttest.
by rewrite HHq.
Qed.

Lemma p2a_popp : forall p : {ppoint K}, 
p2a (popp p) =  ECGroup.neg (p2a p).
Proof.
elim/quotW; elim/ppind=> x y z nz_p //=; rewrite !piE.
rewrite /popp_r /p2a_r /= 2?ppvalK /=; last first.
  by rewrite oppr_eq0 orbF -!negb_and andbA.
by case: (z == 0) => //=;  rewrite mulNr. 
Qed.

Definition ecp_zero := EC_proj (pponcurve0 E).
Definition ecp_opp (p : ec_proj E) := EC_proj (pponcurve_popp p).
Definition ecp_add (p1 p2 : ec_proj E) := EC_proj (pponcurve_padd p1 p2).

Lemma ecpC : commutative ecp_add.
Proof.
case=> [p Ep] [q Eq]; apply/val_inj=> /=.
by rewrite !isomorph_add // ECGroup.addoC.
Qed.

Lemma ecp0e : left_id ecp_zero ecp_add.
Proof. 
case=> [p Ep]; apply/val_inj=> /=; rewrite isomorph_add ?pponcurve0 //.
rewrite !piE /p2a_r ppvalK /= ?(eqxx, oner_eq0) //=.
by rewrite ECGroup.add0o ?(@p2aK _ E) //; apply/oncurve_p2a.
Qed.

Lemma ecpNe : left_inverse ecp_zero ecp_opp ecp_add.
Proof. 
case=> [p Ep]; apply/val_inj=> /=; rewrite !isomorph_add -?test //.
by rewrite p2a_popp ECGroup.addNo.
Qed.

Lemma ecpA : associative ecp_add.
Proof.
case=> [p Ep] [q Eq] [r Er]; apply/val_inj=> /=.
rewrite !isomorph_add // ?pponcurve_a2p ?ECGroup.addO //.
rewrite !a2pK; pose o := EC (@ECGroup.zeroO _ E).
pose e x := insubd o (@p2a K x); have := @addeA_fin _ E.
move/(_ (e p) (e q) (e r))=> /(congr1 val) /=.
by rewrite {}/e /insubd !insubT ?oncurve_p2a //= => _ _ _ ->.
Qed.

Definition ecp_zmodMixin := ZmodMixin ecpA ecpC ecp0e ecpNe.
Canonical  ecp_zmodType := Eval hnf in ZmodType (ec_proj E) ecp_zmodMixin.

Lemma oncurve_a2p (p : point K): oncurve E p -> pponcurve E (a2p p).
Proof. by case: p => [|x y]; rewrite ?pponcurve0 -?pponcurveP. Qed.

Definition ec_p2a (p : ec_proj E) : ec E :=
  EC (oncurve_p2a (valP (sT := ec_proj_subType E) p)).

Definition ec_a2p (p : ec E) : ec_proj E :=
  EC_proj (oncurve_a2p (valP p)).
End multiexpo_projective.

(******************************************************************)
Section Final.
  Variable K : finECUFieldType.
  Variable E : ecuType K.
  Variable n : nat.

  Hypothesis prime_n : prime n.

  Variable phi : {additive (ec E) -> (ec E)}.

  Notation ntorsion := (torsion E n).

  Variable G : ntorsion.

  Hypothesis GNz : G != 0.

  Local Open Scope int_scope.

  Hypothesis divh: ~~ ( (n ^ 2)%:Z %| #|[set: ec E]|%:Z ).

  Notation l := (@phi2l K E n prime_n G GNz phi divh).

Lemma test_final (w k : nat) : l != 0%N -> w != 0%N ->
  multiexpoGZ w (decomp n l k).1 (decomp n l k).2
    (tgpoint G) (phi G) = G *+ k.
Proof.
case kE: (decomp _ _ _) => [k1 k2] /= nz_l nz_w.
rewrite (multiexpoGZ_correct _ _ (tgpoint G) (phi G) nz_w).
have := @correct_decomp n l k; rewrite kE /=.
have nz_n: n != 0%N by rewrite -lt0n prime_gt0.
move/(_ nz_n nz_l)/eqP; rewrite eqz_mod_dvd.
case/dvdzP=> [i] /eqP; rewrite subr_eq pmulrn => /eqP ->.
rewrite raddfMz /= !mulrzDl [k2*_]mulrC [i*_]mulrC.
rewrite !mulrzA (_ : tgpoint G *~ n = 0); last first.
  by rewrite -raddfMz -pmulrn (eqP (torsionE _)) raddf0.
rewrite mul0rz add0r; congr (_ + _); rewrite -pmulrn.
by rewrite -raddfMn (phi2lP prime_n (G := G)) /=.
Qed.
End Final.

Check test_final.
Print Assumptions test_final.