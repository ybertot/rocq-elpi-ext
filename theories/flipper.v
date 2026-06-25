
From elpi Require Import elpi ext.
From elpi.ext Extra Dependency "encode.elpi" as encode.

From Stdlib Require Import Field Ring_polynom Reals.
Import List.

Elpi Command test.
Elpi Accumulate Plugin "ext.elpi".
Open Scope R_scope.
Parameter x : R.
Definition x1 := (x^5 + 4*x^3 + 5*x^2 + 3*x + 15).
Definition x2 := (x^4 - x^3 + 2*x^2 - 3*x - 3).
Notation "x + y" := (@FEadd Z x y).
Notation "x - y" := (@FEsub Z x y).
Notation "x * y" := (@FEmul Z x y).
Notation "`C[ n ]" := (@FEc Z n).
Notation "x ^ y" := (@FEpow Z x (Npos y%positive)).
Notation "`V[ n ]" := (@FEX Z (n%positive)).
Ltac foo z l :=
    let y := mkFieldexpr Z IZR_tac Rpow_tac  0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow z (l: list R) in
     assert (y = y).
Definition wrapper_F (x : FExpr Z) :=
True.
Definition wrapper_LR (x : list R) :=
True.

Definition Peeval' := @PEeval R 0 1 Rplus Rmult Rminus Ropp Z IZR nat BinNat.N.to_nat pow.
Definition Feeval' := @FEeval R 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv Z IZR nat BinNat.N.to_nat pow.
Elpi Accumulate File encode.
Elpi Query lp:{{
collect_glob_lcm {{`V[ 1] ^ 5 + `C[ 10%Z] * `V[ 1] ^ 3 + `C[ 5%Z] * `V[ 1] ^ 2 + `C[ 3%Z] * `V[ 1] + `C[ 15%Z]}} 1 X.
}}.

Definition wrapper_PolZ (x : Pol Z) :=
True.

Definition wrapped_result (t: Z *  (Pol Z * (Pol Z * Pol Z))) :=
True.

Definition norm := norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb.

Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [trm N, trm D] as G) GL :-
  gcd_and_factors pol_encode pe_decode N D N' D' Gcd LCM,
  coq.reduction.vm.norm {{norm lp:N'}} {{Pol Z}} N'',
  coq.reduction.vm.norm {{norm lp:D'}} {{Pol Z}} D'',
  coq.reduction.vm.norm {{norm lp:Gcd}} {{Pol Z}} Gcd',
  (refine {{_  (I : (wrapped_result (pair lp:LCM (pair lp:N'' (pair lp:D'' lp:Gcd')))))}} G GL).


solve (goal _ _ {{wrapper_LR lp:L -> wrapper_F lp:D ->
          wrapper_F lp:N -> _}} _ _ as G ) GL :-
  coq.say "second variant",
  gcd_and_factors fe_encode fe_decode N D N' D' Gcd LCM,
  (refine
  {{let H : (1%R/(IZR lp:LCM) *(Feeval' lp:L lp:N))%R = Feeval' lp:L (@FEmul Z lp:N' lp:Gcd) := _ in
  let H' : (1%R/(IZR lp:LCM) *(Feeval' lp:L lp:D))%R = Feeval' lp:L (@FEmul Z lp:D' lp:Gcd) := _ in _}}
  G GL)
.
}}.

Ltac gcd_for_field pol1 pol2 :=
  elpi factorize_by_gcd ltac_term:(pol1) ltac_term:(pol2);
  match goal with  |-
      wrapped_result (?Co, (?N',(?D', ?Gcd'))) ->_
 => idtac
 end.

Open Scope R_scope.

Ltac reify_then_call_factorize_by_gcd n d :=
let l := FFV IZR_tac Rpow_tac 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow n (nil(A:=R)) in
let l' := FFV IZR_tac Rpow_tac 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow d l in
    let n' := mkFieldexpr Z IZR_tac Rpow_tac  0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow n l' in
    let d' := mkFieldexpr Z IZR_tac Rpow_tac  0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow d l' in
    generalize (I:wrapper_F n');
    generalize  (I:wrapper_F d');
    generalize (I:wrapper_LR l');
    simpl BinNat.N.of_nat;
    lazymatch goal with
      |- wrapper_LR ?l'' -> wrapper_F ?d'' -> wrapper_F ?n'' -> _ =>
      (elpi factorize_by_gcd n'' d''); intros _ _ _
      end.
Close Scope R_scope.

Ltac consume_gcd pol1 pol2 :=
let v := (gcd_for_field pol1 pol2) in
let w := constr:(v) in
assert (w = w) by easy.


Print Pphi_pow.
Definition back_to_R := Pphi_pow 0%R 1%R Rplus Rmult Rminus Ropp
  0%Z 1%Z Z.eqb IZR BinNat.N.to_nat pow (fun _ => None).

(* TODO: find how to reduce Pphi_pow without reducing IZR. *)
Ltac reduce_Pphi_pow :=
    cbv [Pphi_pow Pphi_avoid mult_dev Peq Z.eqb P0 mkmult_c
        mkmult_c_pos get_signZ Pos.eqb mkmult_rec List.rev' add_pow_list
        mkmult1 List.rev_append List.hd BinNat.N.add
        add_mult_dev mkadd_mult mkmult_c_pos mkmult_rec BinNat.N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op List.rev' List.rev_append  List.hd List.tl add_pow_list mkmult_rec Pos.add Nat.add].

Check back_to_R.

Goal True.
gcd_for_field (PX (Pc (1%Z)) 2%positive (Pc (-1)%Z))
 (PX (Pc (1%Z)) 1%positive (Pc 1%Z)).
let in1 := constr:(PX (Pc (1%Z)) 2%positive (Pc (- 1)%Z)) in
  let v_in1 := constr:(back_to_R (PI::nil) in1) in
  generalize (eq_refl v_in1);
  unfold back_to_R.
reduce_Pphi_pow.
intros v_in1.
match goal with |- wrapped_result (_, (?out1, (?out2, ?gcd))) -> _ =>
  generalize (eq_refl (back_to_R (PI::nil) out1));
  unfold back_to_R;
  let name1 := fresh "out1" in
  reduce_Pphi_pow; intros name1
end.
let in2 := constr:(PX (Pc (1%Z)) 1%positive (Pc 1%Z)) in
  let v_in2 := constr:(back_to_R (PI::nil) in2) in
  generalize (eq_refl v_in2);
  unfold back_to_R.
reduce_Pphi_pow.
intros v_in2.
match goal with |- wrapped_result (_, (?out1, (?out2, ?gcd))) -> _ =>
  generalize (eq_refl (back_to_R (PI::nil) out2));
  unfold back_to_R;
  let name := fresh "out2" in
  reduce_Pphi_pow; intros name
end.

easy.
Qed.

Ltac simplify_by_gcd n d :=
  unshelve reify_then_call_factorize_by_gcd n d;
  cbv [Peeval' PEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add];
  try ring.

Goal True.
 simplify_by_gcd (PI^5 + 4* PI^3 + 5* PI^2 +3* PI + 15)%R (PI^4 - PI ^3 + 2 *PI^2 - 3 * PI -3)%R; cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add]; try field.

easy.
Qed.
Notation "x + y" := (@PEadd Z x y).
Notation "x - y" := (@PEsub Z x y).
Notation "x * y" := (@PEmul Z x y).
Notation "`C[ n ]" := (@PEc Z n).
Notation "x ^ y" := (@PEpow Z x (Npos y%positive)).
Notation " - y" := (@PEopp Z y ).
Notation "'x" := (@PEX Z 1%positive).
Notation "'y" := (@PEX Z 2%positive).
Notation "'z" := (@PEX Z 3%positive).

Definition p1 := 'x ^ 2 + (`C[ 3%Z ]) *'y ^ 3 - 'z .
Definition pol1 := norm p1.

Definition p2 := ('x ^ 2 + 'y) * (`C[ 3%Z ] *'y ^ 4 - 'x ^ 3).
Definition pol2 := norm p2.

Definition p3 := ('x ^ 3 + 'y) * ('y  - 'x ^ 3).
Definition pol3 := norm p3.

Definition p4 := (norm_subst 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb Z.quotrem ring_subst_niter nil
(PEadd (PEpow 'x (Npos 2)) (PEpow 'x (Npos 2)))).
Definition pol4 :=  PX (Pc 2%Z) 2 (Pc 0%Z).
Check pol4.
Definition p5 := (norm_subst 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb Z.quotrem ring_subst_niter nil('x)).
Definition pol5 := PX (Pc 1%Z) 1 (Pc 0%Z).
Elpi Accumulate File encode.

Goal True.
gcd_for_field (PX (Pc 2%Z) 2 (Pc 0%Z)) (PX (Pc 1%Z) 1 (Pc 0%Z)).
easy.
Qed.