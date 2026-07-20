From Stdlib Require Import Reals Lra.
Import Ring_polynom.
From elpi Require Import elpi ext.
From elpi.ext Require Import flipper.
Open Scope R_scope.

Lemma happy_life : PI / (PI ^ 2 + PI ^ 2) = 4 / (8 * PI).
Proof.
field.
enough (PI > 0) by nra.
apply PI_RGT_0.
Qed.

Lemma field_unhappy : 1 + exp (PI / (PI ^ 2 + PI ^ 2)) =
  exp (4 / (8 * PI)) + 1.
Proof.
Fail field.
assert (PI_GT0 := PI_RGT_0).
replace (PI / (PI ^ 2 + PI ^ 2)) with (4 / (8 * PI)) by (field; nra).
ring.
Qed.

Lemma field_still_unhappy :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
assert (PI_GT0 := PI_RGT_0).
field_simplify (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
Fail easy.
  replace (PI/ (2 * PI ^ 2)) with (4 / (8 * PI)) by (field; nra).
  easy.
all: nra.
Qed.

Lemma field_solution :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
assert (PI_GT0 := PI_RGT_0).
Fail field.
field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
easy.
all: nra.
Qed.

Lemma field_simplify_sandbox : cos (PI / 2) = cos (2 * (PI / 4)).
Proof.
field_simplify (2 * (PI / 4)).
field_simplify_gcd fs5 / (2 * PI / 4);[ | nra ..].
easy.
Qed.

Lemma polynomial_division x : 0 < x -> 
  exp ((x ^  2 - /((4 - 1) / 3)) / (x + 1)) = exp (x - 1).
Proof.
intros xgt0.
(* field_simplify (x ^ 2 - /((4 - 1)/3)). *)
field_simplify_gcd fs5 / ((x ^ 2 - /((4 - 1)/3)) / (x + 1)).
field.
nra.
Qed.

Elpi Tactic remove_trivial_non_zero.

Elpi Accumulate lp:{{
solve (goal _ _ _ _ _ as G) GL :-
  gcd_and_factors N D N' D' Gcd LCM,
  coq.reduction.vm.norm {{norm lp:N'}} {{Pol Z}} N'',
  coq.reduction.vm.norm {{norm lp:D'}} {{Pol Z}} D'',
  coq.reduction.vm.norm {{norm lp:Gcd}} {{Pol Z}} Gcd',
  (refine {{pair lp:LCM (pair lp:N'' (pair lp:D'' lp:Gcd'))}} G GL).
}}.

Elpi Tactic toto.
From elpi.ext Extra Dependency "encode.elpi" as encode.

Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.

Elpi Query lp:{{
  sigma P Q R V1 V2 T1 T2 V1_w V2_w Ne Ne' N' De De' D' Gcd' G' Gcd\
  P = {{@PEadd Z (@PEc Z (-1)%Z) (@PEmul Z (@PEc Z 4%Z) 
       (@PEpow Z (PEX Z 1) (Npos 2)))}},
  Q = {{@PEadd Z (@PEc Z 1%Z) (@PEmul Z (@PEc Z 2%Z)
        (PEX Z 1))}},
  R = {{Nnorm 19 nil lp:P}},
  coq.reduction.vm.norm R T1 V1,
  coq.reduction.vm.norm {{Nnorm 19 nil lp:Q}} T2 V2,
  pol_encode V1 V1_w,!,
  pol_encode V2 V2_w,
  gcd_poly V1_w V2_w Gcd Ne' De',
  collect_glob_lcm_poly Ne' 1 LCMN,
  collect_glob_lcm_poly De' 1 LCMD,
  collect_glob_lcm_poly Gcd 1 LCMG,
  lcm_int LCMN LCMD LCMND,
  multiply_if_gt_one Ne' LCMND N',
  multiply_if_gt_one De' LCMND D',
  multiply_if_gt_one Gcd LCMG G',
  pe_decode N' Ne,
  pe_decode D' De,
  pe_decode G' Gcd',
  LCM2 is LCMND * LCMG,
  z_decode LCM2 LCMZ,
  coq.term->string Ne Nes,
  coq.term->string De Des,
  coq.term->string Gcd' Gcds,
  coq.term->string LCMZ LCMs
  % gcd_and_factors pol_encode pe_decode V1 V2 A B C M
}}.

Elpi Query lp:{{
  pe_decode (mul (var 1) (var 1)) C,
  coq.term->string C S.
}}.
