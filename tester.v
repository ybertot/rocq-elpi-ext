From Stdlib Require Import Reals Lra.
Import Ring_polynom.
From elpi Require Import elpi ext.
From elpi.ext Require Import flipper.
Open Scope R_scope.

Section add_PI_knowledge.
Let PI_GT0 := PI_RGT_0.

Lemma happy_life : PI / (PI ^ 2 + PI ^ 2) = 4 / (8 * PI).
Proof.
field.
nra.
Qed.

Lemma field_unhappy : 1 + exp (PI / (PI ^ 2 + PI ^ 2)) =
  exp (4 / (8 * PI)) + 1.
Proof.
Fail field.
replace (PI / (PI ^ 2 + PI ^ 2)) with (4 / (8 * PI)) by (field; nra).
ring.
Qed.

Lemma ring_happy :
  exp (2 * PI + 1) = exp (1 + PI + PI).
Proof.
ring_simplify (2 * PI + 1) (1 + PI + PI); ring.
Qed.

Lemma field_still_unhappy :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
field_simplify (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
Fail easy.
  replace (PI/ (2 * PI ^ 2)) with (4 / (8 * PI)) by (field; nra).
  easy.
all: nra.
Qed.

Lemma field_solution :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
Fail field.
field_simplify' (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
easy.
all: nra.
Qed.

Lemma field_simplify_sandbox : cos (PI / 2) = cos (PI / 3 + PI / 6).
Proof.
field_simplify (PI / 3 + PI / 6).
Fail progress (field_simplify (9 * PI / 18)).
field_simplify' (9 * PI / 18);[ | nra ..].
easy.
Qed.

Lemma polynomial_division x : 0 < x -> 
  exp ((x ^  2 - /((4 - 1) / 3)) / (x + 1)) =
    2 * (exp (x - 1) / 3 + exp (x - 1) / 6).
Proof.
intros xgt0.
field_simplify' ((x ^ 2 - /((4 - 1)/3)) / (x + 1)).
field.
nra.
Qed.

Lemma in_cos_example : cos (2 * PI / 4) = cos (PI / 2).
Proof.
Fail progress field_simplify (2 * PI / 4) (PI / 2).
field_simplify' (2 * PI / 4) (PI / 2).
easy.
all:nra.
Qed.

End add_PI_knowledge.

Elpi Tactic test_sandbox.
From elpi.ext Extra Dependency "encode.elpi" as encode.

Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.


Elpi Query lp:{{
  sigma P R V1 V1' V2_rocq P1 R1\
  P = {{@PEadd Z (@PEpow Z (@PEadd Z (@PEc Z (-1)%Z) (@PEmul Z (@PEc Z 4%Z) (PEX Z 1)))
         (Npos 2)) (@PEmul Z (@PEc Z (-9)%Z) (@PEmul Z (PEX Z 2) (PEX Z 2)))
  }},
  R = {{Nnorm 19 nil lp:P}},
  coq.reduction.vm.norm R {{Pol Z}} V1,
  pol_encode V1 V1',
  expensive_id V1' V2,
  pe_decode V2 V2_rocq,
  P1 = {{@PEadd Z lp:P (@PEmul Z (PEc (-1)%Z) lp:V2_rocq)}},
  R1 = {{Nnorm 19 nil lp:P1}},
  coq.reduction.vm.norm R1 _ V3,
  V3 = {{@Pc Z 0%Z}}
}}.

Elpi Query lp:{{
  sigma P Q R T1 V1 T2 V2 V1_w V2_w M Gcd' Ne' De' Ne De Gcd LCMZ\
  P = {{@PEadd Z (@PEc Z (-1)%Z) (@PEmul Z (@PEc Z 4%Z) 
       (@PEpow Z (PEX Z 1) (Npos 2)))}},
  Q = {{@PEadd Z (@PEc Z 1%Z) (@PEmul Z (@PEc Z 2%Z)
        (PEX Z 1))}},
  R = {{Nnorm 19 nil lp:P}},
  coq.reduction.vm.norm R {{Pol Z}} V1,
  coq.reduction.vm.norm {{Nnorm 19 nil lp:Q}} {{Pol Z}} V2,
  pol_encode V1 V1_w,!,
  pol_encode V2 V2_w,
  gcd_poly V1_w V2_w M Gcd' Ne' De',
  pe_decode Ne' Ne,
  pe_decode De' De,
  pe_decode Gcd' Gcd,
  z_decode M LCMZ,
  coq.term->string Ne Nes,
  coq.term->string De Des,
  coq.term->string Gcd Gcds,
  coq.term->string LCMZ LCMs
  % gcd_and_factors pol_encode pe_decode V1 V2 A B C M
}}.

