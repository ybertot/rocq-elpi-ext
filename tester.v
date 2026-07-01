From Stdlib Require Import Reals Lra.
Import Ring_polynom.
From elpi Require Import elpi ext.
From elpi.ext Require Import flipper.
Open Scope R_scope.
Definition RField_lemma5 :=
  Field_theory.Field_rw_pow_correct_w_gcd (Eqsth R) (Eq_ext Rplus Rmult Ropp)
  (@f_equal _ _ Rinv) (F2AF (Eqsth R) (Eq_ext _ _ _) Rfield) R_rm R_power_theory
  get_signZ_th (Ztriv_div_th Rset IZR).

Definition Pmul := Pmul 0%Z 1%Z Z.add Z.mul Z.eqb.

(* Term is the expression that was given by the user for simplification.
  FV is the list of sub-expressions of Term that are not recognized as
  compound field expression (they are considered as variables).  D and N
  are two polynomials (in type Pol Z), such that Term = N / D is already
  proved,  but N / D is not a reduced fraction because these two polynomials
  may have a non-trivial common divisor.
  This tactic also assume that the goal has approximately the shape :
  forall nfe, Fnorm FV fe = nfe ->  <some conditions> ->
    FEeval _ .. _ fe -> Pphi_pow N / Pphi_pow D
  where FEeval _ .. _ fe is convertible with Term.  *)
Ltac find_fraction Term FV D N :=
  let hyp := fresh "rewrite_lemma" in
  intros hyp;
  let D1 := eval vm_compute in D in
  let N1 := eval vm_compute in N in
  let hyp_aux := fresh "gcd_cond_proof" in
  let fact_n0 := fresh "factor_not_0" in
  let num_eq := fresh "equality_for_numerator" in
  let den_eq := fresh "equality_for_denumerator" in
  let res :=
    constr:(ltac:(elpi factorize_by_gcd ltac_term:(N1) ltac_term:(D1))) in
  let F := eval cbv [fst] in (fst res) in
  let N2 := eval cbv [fst snd] in (fst (snd res)) in
  let D2 := eval cbv [fst snd] in (fst (snd (snd res))) in
  let Gcd := eval cbv [snd fst] in (snd (snd (snd res))) in
  assert (fact_n0 : IZR F <> 0) by (apply eq_IZR_contrapositive; easy);
  enough (gcd_cond 0 1 Rplus Rmult Rminus Ropp eq 0%Z 1%Z Z.eqb IZR
    BinNat.N.to_nat
  pow get_signZ FV D D2 N N2 Gcd /\ (Peq Z.eqb (Pmul (Pc F) N) (Pmul N2 Gcd) = true
    /\
    Peq Z.eqb (Pmul (Pc F) D) (Pmul D2 Gcd) = true)) as [hyp_aux [num_eq den_eq]];
    [let hyp2 := fresh "rewrite_lemma2" in
    (assert (hyp2 := hyp F N2 D2 Gcd hyp_aux fact_n0 num_eq den_eq)
      || idtac "assert failed");
    clear hyp_aux hyp fact_n0 num_eq den_eq;
    match type of hyp2 with
    | _ -> ?t = _ =>
      change t with Term in hyp2;
      (rewrite hyp2; clear hyp2);
      [ unfold display_pow_linear; reduce_Pphi_pow|
        cbv [fst snd PCond condition PEeval BinList.nth BinNat.N.to_nat
            List.hd PosDef.Pos.to_nat Init.Nat.add PosDef.Pos.iter_op]]
    end
    |clear hyp fact_n0;
    (split;[ unfold gcd_cond; reduce_Pphi_pow
    | easy || fail 1000 "the oracle returned wrong polynomials"])
      || fail 1000 "failed to prove other goal"
  ].


Definition Nnorm :=
  norm_subst (0%Z) (1%Z) Z.add Z.mul Z.sub Z.opp Z.eqb Z.div_eucl.

Ltac fs5 := Field_simplify_gcd Nnorm RField_lemma5 ltac:(find_fraction).

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
Abort.

Lemma ring_happy : 1+ exp (PI ^ 2 - 1) = exp ((PI + 1) * (PI - 1)) + 1.
Proof.
ring_simplify (PI ^ 2 - 1) ((PI + 1) * (PI - 1)).
ring.
Qed.

Lemma field_still_unhappy :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
assert (PI_GT0 := PI_RGT_0).
field_simplify (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
Abort.

Lemma field_solution :
  exp (PI / (PI ^ 2 + PI ^ 2)) = exp (4 / (8 * PI)).
Proof.
assert (PI_GT0 := PI_RGT_0).
Fail field.
field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
easy.
nra.
nra.
nra.
nra.
Qed.
