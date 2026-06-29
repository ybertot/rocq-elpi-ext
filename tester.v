From Stdlib Require Import Reals Lra.
Import Ring_polynom.
From elpi Require Import elpi ext.
From elpi.ext Require Import flipper.
Open Scope R_scope.
Definition RField_lemma5 :=
  Field_theory.Field_rw_pow_correct_w_gcd (Eqsth R) (Eq_ext Rplus Rmult Ropp)
  (@f_equal _ _ Rinv) (F2AF (Eqsth R) (Eq_ext _ _ _) Rfield) R_rm R_power_theory
  get_signZ_th (Ztriv_div_th Rset IZR).

Ltac find_fraction :=
  let t_eq := fresh "term_eq" in
  let hyp := fresh "rewrite_lemma" in
  intros t_eq hyp;
  lazymatch type of t_eq with
  | ?term = _ =>
    clear t_eq;
    idtac "in find_fraction" term;
    lazymatch type of hyp with
    | forall _ _ _ _,
      gcd_cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?FV ?D _ ?N _ _ -> _
      =>
    let D1 := eval vm_compute in D in
    let N1 := eval vm_compute in N in
    idtac "debug1" D1 N1;
    let hyp_aux := fresh "gcd_cond_proof" in
    let fact_n0 := fresh "factor_not_0" in
    let num_eq := fresh "equality_for_numerator" in
    let den_eq := fresh "equality_for_denumerator" in
      let res := constr:(ltac:(elpi factorize_by_gcd ltac_term:(N1) 
          ltac_term:(D1))) in
      idtac "debug5" res;
      let F := eval cbv [fst] in (fst res) in
      let N2 := eval cbv [fst snd] in (fst (snd res)) in
      let D2 := eval cbv [fst snd] in (fst (snd (snd res))) in
      let Gcd := eval cbv [snd fst] in (snd (snd (snd res))) in
        assert (fact_n0 : IZR F <> 0) by (apply eq_IZR_contrapositive; easy);
        enough (gcd_cond 0 1 Rplus Rmult Rminus Ropp eq 0%Z 1%Z Z.eqb IZR
          BinNat.N.to_nat
        pow get_signZ FV D D2 N N2 Gcd /\
          (Pmul 0%Z 1%Z Z.add Z.mul Z.eqb (Pc F) N =
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb N2 Gcd /\
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb (Pc F) D =
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb D2 Gcd)) as [hyp_aux [num_eq den_eq]];
        [ idtac "one goal";
          generalize (hyp F N2 D2 Gcd hyp_aux fact_n0 num_eq den_eq);
          clear hyp_aux hyp fact_n0 num_eq den_eq;
          let hyp2 := fresh "rewrite_lemma2" in 
          intros hyp2;
          match type of hyp2 with
          | _ -> ?t = ?r =>
            change t with term in hyp2;
            (rewrite hyp2; clear hyp2);
            [ unfold display_pow_linear; reduce_Pphi_pow|
             cbv [fst snd PCond condition PEeval BinList.nth BinNat.N.to_nat
                  List.hd PosDef.Pos.to_nat Init.Nat.add PosDef.Pos.iter_op]]
          end
          | idtac "other goal";
          clear hyp fact_n0;
          (split;       
           [split; 
            [
              match goal with 
              | |-  (_ -> _)  =>
              intros [? [? ?]]; easy
               | |- ?G  => try easy; intros [?[H H1]]; apply Z.eqb_eq in H1; unfold norm_subst in H; simpl in H; subst; try easy
              end
            | reduce_Pphi_pow
            ] 
          | easy || fail 1000 "polynomial equalities should have been proved"])
            || fail 1000 "failed to prove other goal"
       ]
    end
  end.

Ltac fs5 := Field_simplify_gcd RField_lemma5 ltac:(find_fraction).

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

field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2)) (4 / (8 * PI)).
Fail field.
field_simplify_gcd fs5 / (4 / (8 * PI)).
field.
all: try nra.
Qed.