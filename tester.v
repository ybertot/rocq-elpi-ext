From Stdlib Require Import Reals Lra.
Import Ring_polynom.
From elpi.ext Require Import flipper.
Open Scope R_scope.
Definition RField_lemma5 :=
  Field_theory.Field_rw_pow_correct_w_gcd (Eqsth R) (Eq_ext Rplus Rmult Ropp)
  (@f_equal _ _ Rinv) (F2AF (Eqsth R) (Eq_ext _ _ _) Rfield) R_rm R_power_theory
  get_signZ_th (Ztriv_div_th Rset IZR).


Ltac compute_gcd D N :=
  constr:(pair 1%Z (pair (PX (Pc 2) 1 (Pc 0))
    (pair (Pc 1) (PX (Pc 1) 1 (Pc 0))))%Z).


Ltac compute_gcd' D N :=
gcd_for_field N D;
match goal with |- wrapped_result (?F, (?N',(?D', ?Gcd'))) -> _
=> intros _;
  constr:(pair F (pair N' (pair D' Gcd')))
    end.

Ltac den_gcd_n0 :=
  split;[ apply Rmult_integral_contrapositive; split;
    [apply not_eq_sym, Rlt_not_eq, Rlt_0_2 | ]| ]; apply PI_neq0.

Ltac find_fraction dummy :=
  let t_eq := fresh "term_eq" in
  let hyp := fresh "rewrite_lemma" in
  intros t_eq hyp;
  lazymatch type of t_eq with
  | ?term = _ =>
    clear t_eq;
    lazymatch type of hyp with
    | forall _ _ _ _,
      gcd_cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?FV ?D _ ?N _ _ -> _
      =>
    let D1 := eval vm_compute in D in
    let N1 := eval vm_compute in N in
    let hyp_aux := fresh "gcd_cond_proof" in
    let fact_n0 := fresh "factor_not_0" in
    let num_eq := fresh "equality_for_numerator" in
    let den_eq := fresh "equality_for_denumerator" in
      gcd_for_field N1 D1;
      lazymatch goal with
        |- wrapped_result (?F ,(?N2,(?D2, ?Gcd))) -> _
        => intros _;
        assert (fact_n0 : IZR F <> 0) by (apply eq_IZR_contrapositive; easy);
        enough (gcd_cond 0 1 Rplus Rmult Rminus Ropp eq 0%Z 1%Z Z.eqb IZR
          BinNat.N.to_nat
        pow get_signZ FV D D2 N N2 Gcd /\
          (Pmul 0%Z 1%Z Z.add Z.mul Z.eqb (Pc F) N =
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb N2 Gcd /\
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb (Pc F) D =
          Pmul 0%Z 1%Z Z.add Z.mul Z.eqb D2 Gcd)) as [hyp_aux [num_eq den_eq]];
        [
          generalize (hyp F N2 D2 Gcd hyp_aux fact_n0 num_eq den_eq);
          clear hyp_aux hyp fact_n0 num_eq den_eq;
          let hyp2 := fresh "rewrite_lemma2" in 
          intros hyp2;
          match type of hyp2 with
          | _ -> ?t = ?r =>
            change t with term in hyp2;
            (rewrite hyp2; clear hyp2);
            [ unfold display_pow_linear; reduce_Pphi_pow|
             cbv [PCond condition PEeval BinList.nth BinNat.N.to_nat
                  List.hd PosDef.Pos.to_nat Init.Nat.add PosDef.Pos.iter_op]]
          end
          |
          clear hyp fact_n0;
          split;       
           [split; 
            [
              match goal with 
              | |-  (_ -> _)  =>
              intros [? [? ?]]; easy
               | |- ?G  => try easy; intros [?[H H1]]; apply Z.eqb_eq in H1; unfold norm_subst in H; simpl in H; subst; easy
              end
            | reduce_Pphi_pow
            ] 
          | easy || fail 1000 "polynomial equalities should have been proved"]
       ]
        | |-?G => idtac G; fail 1000 "find_fraction fail"
      end
    end
  end.

Ltac fs5 := Field_simplify_gcd RField_lemma5 ltac:(find_fraction).

Lemma toto : PI / (PI ^ 2 + PI ^ 2) = 4 / 4 * PI.
(* find_fraction (). *)
field_simplify_gcd fs5  / (PI / (PI ^ 2 + PI ^ 2)).
Fail field_simplify_gcd fs5 / (4 / (4 * PI)).
admit.
admit.
enough (PI > 0) by lra.
apply PI_RGT_0.
split.
  lra.
  admit.
  Unshelve.
  compute.
Admitted.
 Lemma toto3 x : (3*x + 6 )/3 = x+2.
 field_simplify_gcd fs5  / ((3*x + 6 )/3).
easy.
Admitted.

Lemma toto4 x :(x + 2) /(3/3) = x + 2.
 field_simplify_gcd fs5  / ((x + 2) /(3/3)).
Admitted.
