
From elpi Require Import elpi ext.
From elpi.ext Extra Dependency "encode.elpi" as encode.

From Stdlib Require Import Field Ring_polynom Reals.
Import List.
Open Scope R_scope.

Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [trm N, trm D] as G) GL :-
  gcd_and_factors N D N' D' Gcd LCM,
  (refine {{(lp:LCM, (lp:N', (lp:D', lp:Gcd)))}} G GL).
}}.

Definition RField_lemma5 :=
  Field_theory.Field_rw_pow_correct_w_gcd (Eqsth R) (Eq_ext Rplus Rmult Ropp)
  (@f_equal _ _ Rinv) (F2AF (Eqsth R) (Eq_ext _ _ _) Rfield) R_rm R_power_theory
  get_signZ_th (Ztriv_div_th Rset IZR).

Definition Pmul := Pmul 0%Z 1%Z Z.add Z.mul Z.eqb.
Local Notation "x ?== y" := (Peq Z.eqb x y) (at level 70, no associativity).

Definition Nnorm :=
  norm_subst (0%Z) (1%Z) Z.add Z.mul Z.sub Z.opp Z.eqb Z.div_eucl.

(* TODO: find how to reduce Pphi_pow without reducing IZR. *)
Ltac reduce_Pphi_pow :=
  cbv [fst snd Pphi_pow Pphi_avoid mult_dev Peq Z.eqb P0 mkmult_c
      mkmult_c_pos get_signZ Pos.eqb mkmult_rec List.rev' add_pow_list
      mkmult1 List.rev_append List.hd BinNat.N.add
      add_mult_dev mkadd_mult mkmult_c_pos mkmult_rec BinNat.N.to_nat 
      PosDef.Pos.to_nat PosDef.Pos.iter_op List.rev' List.rev_append
      List.hd List.tl add_pow_list mkmult_rec Pos.add Nat.add
      display_pow_linear].

Ltac reduce_PCond :=
  cbv [fst snd PCond condition PEeval BinList.nth BinNat.N.to_nat
        List.hd PosDef.Pos.to_nat Init.Nat.add PosDef.Pos.iter_op
        BinList.jump List.tl].

(* Term is the expression that was given by the user for simplification.
  FV is the list of sub-expressions of Term that are not recognized as
  compound field expression (they are considered as variables).  D and N
  are two polynomials (in type Pol Z), such that
    Term = Pphi_pow FV  N / Pphi_pow FV D
  is already guaranteed,  but N / D is not a reduced fraction because these
  two polynomials ay have a non-trivial common divisor.
  This tactic also assume that the goal has approximately the shape :
  (forall m num' den' gcd, IZR m <> 0 ->
    <<Pc m * N = num' * gcd>> ->
    <<Pc m * D = den' * gcd>> ->  PCond <some list> ->
    FEeval _ .. _ fe = Pphi_pow N / Pphi_pow D) -> ...
  where the equalities between << >> are expressed in much longer
  form and FEeval _ .. _ FV fe is convertible with Term.  *)
Ltac fraction_finisher Term FV D N :=
let hyp := fresh "rewrite_lemma" in intros hyp;
let hyp2 := fresh "rew_l2" in
let D1 := eval vm_compute in D in
let N1 := eval vm_compute in N in
let res :=
  constr:(ltac:(elpi factorize_by_gcd ltac_term:(N1) ltac_term:(D1))) in
let F := eval cbv [fst] in (fst res) in
let N2 := eval cbv [fst snd] in (fst (snd res)) in
let D2 := eval cbv [fst snd] in (fst (snd (snd res))) in
let Gcd := eval cbv [snd fst] in (snd (snd (snd res))) in
assert (hyp2 := hyp F N2 D2 Gcd);
lazymatch type of hyp2 with
| _ -> _ -> _ -> _ -> ?t = ?r =>
change t with Term in hyp2;
  (try rewrite hyp2; clear hyp hyp2);
  [reduce_Pphi_pow | easy| easy | easy| reduce_PCond]
end.

Ltac fs5 := Field_simplify_gcd Nnorm RField_lemma5 ltac:(fraction_finisher).

(** field_simplify' formuula1 formula2 ...
  Simplify formulas according to field calculation laws.
  unlike field_simplify, this tactic does not take a list of hypotheses
  as argument.
  This version provides more simplified resulting formulas, since the
  these resulting formulas are *reduced* polynomial fractions. *)
Tactic Notation (at level 0) "field_simplify'" constr_list(rl) :=
  let G := Get_goal in
  field_lookup
    (PackField ltac:(Field_simplify_gcd Nnorm RField_lemma5 fraction_finisher))
    [] rl G.