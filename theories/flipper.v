
From elpi Require Import elpi ext.
From elpi.ext Extra Dependency "encode.elpi" as encode.

From Stdlib Require Import Field Ring_polynom Reals.

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
Definition wrapper_PolZ (x : Pol Z) :=
True.
Definition wrapped_result (t: Z * (PExpr Z * (PExpr Z * PExpr Z))) :=
True.

Goal True.
unshelve (epose (x:= _ :nat)).
exact 7%nat.
easy.
Qed.

Definition Peeval' := @PEeval R 0 1 Rplus Rmult Rminus Ropp Z IZR nat BinNat.N.to_nat pow.
Definition Feeval' := @FEeval R 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv Z IZR nat BinNat.N.to_nat pow.

Ltac normalize_Feeval :=
cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat
PosDef.Pos.iter_op Init.Nat.add].

Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.
Elpi Accumulate lp:{{
solve _ _ :-
coq.say "fac by gcd called",fail.

solve (goal _ _ {{wrapper_LR lp:L -> wrapper_F lp:D -> wrapper_F lp:N -> _}} _ _ as G ) GL :-
coq.say "fac by gcd called with 3 arguments",

  fe_encode N Nx,
  fe_encode D Dx,
  factorize_poly Nx Dx Ne' De',
  gcd_poly Nx Dx Gcd',
  coq.say "Nx ===" Nx,
  coq.say "Dx ===" Dx,
  coq.say "Ne' De' ==="  Ne' "---" De',
  coq.say "Gcd === " Gcd',
  collect_glob_lcm_poly Gcd' 1 LCM_G,
  collect_glob_lcm_poly Ne' 1 LCM_N,
  collect_glob_lcm_poly De' 1 LCM_D,
  LCM_product is LCM_G * LCM_N * LCM_D,
  ND_factor is LCM_N * LCM_D,

  if (LCM_product > 1) 
    % then
  (multiply_lcm_poly Ne' ND_factor Ne,
  multiply_lcm_poly De' ND_factor De,
  multiply_lcm_poly Gcd' LCM_G Gcd)
    %else
     (Ne = Ne', De = De', Gcd = Gcd'),
  % endif
  fe_decode Ne N_final,
  fe_decode De D_final,
  fe_decode Gcd Gcd_final,
  z_decode LCM_product Co,

coq.say "debug yves" LCM_G,
std.assert-ok! (coq.typecheck {{ ((IZR lp:Co) * (Feeval' lp:L lp:D))%R = 
           Feeval' lp:L (@FEmul Z lp:D_final lp:Gcd_final) }} _)
  "typecheck product for numerator failed",
if (LCM_product > 1)
  (
    refine {{(_ : (IZR lp:Co * (Feeval' lp:L lp:N))%R = 
                  Feeval' lp:L (@FEmul Z lp:N_final lp:Gcd_final) ->
                  ((IZR lp:Co) * (Feeval' lp:L lp:D))%R = 
                  Feeval' lp:L (@FEmul Z lp:D_final lp:Gcd_final)  -> _) _ _}}
  % {{(_ :(IZR lp:Co *
  %   (Feeval' lp:L lp:N))%R = Feeval' lp:L (@FEmul Z lp:N_final lp:Gcd_final) ->
  %   (1%R/(IZR lp:Co) *(Feeval' lp:L lp:D))%R = 
  %   Feeval' lp:L (@FEmul Z lp:D_final lp:Gcd_final) -> _) _}}
  G GL)
  (refine 
    {{(_ : (Feeval' lp:L lp:N) = Feeval' lp:L (@FEmul Z lp:N_final lp:Gcd_final) -> 
      (Feeval' lp:L lp:D) = Feeval' lp:L (@FEmul Z lp:D_final lp:Gcd_final) -> _) _ _}}
  % {{let H : (Feeval' lp:L lp:N) = Feeval' lp:L (@FEmul Z lp:N' lp:Gcd') := _ in 
  % let H' : (Feeval' lp:L lp:D) = Feeval' lp:L (@FEmul Z lp:D' lp:Gcd') := _ in _}}
  G GL).

solve (goal _ _ {{wrapper_PolZ lp:Pol2 -> wrapper_PolZ lp:Pol1 -> _ }}
 _ _  as G) GL :-
  coq.say "fac by gcd called with 2 arguments",
  pol_encode Pol1 Nx,
  coq.say "Nx ===" Nx,
  pol_encode Pol2 Dx,
  coq.say "pol_encode passed",
  collect_glob_lcm_poly (add Nx Dx) 1 LCM,
  if (LCM > 1) 
  (multiply_lcm_poly Nx LCM Ne,
  multiply_lcm_poly Dx LCM De) (Ne = Nx, De = Dx),
  gcd_poly Ne De Gcd,
    coq.say "gcd_poly passed",

  factorize_poly Ne De Ne' De',
  coq.say "ok",
  normalize_after_fac Ne' De' Ne'' De'',
  coq.say " fac passed",
  coq.say "Ne'' ===" Ne'',
  pe_decode Ne'' N',
  pe_decode De'' D',
    coq.say "pe_decode passed",

  pe_decode Gcd Gcd',
  z_decode LCM Co,
  coq.say "and here" Cp,
  (refine 
  {{_  (I : (wrapped_result (pair lp:Co (pair lp:N' (pair lp:D' lp:Gcd')))))}}
  G GL),
  coq.say "success refine with " Co N' D' Gcd'.
}}.

Ltac gcd_for_field pol1 pol2 :=
  generalize (I:wrapper_PolZ pol1);
  generalize (I:wrapper_PolZ pol2);
   match goal with  |- 
      wrapper_PolZ  ?pol1' -> wrapper_PolZ ?pol2' -> _ =>
  elpi factorize_by_gcd; 
  let tmp_name := fresh "Gcd_var" in intros tmp_name _ _;
  revert tmp_name;
  match goal with  |- 
      wrapped_result (?Co, (?N',(?D', ?Gcd'))) ->_ 
 => idtac
 end
 end.


Open Scope R_scope.

Ltac foo1 n d :=
let l := FFV IZR_tac Rpow_tac 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow n (nil(A:=R)) in
let l' := FFV IZR_tac Rpow_tac 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow d l in
    let n' := mkFieldexpr Z IZR_tac Rpow_tac  0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow n l' in
    let d' := mkFieldexpr Z IZR_tac Rpow_tac  0 1 Rplus Rmult Rminus Ropp Rdiv Rinv pow d l' in
    generalize (I:wrapper_F n');
    generalize  (I:wrapper_F d');
    generalize (I:wrapper_LR l');
    simpl BinNat.N.of_nat;
      let name1 := fresh "foo1_tmp" in
      let name2 := fresh "foo1_tmp" in
      idtac "hello";(elpi factorize_by_gcd n'' d'');
        normalize_Feeval;
        [intros name1 name2 _ _ _; revert name1 name2 | | ].

Close Scope R_scope.

Ltac consume_gcd pol1 pol2 :=
let v := (gcd_for_field pol1 pol2) in
let w := constr:(v) in
assert (w = w) by easy.

Ltac simplify_by_gcd n d :=
 unshelve foo1 n d;
  cbv [Peeval' PEeval BinList.nth BinNat.N.to_nat List.hd 
  PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add].

Goal True.  (* failing test *)
simplify_by_gcd (2 * PI ^ 2 + 4)%R 
  (4 * PI ^ 3 - 4 * PI ^ 2 + 8 * PI - 8)%R.
2,3: ring.

Qed.

Goal True. 
  simplify_by_gcd (PI^5 + 4* PI^3 + 5* PI^2 +3* PI + 15)%R
     (PI^4 - PI ^3 + 2 *PI^2 - 3 * PI -3)%R.
2,3: ring.

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
Definition norm := norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb.

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

Elpi Query lp:{{
  % coq.reduction.vm.norm {{pol1}} _ X1,
  % pol_encode X1 Pol1,
  % pe_decode Pol1 P1,
  % coq.term->string P1 PS1,
  % coq.reduction.vm.norm {{pol2}} _ X2,
  % pol_encode X2 Pol2,
  % pe_decode Pol2 P2,
  % coq.term->string P2 PS2,
  % coq.reduction.vm.norm {{pol3}} _ X3,
  % pol_encode X3 Pol3,
  % pe_decode Pol3 P3,
  % coq.term->string P3 PS3,
  % coq.reduction.vm.norm {{pol1}} _ X1,
  pol_encode {{PX (Pc 2%Z) 2 (Pc 0%Z)}} Dx,
  pol_encode {{PX (Pc 1%Z) 1 (Pc 0%Z)}} Nx,
  collect_glob_lcm_poly (add Nx Dx) 1 LCM,
  if (LCM > 1) 
  (multiply_lcm_poly Nx LCM Ne,
  multiply_lcm_poly Dx LCM De) (Ne = Nx, De = Dx),
  gcd_poly Ne De Gcd,
    coq.say "gcd_poly passed",

  factorize_poly Ne De Ne' De',
  coq.say " fac passed",
  normalize_after_fac Ne' De' Ne'' De'',
  pe_decode Ne'' N'  %   coq.say "pe_decode passed",

}}.

(* gcd_for_field (PX (Pc 2%Z) 2 (Pc 0%Z)) (PX (Pc 1%Z) 1 (Pc 0%Z)). *)