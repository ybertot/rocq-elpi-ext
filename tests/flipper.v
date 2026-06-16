
From elpi Require Import elpi ext.
From Gcd.src Extra Dependency "encode.elpi" as encode.

From Stdlib Require Import Field Ring_polynom Reals.

Elpi Command test.
Elpi Accumulate Plugin "ext.elpi".
Check (fun x => Npos (xO x)).

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
Check (`C[2%Z] + `V[3] *`C[4%Z]^2).
Check ( `V[1]).

Goal True.
unshelve (epose (x:= _ :nat)).
exact 7%nat.
easy.
Qed.
Definition Peeval' := @PEeval R 0 1 Rplus Rmult Rminus Ropp Z IZR nat BinNat.N.to_nat pow.
Definition Feeval' := @FEeval R 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv Z IZR nat BinNat.N.to_nat pow.
Elpi Accumulate File encode.
Elpi Query lp:{{
collect_glob_lcm {{`V[ 1] ^ 5 + `C[ 10%Z] * `V[ 1] ^ 3 + `C[ 5%Z] * `V[ 1] ^ 2 + `C[ 3%Z] * `V[ 1] + `C[ 15%Z]}} 1 X.
}}.

Definition wrapper_PolZ (x : Pol Z) :=
True.


Definition wrapped_result (t: Z * (PExpr Z * (PExpr Z * PExpr Z))) :=
True.

Check wrapped_result (0%Z , (PEO, (PEO, PEO))).
Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.
Elpi Accumulate lp:{{

solve (goal _ _ T _ _  as G) GL :-
  T = {{wrapper_PolZ lp:Pol2 -> wrapper_PolZ lp:Pol1 -> _ }},
  pol_encode Pol1 Nx,
  pol_encode Pol2 Dx,
  collect_glob_lcm_poly (add Nx Dx) 1 LCM,
  if (LCM > 1) 
  (multiply_lcm_poly Nx LCM Ne,
  multiply_lcm_poly Dx LCM De) (Ne = Nx, De = Dx),
  gcd_poly Ne De Gcd,
  factorize_poly Ne De Ne' De',
  pe_decode Ne' N',
  pe_decode De' D',
  pe_decode Gcd Gcd',
  z_decode LCM Co,
  (refine 
  {{_  (I : (wrapped_result (pair lp:Co (pair lp:N' (pair lp:D' lp:Gcd')))))}}
  G GL).


solve (goal _ _ {{wrapper_LR lp:L -> wrapper_F lp:D -> wrapper_F lp:N -> _}} _ _ as G ) GL :-
  fe_encode N Nx,
  fe_encode D Dx,

  collect_glob_lcm_poly (add Nx Dx) 1 LCM,
  if (LCM > 1) 
  (multiply_lcm_poly Nx LCM Ne,
  multiply_lcm_poly Dx LCM De) (Ne = Nx, De = Dx)
  ,
  gcd_poly Ne De Gcd,
  factorize_poly Ne De Ne' De',
 fe_decode Ne' N',
  fe_decode De' D',
  fe_decode Gcd Gcd',

  z_decode LCM Co,
if (LCM > 1)
  (
    refine 
  {{let H : (1%R/(IZR lp:Co) *(Feeval' lp:L lp:N))%R = Feeval' lp:L (@FEmul Z lp:N' lp:Gcd') := _ in 
  let H' : (1%R/(IZR lp:Co) *(Feeval' lp:L lp:D))%R = Feeval' lp:L (@FEmul Z lp:D' lp:Gcd') := _ in _}}
  G GL)
  (refine 
  {{let H : (Feeval' lp:L lp:N) = Feeval' lp:L (@FEmul Z lp:N' lp:Gcd') := _ in 
  let H' : (Feeval' lp:L lp:D) = Feeval' lp:L (@FEmul Z lp:D' lp:Gcd') := _ in _}}
  G GL).
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
    match goal with  |- 
      wrapper_LR ?l'' -> wrapper_F ?d'' -> wrapper_F ?n'' -> _ =>
      idtac "hello";(elpi factorize_by_gcd n'' d''); intros _ _ _
      (* idtac *)
      end.  
Close Scope R_scope.

Ltac consume_gcd pol1 pol2 :=
let v := (gcd_for_field pol1 pol2) in
let w := constr:(v) in
assert (w = w) by easy.
Elpi Tactic factorize2.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate lp:{{

}}.
Goal True.
gcd_for_field (PX (Pc ((- 1)%Z)) 2%positive (Pc 1%Z))  (PX (Pc (1%Z)) 1%positive (Pc 1%Z)).

Ltac simplify_by_gcd n d :=
 unshelve foo1 n d; cbv [Peeval' PEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add]; try ring.

Goal True. 
 simplify_by_gcd (PI^5 + 4* PI^3 + 5* PI^2 +3* PI + 15)%R (PI^4 - PI ^3 + 2 *PI^2 - 3 * PI -3)%R; cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add]; try ring.

easy.
Qed.
