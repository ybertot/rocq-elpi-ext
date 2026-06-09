
From elpi Require Import elpi ext.
From Gcd.src Extra Dependency "encode.elpi" as encode.

From Stdlib Require Import Field Reals.
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
Definition Feeval' := @FEeval R 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv Z IZR nat BinNat.N.to_nat pow.
Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ L ) _ :-
coq.say L,fail.

solve (goal _ _ _ _ [trm N, trm D] as G) GL :-
  coq.say "a",

  fe_encode N Ne,
  fe_encode D De,
  coq.say {coq.term->string N},
  gcd_poly Ne De Gcd,
  
  factorize_poly Ne De Ne' De',
  fe_decode Ne' N',
  fe_decode De' D',
  fe_decode Gcd Gcd',
refine 
{{let H : lp:N = (@FEmul Z lp:N' lp:Gcd') := _ in 
  let H' : lp:D = (@FEmul Z lp:D' lp:Gcd') := _ in _}}
  G GL.


solve (goal _ _ {{wrapper_LR lp:L -> wrapper_F lp:D -> wrapper_F lp:N -> _}} _ _ as G ) GL :-
coq.say L,
  fe_encode N Ne,
  fe_encode D De,
  coq.say {coq.term->string N},
  gcd_poly Ne De Gcd,
  
  factorize_poly Ne De Ne' De',
  fe_decode Ne' N',
  fe_decode De' D',
  fe_decode Gcd Gcd',
refine 
{{let H : (Feeval' lp:L lp:N) = Feeval' lp:L (@FEmul Z lp:N' lp:Gcd') := _ in 
  let H' : (Feeval' lp:L lp:D) = Feeval' lp:L (@FEmul Z lp:D' lp:Gcd') := _ in _}}
  G GL.
}}.




Goal True.
  unshelve elpi factorize_by_gcd (`V[1] ^ 2) (`V[1] ).
   elpi factorize_by_gcd (`V[ 1] ^ 5 + `C[ 4%Z] * `V[ 1] ^ 3 + `C[ 5%Z] * `V[ 1] ^ 2 + `C[ 3%Z] * `V[ 1] +
`C[ 15%Z]) (`V[ 1] ^ 4 - `V[ 1] ^ 3 + `C[ 2%Z] * `V[ 1] ^ 2 - `C[ 3%Z] * `V[ 1] - `C[ 3%Z]).
  Show 3.
(* assert (H : True = True). *)
Show Proof.
  elpi factorize_by_gcd (`V[1] ^ 2) (`V[1] ).
Admitted.
Locate "_ ^ _".
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
Elpi Tactic factorize2.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate lp:{{
  

}}.

Ltac simplify_by_gcd n d :=
 unshelve foo1 n d; cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add]; try ring.

Goal True. 
 simplify_by_gcd (PI^5 + 4* PI^3 + 5* PI^2 +3* PI + 15)%R (PI^4 - PI ^3 + 2 *PI^2 - 3 * PI -3)%R; cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add]; try ring.
cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add] in H.
cbv [Feeval' FEeval BinList.nth BinNat.N.to_nat List.hd PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add] in H'.
easy.
Qed.
