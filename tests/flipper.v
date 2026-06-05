
From elpi Require Import elpi ext.

From Stdlib Require Import Field Reals.
Elpi Command test.
Elpi Accumulate Plugin "ext.elpi".
Check (fun x => Npos (xO x)).

Elpi Accumulate  lp:{{
func encode_rat term -> ratT.
encode_rat {{0}} (rat 0 1) :- !.
encode_rat {{S lp:X}} (rat N1 1) :- 
  encode_rat X (rat N 1), N1 is N + 1.

func encode term -> polyT.

encode T (gconst R) :-
  coq.typecheck T {{nat}} ok,!,
  encode_rat T R.
encode {{lp:X1 + lp:X2}} (add P1 P2) :-
  encode {{lp:X1}} P1, encode {{lp:X2}} P2.
  
encode {{lp:X1 * lp:X2}} (mul P1 P2) :-
  encode {{lp:X1}} P1, encode {{lp:X2}} P2.

func pos_encode term -> int.
pos_encode {{xH}} 1.
pos_encode {{xO lp:X}} N :- pos_encode X N1, N is N1 * 2.
pos_encode {{xI lp:X}} N :- pos_encode X N1, N is N1 * 2 + 1.

func pos_decode int -> term.

pos_decode 1 {{xH}} :- !.
pos_decode N {{xO lp:X}} :- 0 is N mod 2, !,  N1 is N div 2,  pos_decode N1 X.
pos_decode N {{xI lp:X}} :- N1 is N div 2, pos_decode N1 X.

func z_encode term -> int.
z_encode {{Z0}} 0.
z_encode {{Zpos lp:P}} N :- pos_encode P N.
z_encode {{Zneg lp:P}} N :- pos_encode P N1, N is 0 - N1.

func z_decode int -> term.
z_decode 0 {{Z0}} :- !.
z_decode N {{Zpos lp:P}} :- N > 0 ,!, pos_decode N P.
z_decode N {{Zneg lp:P}} :-  N1 is 0 - N, pos_decode N1 P.

func fe_encode term -> polyT.

fe_encode {{FEO}} (gconst (rat 0 1)).
fe_encode {{FEI}} (gconst (rat 1 1)).
fe_encode {{@FEc Z lp:C }} (gconst (rat C1 1)) :-
  z_encode C C1.
fe_encode {{@FEX Z lp:X}} (var Y) :-
 pos_encode X Y.
fe_encode {{@FEadd Z lp:X1 lp:X2}} (add P1 P2) :-
  fe_encode X1 P1, fe_encode X2 P2.
fe_encode {{FEsub lp:X1 lp:X2}} (add P1 (mul (gconst (rat (-1) 1)) P2)) :-
  fe_encode X1 P1, fe_encode X2 P2.
% fe_encode {{FEmul FEI lp:X2}} P2 :- !,
%   fe_encode X2 P2.
% fe_encode {{FEmul lp:X1 FEI}} P1 :- !,
%   fe_encode X1 P1.
fe_encode {{FEmul lp:X1 lp:X2}} (mul P1 P2) :-
  fe_encode X1 P1, fe_encode X2 P2.
fe_encode {{FEopp lp:X}} (mul (gconst (rat (-1) 1)) P) :-
  fe_encode X P.
fe_encode {{FEpow _ 0}} (gconst (rat 1 1)).

fe_encode {{FEpow lp:X (Npos 1)}} Y :-
  fe_encode X Y.
fe_encode {{FEpow lp:X (Npos (xO lp:N))}} (mul Y Y) :-
  fe_encode {{FEpow lp:X (Npos lp:N)}} Y.
fe_encode {{FEpow lp:X (Npos (xI lp:N))}} (mul (mul Y Y) Z) :-
  fe_encode X Z,
  fe_encode {{FEpow lp:X (Npos lp:N)}} Y.

func fe_decode polyT -> term.
fe_decode (gconst (rat 0 1)) {{FEO}} :- !.
fe_decode (gconst (rat 1 1)) {{FEI}} :- !.
fe_decode (gconst (rat Num 1)) {{@FEc Z lp:Num1 }} :- !,
  z_decode Num Num1.
fe_decode (gconst (rat Num Denom)) {{FEdiv (FEc lp:ZNum) (FEc lp:ZDenom)}} :- !,
  z_decode Num ZNum,
  z_decode Denom ZDenom.

fe_decode (var Y) {{FEX lp:X}} :- !,
 pos_decode Y X.
fe_decode (add P1 (mul (gconst (rat (-1) 1)) P2)) {{FEsub lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2.
fe_decode (add P1 P2) {{@FEadd Z lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2 .
fe_decode (mul (gconst (rat 1 1)) X) Y :- !,
  fe_decode X Y.
fe_decode (mul X (gconst (rat 1 1))) Y :- !,
  fe_decode X Y.
fe_decode (mul X (gconst (rat (-1) 1))) {{FEopp lp:Y}} :- !,
  fe_decode X Y.
fe_decode (mul (gconst (rat (-1) 1)) P) {{FEopp lp:X}} :- !,
  fe_decode P X.

fe_decode (mul (mul Y Y) Z) {{FEpow lp:X (Npos (xI lp:N))}} :- 
  fe_decode Z X,
  fe_decode Y {{FEpow lp:X (Npos lp:N)}} ,!.

fe_decode (mul (mul Y Y) Z) {{FEpow lp:X (Npos 3)}} :- 
  fe_decode Z X,
  fe_decode Y X ,!.

fe_decode (mul Y Y) {{FEpow lp:X (Npos (xO lp:N))}}:-
  fe_decode Y {{FEpow lp:X (Npos lp:N)}} , !.

fe_decode (mul Y Y) {{FEpow lp:Z (Npos 2)}}:-
  fe_decode Y Z , !.

fe_decode (mul P1 P2) {{FEmul lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2.
% % fe_decode (gconst (rat 1 1)) {{FEpow _ 0}}.
% fe_decode Y {{FEpow lp:X (Npos 1)}}:-
%   fe_decode Y X.



func decode_rat ratT -> term.
decode_rat (rat 0 1) {{0}} :- !.
decode_rat (rat N1 1) {{S lp:X}} :- !,
  N2 is N1 - 1, decode_rat (rat N2 1) X.

func decode polyT -> term.
decode  (gconst R) T :-
  coq.typecheck T {{nat}} ok,
  decode_rat R T.
decode (add P1 P2) {{lp:X1 + lp:X2}} :-
  decode  P1 X1, decode P2 X2.
  
decode (mul P1 P2) {{lp:X1 * lp:X2}} :-
  decode  P1 X1, decode P2 X2.
}}.
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


Check (`C[2%Z] + `V[3] *`C[4%Z]^2).
Check ( `V[1]).

Elpi Query  lp:{{

  fe_encode {{`V[ 1] ^ 5 + `C[ 4%Z] * `V[ 1] ^ 3 + `C[ 5%Z] * `V[ 1] ^ 2 + `C[ 3%Z] * `V[ 1] +
`C[ 15%Z] }} X1,
   fe_encode {{`V[ 1] ^ 4 - `V[ 1] ^ 3 + `C[ 2%Z] * `V[ 1] ^ 2 - `C[ 3%Z] * `V[ 1] - `C[ 3%Z]}} X2,
      fe_encode {{`C[ 3%Z]}} X4,
  gcd_poly X1 X2 X3,
  fe_decode X3 Y,
  coq.term->string Y YS,
  factorize_poly X1 X2 X5 X6,
  fe_decode X5 P,
  coq.term->string P PS,
   fe_decode X6 Q,
  coq.term->string Q QS
}}.

Goal True.
unshelve (epose (x:= _ :nat)).
exact 7%nat.
easy.
Qed.

Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate lp:{{

func pos_encode term -> int.
pos_encode {{xH}} 1.
pos_encode {{xO lp:X}} N :- pos_encode X N1, N is N1 * 2.
pos_encode {{xI lp:X}} N :- pos_encode X N1, N is N1 * 2 + 1.

func pos_decode int -> term.
pos_decode 1 {{xH}} :- !.
pos_decode N {{xO lp:X}} :- 0 is N mod 2, !,  N1 is N div 2,  pos_decode N1 X.
pos_decode N {{xI lp:X}} :- N1 is N div 2, pos_decode N1 X.

func z_encode term -> int.
z_encode {{Z0}} 0.
z_encode {{Zpos lp:P}} N :- pos_encode P N.
z_encode {{Zneg lp:P}} N :- pos_encode P N1, N is 0 - N1.

func z_decode int -> term.
z_decode 0 {{Z0}} :- !.
z_decode N {{Zpos lp:P}} :- N > 0 ,!, pos_decode N P.
z_decode N {{Zneg lp:P}} :-  N1 is 0 - N, pos_decode N1 P.

func fe_encode term -> polyT.

fe_encode {{FEO}} (gconst (rat 0 1)).
fe_encode {{FEI}} (gconst (rat 1 1)).
fe_encode {{@FEc Z lp:C }} (gconst (rat C1 1)) :-
  z_encode C C1.
fe_encode {{@FEX Z lp:X}} (var Y) :-
 pos_encode X Y.
fe_encode {{@FEadd Z lp:X1 lp:X2}} (add P1 P2) :-
  fe_encode X1 P1, fe_encode X2 P2.
fe_encode {{FEsub lp:X1 lp:X2}} (add P1 (mul (gconst (rat (-1) 1)) P2)) :-
  fe_encode X1 P1, fe_encode X2 P2.
fe_encode {{FEmul lp:X1 lp:X2}} (mul P1 P2) :-
  fe_encode X1 P1, fe_encode X2 P2.
fe_encode {{FEopp lp:X}} (mul (gconst (rat (-1) 1)) P) :-
  fe_encode X P.
fe_encode {{FEpow _ 0}} (gconst (rat 1 1)).
fe_encode {{FEpow lp:X (Npos 1)}} Y :-
  fe_encode X Y.
fe_encode {{FEpow lp:X (Npos (xO lp:N))}} (mul Y Y) :-
  fe_encode {{FEpow lp:X (Npos lp:N)}} Y.
fe_encode {{FEpow lp:X (Npos (xI lp:N))}} (mul (mul Y Y) Z) :-
  fe_encode X Z,
  fe_encode {{FEpow lp:X (Npos lp:N)}} Y.

func fe_decode polyT -> term.
fe_decode (gconst (rat 0 1)) {{FEO}} :- !.
fe_decode (gconst (rat 1 1)) {{FEI}} :- !.
fe_decode (gconst (rat Num 1)) {{@FEc Z lp:Num1 }} :- !,
  z_decode Num Num1.
fe_decode (gconst (rat Num Denom)) {{FEdiv (FEc lp:ZNum) (FEc lp:ZDenom)}} :- !,
  z_decode Num ZNum,
  z_decode Denom ZDenom.
fe_decode (var Y) {{FEX lp:X}} :- !,
 pos_decode Y X.
fe_decode (add P1 (mul (gconst (rat (-1) 1)) P2)) {{FEsub lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2.
fe_decode (add P1 P2) {{@FEadd Z lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2 .
fe_decode (mul (gconst (rat 1 1)) X) Y :- !,
  fe_decode X Y.
fe_decode (mul X (gconst (rat 1 1))) Y :- !,
  fe_decode X Y.
fe_decode (mul X (gconst (rat (-1) 1))) {{FEopp lp:Y}} :- !,
  fe_decode X Y.
fe_decode (mul (gconst (rat (-1) 1)) P) {{FEopp lp:X}} :- !,
  fe_decode P X.
fe_decode (mul (mul Y Y) Z) {{FEpow lp:X (Npos (xI lp:N))}} :- 
  fe_decode Z X,
  fe_decode Y {{FEpow lp:X (Npos lp:N)}} ,!.
fe_decode (mul (mul Y Y) Z) {{FEpow lp:X (Npos 3)}} :- 
  fe_decode Z X,
  fe_decode Y X ,!.
fe_decode (mul Y Y) {{FEpow lp:X (Npos (xO lp:N))}}:-
  fe_decode Y {{FEpow lp:X (Npos lp:N)}} , !.
fe_decode (mul Y Y) {{FEpow lp:Z (Npos 2)}}:-
  fe_decode Y Z , !.
fe_decode (mul P1 P2) {{FEmul lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2.


solve (goal _ _ T _ [trm N, trm D] as G) GL :-
  fe_encode N Ne,
  fe_encode D De,
  gcd_poly Ne De Gcd,
  factorize_poly Ne De Ne' De',
  fe_decode Ne' N',
  fe_decode De' D',
  fe_decode Gcd Gcd',
coq.say ":()",
coq.say {coq.term->string N'},
coq.say {coq.term->string D'},
coq.say {coq.term->string Gcd'},
pi x\ 
((copy Gcd' x :- !) ==> copy T (Tabs x)),
Hole x = {{_ : lp:{{Tabs x}}}},
refine 
  (let `_gcd` _ Gcd' x\ Hole x) G GL,
  coq.say "yay".
  

}}.

Goal True.
  elpi factorize_by_gcd (`V[1] ^ 2) (`V[1] ).
  sorry.
Qed.

