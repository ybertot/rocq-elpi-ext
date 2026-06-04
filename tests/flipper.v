
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
pos_decode N {{xO lp:X}} :- N mod 2 = 0, !, pos_decode N1 X, N is N1 * 2.
pos_decode N {{xI lp:X}} :- pos_decode N1 X, N is N1 * 2 + 1.

func z_encode term -> int.
z_encode {{Z0}} 0.
z_encode {{Zpos lp:P}} N :- pos_encode P N.
z_encode {{Zneg lp:P}} N :- pos_encode P N1, N is (0-N1).

func z_decode int -> term.
z_decode 0 {{Z0}} :- !.
z_decode N {{Zpos lp:P}} :- N > 0 ,!, pos_decode N P.
z_decode N {{Zneg lp:P}} :- pos_decode N1 P, N1 is (0-N).

func fe_encode term -> polyT.

fe_encode {{FEO}} (gconst (rat 0 1)).
fe_encode {{FEI}} (gconst (rat 1 1)).
fe_encode {{@FEc Z lp:C }} (gconst (rat C1 1)) :-
  z_encode C C1.
fe_encode {{FEX lp:X}} (var Y) :-
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
fe_decode (gconst (rat C1 1)) {{@FEc Z lp:C }} :- !,
  z_decode C1 C.
fe_decode (var Y) {{FEX lp:X}} :- !,
 pos_decode Y X.
fe_decode (add P1 (mul (gconst (rat (-1) 1)) P2)) {{FEsub lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2.
fe_decode (add P1 P2) {{@FEadd Z lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2 .
fe_decode (mul (gconst (rat (-1) 1)) P) {{FEopp lp:X}} :- !,
  fe_decode P X.

fe_decode (mul (mul Y Y) Z) {{FEpow lp:X (Npos (xI lp:N))}} :- 
  fe_decode Z X,
  fe_decode Y {{FEpow lp:X (Npos lp:N)}} ,!.
fe_decode (mul Y Y) {{FEpow lp:X (Npos (xO lp:N))}}:-
  fe_decode Y {{FEpow lp:X (Npos lp:N)}} , !.
fe_decode (mul P1 P2) {{FEmul lp:X1 lp:X2}} :- !,
  fe_decode P1 X1, fe_decode P2 X2.
% fe_decode (gconst (rat 1 1)) {{FEpow _ 0}}.
fe_decode Y {{FEpow lp:X (Npos 1)}}:-
  fe_decode Y X.



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

Notation "x + y" := (@FEadd Z x y).
Notation "x * y" := (@FEmul Z x y).
Notation "`C[ n ]" := (@FEc Z n).
Notation "x ^ y" := (@FEpow Z x (Npos y%positive)).

Check (`C[2%Z] + `C[3%Z] *`C[4%Z]^2).
Elpi Query  lp:{{
  fe_encode {{`C[2%Z] }} X
  %  ,fe_decode X Y
}}.
