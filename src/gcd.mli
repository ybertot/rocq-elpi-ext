type rat = { num: int; den: int }

val rat_zero : rat
val rat_one : rat
val rat_is_zero : rat -> bool


type monomial = { coef: rat; exps: (int * int) list }
type mpoly    = monomial list

type poly = Const of rat | Var of int | Add of poly * poly | Mul of poly * poly

val mpoly_to_poly : mpoly -> poly
val to_mpoly : poly -> mpoly
val poly_gcd : poly -> poly -> poly
val poly_lcm : poly -> poly -> poly
val div_mpoly : mpoly -> mpoly -> mpoly
val normalise_lex : mpoly -> mpoly
val collect : mpoly -> mpoly
