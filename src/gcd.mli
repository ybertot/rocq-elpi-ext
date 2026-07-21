type rat = { num: int; den: int }

val rat_zero : rat
val rat_one : rat
val rat_is_zero : rat -> bool


type poly = Const of rat | Var of int | Add of poly * poly | Mul of poly * poly

val poly_gcd : poly -> poly -> int * poly * poly * poly
