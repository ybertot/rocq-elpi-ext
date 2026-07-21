module API = Elpi.API

open Gcd
open API
open ContextualConversion

let rat_ = AlgebraicData.declare {
  ty = TyName "ratT";
  doc = "a type of rational numbers viewed as pairs of int values";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("rat","numerator then denumerator",
      A(BuiltInData.int,A (BuiltInData.int, N)),
      B (fun n d -> { num = n; den = d }),
      M (fun ~ok ~ko t -> match t with { num = n; den = d } -> ok n d ))]
} |> (!<)

let poly_ = AlgebraicData.declare {
  ty = TyName "polyT";
  doc = "A type of ring expressions, simply with numeric constants," ^
        " variables, addition, and multiplication";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("pcst","constant polynomial", A(rat_, N),
      B (fun n -> Const n),
      M (fun ~ok ~ko t -> match t with Const r -> ok r | _ -> ko ()));
    K("var","indexed variable",A (BuiltInData.int, N),
      B (fun n -> Var n),
      M (fun ~ok ~ko t -> match t with Var n -> ok n | _ -> ko ()));
    K("add","binary addition",S(S(N)),
      B (fun x y -> Add (x, y)),
      M (fun ~ok ~ko t -> match t with Add (x,y) -> ok x y | _ -> ko ()));
    K("mul","binary multiplication",S(S(N)),
      B (fun x y -> Mul (x, y)),
      M (fun ~ok ~ko t -> match t with Mul (x,y) -> ok x y | _ -> ko ()));
      ]
} |> (!<)


open BuiltInPredicate.Notation

let gcd_poly_api =
    let ty = poly_ in
    BuiltIn.MLCode(Pred ("gcd_poly",
    In(ty, "p1", In(ty, "p2",
    Out(API.BuiltInData.int, "factor",
    Out(ty, "gcd",Out (ty, "p1_div",Out (ty, "p2_div",
    Easy("gcd is the greatest common divisor of polynomials p1 and p2," ^
         "up to an integer factor \n" ^
         " p1_div is (factor * p1)/gcd, p2_div is (factor * p2)/gcd"))))))),
    fun a b _ _ _ _ ~depth ->
      (match Gcd.poly_gcd a b with
        (v1, v2, v3, v4) -> !: v1 +! v2 +! v3 +! v4)),
    DocAbove)

let expensive_id_api =
  let ty = poly_ in
  BuiltIn.MLCode(Pred ("expensive_id", In(ty, "",
    (Out(ty, "", Easy("identity function")))),
    fun a _ ~depth -> !: (expensive_id a)), DocAbove)

let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
  MLData rat_;
  MLData poly_;
  gcd_poly_api;
  expensive_id_api
]
