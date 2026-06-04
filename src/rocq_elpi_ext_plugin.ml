open Gcd
module API = Elpi.API
module E = API.RawData

let declare = let open API.AlgebraicData in declare



type mysumT = | MyC : int -> mysumT | MyA : (mysumT * mysumT) -> mysumT

let rec compute (s : mysumT) = match s with
  | MyC n -> n
  | MyA (s1, s2) -> compute s1 + compute s2

let myC = E.Constants.declare_global_symbol "myC"
let myA = E.Constants.declare_global_symbol "myA"

let gRat = E.Constants.declare_global_symbol "rat"
let gConst = E.Constants.declare_global_symbol "gconst"
let gVar = E.Constants.declare_global_symbol "var"
let gAdd = E.Constants.declare_global_symbol "add"
let gMul = E.Constants.declare_global_symbol "mul"

let embed_rat = function
  | { num = n; den = d } -> E.mkApp gRat (API.RawOpaqueData.of_int n) [API.RawOpaqueData.of_int d]


let rat_ = API.(AlgebraicData.declare {
  ty = TyName "ratT";
  doc = "blibli";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("rat","",A(BuiltInData.int,A (BuiltInData.int, N)),
      B (fun n d -> { num = n; den = d }),
      M (fun ~ok ~ko t -> match t with { num = n; den = d } -> ok n d ))]
} |> ContextualConversion.(!<))

let compute_rat_api = API.BuiltIn.MLCode(Pred("compute",
    In(rat_, "rat",
    Out(rat_, "rat",
    Easy("AAA"))),
    fun a _ ~depth -> (), Some ( {num = 2*a.num; den = a.den})),
    DocAbove)

let poly_ = API.(AlgebraicData.declare {
  ty = TyName "polyT";
  doc = "blibli";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("gconst","",A(rat_, N),
      B (fun n -> Const n),
      M (fun ~ok ~ko t -> match t with Const r -> ok r | _ -> ko ()));
    K("var","",A (BuiltInData.int, N),
      B (fun n -> Var n),
      M (fun ~ok ~ko t -> match t with Var n -> ok n | _ -> ko ()));
    K("add","",S(S(N)),
      B (fun x y -> Add (x, y)),
      M (fun ~ok ~ko t -> match t with Add (x,y) -> ok x y | _ -> ko ()));
    K("mul","",S(S(N)),
      B (fun x y -> Mul (x, y)),
      M (fun ~ok ~ko t -> match t with Mul (x,y) -> ok x y | _ -> ko ())); 
      ]
} |> ContextualConversion.(!<))


let compute_poly_api = API.BuiltIn.MLCode(Pred("compute_poly",
    In(poly_, "poly",
    Out(poly_, "poly",
    Easy("AAA"))),
    fun a _ ~depth -> (), Some ( a)),
    DocAbove)

let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
  MLData rat_;
  MLData poly_;
  compute_rat_api;
  compute_poly_api
]
