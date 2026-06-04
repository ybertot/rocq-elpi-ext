(* let _ = Mltop.add_known_module "gcd"
let () = Tacentries.tactic_extend "gcd" "factorize_tactic" ~level:0 
[(
Tacentries.TyML (Tacentries.TyIdent ("factorize", Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), Tacentries.TyNil)), 
(fun t ist -> 
                                                                    
# 9 "gcd/gcd.mlg"
    let (numr,denomr,gcd) =  factorize t in 
    Tacticals.tclIDTAC 
# 15 "gcd/gcd.ml"
)))] *)

(* ══════════════════════════════════════════════════════════════════════
   Rational numbers
   ══════════════════════════════════════════════════════════════════════ *)
type rat = { num: int; den: int }

let rat_zero = { num = 0; den = 1 }
let rat_one  = { num = 1; den = 1 }

let gcd a b =
  let a = abs a and b = abs b in
  let rec g a b = if b = 0 then a else g b (a mod b) in g a b

let rat_simplify r =
  if r.num = 0 then rat_zero
  else
    let g = gcd (abs r.num) (abs r.den) in
    let sign = if r.den < 0 then -1 else 1 in
    { num = sign * r.num / g; den = sign * r.den / g }

let rat_add a b = rat_simplify { num = a.num * b.den + b.num * a.den; den = a.den * b.den }
let rat_mul a b = rat_simplify { num = a.num * b.num; den = a.den * b.den }
let rat_neg a   = { num = -a.num; den = a.den }
(* let rat_sub a b = rat_add a (rat_neg b) *)
let rat_inv a   = if a.num = 0 then failwith "div by zero"
                  else rat_simplify { num = a.den; den = a.num }
let rat_div a b = rat_mul a (rat_inv b)
let rat_is_zero r = r.num = 0

(* ══════════════════════════════════════════════════════════════════════
   Poly type
   ══════════════════════════════════════════════════════════════════════ *)
type poly = Const of rat | Var of int | Add of poly * poly | Mul of poly * poly

(* ══════════════════════════════════════════════════════════════════════
   Internal monomial representation
   coef * (variable index * exponent) list, sorted by variable index
   Exponents are always non-negative (int).
   ══════════════════════════════════════════════════════════════════════ *)
type monomial = { coef: rat; exps: (int * int) list }
type mpoly    = monomial list

let mono_normalise m =
  { m with exps = List.sort (fun (a,_) (b,_) -> compare a b)
             (List.filter (fun (_, e) -> e <> 0) m.exps) }

(* ══════════════════════════════════════════════════════════════════════
   poly -> mpoly
   ══════════════════════════════════════════════════════════════════════ *)
let rec to_mpoly = function
  | Const r      -> if rat_is_zero r then [] else [{ coef = r; exps = [] }]
  | Var x        -> [{ coef = rat_one; exps = [(x, 1)] }]
  | Add (p, q)   -> to_mpoly p @ to_mpoly q
  | Mul (p, q)   ->
    List.concat_map (fun a ->
      List.map (fun b ->
        let rec merge xs ys = match xs, ys with
          | [], ys -> ys | xs, [] -> xs
          | (xv,xe)::xt, (yv,ye)::yt ->
            if xv = yv then (xv, xe+ye) :: merge xt yt
            else if xv < yv then (xv,xe) :: merge xt ys
            else (yv,ye) :: merge xs yt
        in
        mono_normalise { coef = rat_mul a.coef b.coef; exps = merge a.exps b.exps }
      ) (to_mpoly q)
    ) (to_mpoly p)

(* ══════════════════════════════════════════════════════════════════════
   Collect like terms
   ══════════════════════════════════════════════════════════════════════ *)
let collect (p: mpoly) : mpoly =
  let tbl : ((int * int) list, rat ref) Hashtbl.t = Hashtbl.create 16 in
  List.iter (fun m ->
    match Hashtbl.find_opt tbl m.exps with
    | Some r -> r := rat_add !r m.coef
    | None   -> Hashtbl.add tbl m.exps (ref m.coef)
  ) p;
  Hashtbl.fold (fun exps r acc ->
    if rat_is_zero !r then acc else { coef = !r; exps } :: acc
  ) tbl []

(* ══════════════════════════════════════════════════════════════════════
   Lexicographic monomial order (Var 0 > Var 1 > ...)
   Higher exponent on the first differing variable = larger.
   ══════════════════════════════════════════════════════════════════════ *)
let compare_mono_lex (a: monomial) (b: monomial) : int =
  let rec cmp xs ys = match xs, ys with
    | [], []                    ->  0
    | [], (_, e)::_             ->  if e > 0 then  1 else 0
    | (_, e)::_, []             ->  if e > 0 then -1 else 0
    | (xv,xe)::xt, (yv,ye)::yt ->
      if xv = yv then
        let c = compare ye xe in
        if c <> 0 then c else cmp xt yt
      else if xv < yv then
        if xe > 0 then -1 else cmp xt ys
      else
        if ye > 0 then  1 else cmp xs yt
  in
  cmp a.exps b.exps

let normalise_lex (p: mpoly) : mpoly =
  List.sort compare_mono_lex (collect p)

(* ══════════════════════════════════════════════════════════════════════
   mpoly multiplication
   ══════════════════════════════════════════════════════════════════════ *)
let mul_mpoly (a: mpoly) (b: mpoly) : mpoly =
  normalise_lex (collect (
    List.concat_map (fun ma ->
      List.map (fun mb ->
        let rec merge xs ys = match xs, ys with
          | [], ys -> ys | xs, [] -> xs
          | (xv,xe)::xt, (yv,ye)::yt ->
            if xv = yv then (xv, xe+ye) :: merge xt yt
            else if xv < yv then (xv,xe) :: merge xt ys
            else (yv,ye) :: merge xs yt
        in
        mono_normalise { coef = rat_mul ma.coef mb.coef; exps = merge ma.exps mb.exps }
      ) b
    ) a
  ))

(* ══════════════════════════════════════════════════════════════════════
   mpoly subtraction
   ══════════════════════════════════════════════════════════════════════ *)
let sub_mpoly (a: mpoly) (b: mpoly) : mpoly =
  a @ List.map (fun m -> { m with coef = rat_neg m.coef }) b

(* ══════════════════════════════════════════════════════════════════════
   Leading monomial
   ══════════════════════════════════════════════════════════════════════ *)
let lm_lex (p: mpoly) : monomial option =
  match normalise_lex p with [] -> None | m :: _ -> Some m

(* ══════════════════════════════════════════════════════════════════════
   Divide monomial p by monomial q (returns None if impossible)
   ══════════════════════════════════════════════════════════════════════ *)
let divide_mono (p: monomial) (q: monomial) : monomial option =
  if rat_is_zero q.coef then None
  else
    let rec sub_exps ps qs = match ps, qs with
      | ps, []                  -> Some ps
      | [], (_, e)::_ when e>0  -> None
      | [], _                   -> Some []
      | (pv,pe)::pt, (qv,qe)::qt ->
        if pv = qv then
          if pe >= qe then
            Option.map (fun r -> if pe - qe = 0 then r else (pv, pe-qe)::r)
              (sub_exps pt qt)
          else None
        else if pv < qv then
          Option.map (fun r -> (pv,pe)::r) (sub_exps pt qs)
        else None
    in
    match sub_exps p.exps q.exps with
    | None      -> None
    | Some exps -> Some (mono_normalise { coef = rat_div p.coef q.coef; exps })

(* ══════════════════════════════════════════════════════════════════════
   Scale mpoly by a monomial
   ══════════════════════════════════════════════════════════════════════ *)
let scale_mpoly (m: monomial) (p: mpoly) : mpoly =
  List.map (fun t ->
    let rec merge xs ys = match xs, ys with
      | [], ys -> ys | xs, [] -> xs
      | (xv,xe)::xt, (yv,ye)::yt ->
        if xv = yv then (xv, xe+ye) :: merge xt yt
        else if xv < yv then (xv,xe) :: merge xt ys
        else (yv,ye) :: merge xs yt
    in
    mono_normalise { coef = rat_mul m.coef t.coef; exps = merge m.exps t.exps }
  ) p

(* ══════════════════════════════════════════════════════════════════════
   Polynomial division: p / q when q divides p exactly
   ══════════════════════════════════════════════════════════════════════ *)
let div_mpoly (p: mpoly) (q: mpoly) : mpoly =
  let q   = normalise_lex (collect q) in
  let ltq = match lm_lex q with
    | None   -> failwith "division by zero polynomial"
    | Some m -> m
  in
  let rec loop remainder quotient =
    let remainder = normalise_lex (collect remainder) in
    match lm_lex remainder with
    | None     -> quotient
    | Some ltr ->
      match divide_mono ltr ltq with
      | None        -> failwith "q does not divide p"
      | Some factor ->
        loop (sub_mpoly remainder (scale_mpoly factor q)) (factor :: quotient)
  in
  collect (loop p [])

(* ══════════════════════════════════════════════════════════════════════
   Multivariate reduction: reduce p modulo a list of polynomials
   ══════════════════════════════════════════════════════════════════════ *)
let reduce (p: mpoly) (gs: mpoly list) : mpoly =
  let gs_lm = List.filter_map (fun g ->
    match lm_lex g with None -> None | Some lm -> Some (lm, g)
  ) gs in
  let rec loop rem =
    let rem = normalise_lex rem in
    match rem with
    | [] -> []
    | ltr :: _ ->
      match List.find_opt (fun (lmg, _) ->
        match divide_mono ltr lmg with Some _ -> true | None -> false
      ) gs_lm with
      | None ->
        ltr :: loop (List.tl rem)
      | Some (lmg, g) ->
        let factor = Option.get (divide_mono ltr lmg) in
        loop (sub_mpoly rem (scale_mpoly factor g))
  in
  collect (loop p)

(* ══════════════════════════════════════════════════════════════════════
   mpoly -> poly
   ══════════════════════════════════════════════════════════════════════ *)
let mono_to_poly (m: monomial) : poly =
  let base = Const m.coef in
  List.fold_left (fun acc (v, e) ->
    let rec pow n = if n = 1 then Var v else Mul (Var v, pow (n-1)) in
    Mul (acc, if e = 1 then Var v else pow e)
  ) base m.exps

let mpoly_to_poly = function
  | []     -> Const rat_zero
  | [m]    -> mono_to_poly m
  | m::ms  -> List.fold_left (fun acc t -> Add (acc, mono_to_poly t))
                (mono_to_poly m) ms

(* ══════════════════════════════════════════════════════════════════════
   S-polynomial
   ══════════════════════════════════════════════════════════════════════ *)
let mono_lcm (a: monomial) (b: monomial) : monomial =
  let rec merge xs ys = match xs, ys with
    | [], ys -> ys | xs, [] -> xs
    | (xv,xe)::xt, (yv,ye)::yt ->
      if xv = yv then (xv, max xe ye) :: merge xt yt
      else if xv < yv then (xv,xe) :: merge xt ys
      else (yv,ye) :: merge xs yt
  in
  mono_normalise { coef = rat_one; exps = merge a.exps b.exps }

let s_poly (f: mpoly) (g: mpoly) : mpoly option =
  match lm_lex f, lm_lex g with
  | None, _ | _, None -> None
  | Some ltf, Some ltg ->
    let l = mono_lcm ltf ltg in
    match divide_mono l ltf, divide_mono l ltg with
    | None, _ | _, None -> None
    | Some ff, Some fg  ->
      Some (sub_mpoly (scale_mpoly ff f) (scale_mpoly fg g))

(* ══════════════════════════════════════════════════════════════════════
   Buchberger's algorithm
   ══════════════════════════════════════════════════════════════════════ *)
let groebner_basis_mpoly (generators: mpoly list) : mpoly array =
  let basis = ref (Array.of_list (List.filter (fun g -> g <> []) generators)) in
  let n = Array.length !basis in
  let pairs = ref [] in
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      pairs := (i, j) :: !pairs
    done
  done;
  let rec loop () =
    match !pairs with
    | [] -> ()
    | (i, j) :: rest ->
      pairs := rest;
      let fi = (!basis).(i) and fj = (!basis).(j) in
      (match s_poly fi fj with
       | None -> ()
       | Some sp ->
         let r = normalise_lex (reduce sp (Array.to_list !basis)) in
         if r <> [] then begin
           let new_idx = Array.length !basis in
           basis := Array.append !basis [| r |];
           for k = 0 to new_idx - 1 do
             pairs := (k, new_idx) :: !pairs
           done
         end);
      loop ()
  in
  loop ();
  !basis

(* let groebner_basis (generators: poly list) : poly list =
  generators
  |> List.map (fun p -> normalise_lex (collect (to_mpoly p)))
  |> groebner_basis_mpoly
  |> Array.to_list
  |> List.map mpoly_to_poly *)

(* ══════════════════════════════════════════════════════════════════════
   Interreduction -> reduced Gröbner basis
   ══════════════════════════════════════════════════════════════════════ *)
let interreduce (basis: mpoly list) : mpoly list =
  let monic m = match lm_lex m with
    | None    -> m
    | Some lm -> List.map (fun t -> { t with coef = rat_div t.coef lm.coef }) m
  in
  let rec reduce_all acc = function
    | [] -> acc
    | g :: rest ->
      let r = normalise_lex (reduce g (acc @ rest)) in
      if r = [] then reduce_all acc rest
      else reduce_all (monic r :: acc) rest
  in
  reduce_all [] basis

(* ══════════════════════════════════════════════════════════════════════
   Variable helpers
   ══════════════════════════════════════════════════════════════════════ *)
(* let rec max_var = function
  | Const _    -> -1
  | Var n      -> n
  | Add (p, q) -> max (max_var p) (max_var q)
  | Mul (p, q) -> max (max_var p) (max_var q) *)

let shift_up_mpoly (p: mpoly) : mpoly =
  List.map (fun m ->
    { m with exps = List.map (fun (v, e) -> (v + 1, e)) m.exps }
  ) p

let shift_down_mpoly (p: mpoly) : mpoly =
  List.map (fun m ->
    { m with exps = List.map (fun (v, e) -> (v - 1, e)) m.exps }
  ) p

let mpoly_has_t (p: mpoly) : bool =
  List.exists (fun m -> List.exists (fun (v, _) -> v = 0) m.exps) p

(* ══════════════════════════════════════════════════════════════════════
   GCD and LCM via Gröbner basis elimination

   Ideal membership identity:
     <t*p, (1-t)*q> ∩ k[x1,...,xn]  =  <lcm(p, q)>

   So the t-free elimination polynomial is lcm(p,q),
   and gcd(p,q) = p*q / lcm(p,q).
   ══════════════════════════════════════════════════════════════════════ *)
let poly_gcd_and_lcm (p: poly) (q: poly) : poly * poly =
  let mp = normalise_lex (collect (to_mpoly p)) in
  let mq = normalise_lex (collect (to_mpoly q)) in

  (* Shift original variables up by 1; t = Var 0 goes first in lex order,
     so it is eliminated first by Buchberger's algorithm.                 *)
  let mp_s = shift_up_mpoly mp in
  let mq_s = shift_up_mpoly mq in

  let t         : mpoly = [{ coef = rat_one;          exps = [(0, 1)] }] in
  let one_min_t : mpoly = [{ coef = rat_one;          exps = []       };
                            { coef = rat_neg rat_one; exps = [(0, 1)] }] in

  (* f = t * p,   g = (1 - t) * q *)
  let f = mul_mpoly t mp_s in
  let g = mul_mpoly one_min_t mq_s in

  let gb = groebner_basis_mpoly [f; g] in

  (* Extract and interreduce the t-free part of the basis *)
  let elim =
    Array.to_list gb
    |> List.filter (fun r -> r <> [] && not (mpoly_has_t r))
    |> interreduce
  in

  (* The t-free ideal is principal: pick the unique generator (after
     interreduction there should be exactly one up to scalar).           *)
  let lcm_m =
    match elim with
    | []  -> failwith "no elimination polynomial found"
    | [x] -> normalise_lex (shift_down_mpoly x)
    | xs  ->
      (* Defensive: take lowest total degree element *)
      let tdeg m = match lm_lex m with
        | None    -> 0
        | Some lm -> List.fold_left (fun a (_, e) -> a + e) 0 lm.exps
      in
      normalise_lex (shift_down_mpoly
        (List.fold_left (fun b c -> if tdeg c < tdeg b then c else b)
           (List.hd xs) (List.tl xs)))
  in

  (* gcd = p * q / lcm *)
  let pq    = mul_mpoly mp mq in
  let gcd_m = normalise_lex (div_mpoly pq lcm_m) in

  (mpoly_to_poly gcd_m, mpoly_to_poly lcm_m)

let poly_gcd (p: poly) (q: poly) : poly = fst (poly_gcd_and_lcm p q)
let poly_lcm (p: poly) (q: poly) : poly = snd (poly_gcd_and_lcm p q)


(* ══════════════════════════════════════════════════════════════════════
   Example
   ══════════════════════════════════════════════════════════════════════ *)

(* let p = Add (Mul (Mul (Var 1,Var 1), (Mul (Var 0, Var 0))), Mul (Var 0,Var 1))
let q = Mul (Var 0, Var 1) *)