
From elpi Require Import elpi ext.
From elpi.ext Extra Dependency "encode.elpi" as encode.

From Stdlib Require Import Field Ring_polynom Reals.
Import List.

Elpi Command test.
Elpi Accumulate Plugin "ext.elpi".
Open Scope R_scope.

Elpi Accumulate File encode.

Definition norm := norm_aux 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb.

Elpi Tactic factorize_by_gcd.
Elpi Accumulate Plugin "ext.elpi".
Elpi Accumulate File encode.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [trm N, trm D] as G) GL :-
  gcd_and_factors pol_encode pe_decode N D N' D' Gcd LCM,
  coq.reduction.vm.norm {{norm lp:N'}} {{Pol Z}} N'',
  coq.reduction.vm.norm {{norm lp:D'}} {{Pol Z}} D'',
  coq.reduction.vm.norm {{norm lp:Gcd}} {{Pol Z}} Gcd',
  (refine {{pair lp:LCM (pair lp:N'' (pair lp:D'' lp:Gcd'))}} G GL).

}}.

(* TODO: find how to reduce Pphi_pow without reducing IZR. *)
Ltac reduce_Pphi_pow :=
    cbv [fst snd Pphi_pow Pphi_avoid mult_dev Peq Z.eqb P0 mkmult_c
        mkmult_c_pos get_signZ Pos.eqb mkmult_rec List.rev' add_pow_list
        mkmult1 List.rev_append List.hd BinNat.N.add
        add_mult_dev mkadd_mult mkmult_c_pos mkmult_rec BinNat.N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op List.rev' List.rev_append  List.hd List.tl add_pow_list mkmult_rec Pos.add Nat.add].

