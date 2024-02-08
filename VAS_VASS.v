From mathcomp Require Import all_ssreflect all_algebra ssrint.
From mathcomp Require Import ssralg fintype ssrnum finmap.
Import Order.TTheory Num.Theory GRing.Theory.
Require Import monad. (*From https://bitbucket.org/mituharu/karpmiller/src/master/*)
Require Import vecop vectrans.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.

Section VAS.
Variable dim : nat.
Definition VAS := {fset (vint dim)}.
Definition markingVAS : Type := vnat dim.
Definition nextVAS {vas : VAS} (m : markingVAS) (v : vas) : option markingVAS 
 := vtrans m (val v).
End VAS.

Section VASS.
Variables (dim : nat) (state : finType).
Definition VASS  := {fset (state * vint dim * state)}.
Definition confVASS : Type := state * vnat dim.
Definition nextVASS {vass : VASS} (c : confVASS) (a : vass) 
 : option confVASS := let: (q1,v,q2) := val a in
  let: (q,m) := c in
   if q1 == q then 
    if vtrans m v is Some t then Some (q2, t) else None
  else None.
End VASS.

Definition reachable' {S T : Type} (next : S -> T -> option S) (x0 x : S) :=
 exists s : seq T, foldm next x0 s = Some x.

