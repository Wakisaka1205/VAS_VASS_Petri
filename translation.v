From mathcomp Require Import all_ssreflect all_algebra ssrint.
From mathcomp Require Import ssralg fintype ssrnum finmap zify.
From AlmostFull.PropBounded Require Import AlmostFull.
Import Order.TTheory Num.Theory GRing.Theory.
Require Import ssreflectext orderext monad afext petrinet.
(*From https://bitbucket.org/mituharu/karpmiller/src/master/*)
Require Import vecop vectrans VAS_VASS.
Set Implicit Arguments.
Unset Strict Implicit. 
Unset Printing Implicit Defensive.
Local Open Scope order_scope.
Local Open Scope fset_scope.
Declare Scope petri_net_scope.
Delimit Scope petri_net_scope with PN.
Local Open Scope petri_net_scope.

Section VAS2Petri.
Variable dim : nat.
Local Notation VAS := (VAS dim).
Definition Petri_of_VAS (V : VAS) : petri_net :=
 PetriNet
 (fun t : V => [ffun i : 'I_dim => if ((val t) i < 0)%R
   then `|(val t) i | else 0])
 (fun t : V => [ffun i : 'I_dim => if ((val t) i > 0)%R
   then `|(val t) i | else 0]).
Definition Petri_of_VAS_m (V : VAS) (m : markingVAS dim) 
 : marking (Petri_of_VAS V) := m.
Definition Petri_of_VAS_t (V : VAS) (v : V) 
 : transition (Petri_of_VAS V) := v.

Lemma Petri_of_VAS_transitionable (V : VAS) (m : markingVAS dim) (v : V) : 
[forall i, (0 <= ((val m + val v) i))%R] = (pre (Petri_of_VAS_t v) <= Petri_of_VAS_m _ m).
Proof.
apply/forallP/forallP => /[swap] p /(_ p); rewrite !ffunE.
 case: ifP => //.
 rewrite leEnat -lez_nat => /ltz0_abs -> ?.
 by rewrite -subr_ge0 opprK.
case: ltP.
 move/ltz0_abs. rewrite leEnat -lez_nat => -> ?.
 by rewrite -(opprK (\val v p)) subr_ge0.
by rewrite leEnat -lez_nat => ? ?; apply: addr_ge0.
Qed.

Lemma Petri_of_VAS_next (V : VAS) (m : markingVAS dim) (v : V) : 
 omap (Petri_of_VAS_m V) (nextVAS m v) = nextm (Petri_of_VAS_m V m) (Petri_of_VAS_t v).
Proof.
rewrite /nextm omap_id -Petri_of_VAS_transitionable /nextVAS /vtrans.
case: insubP=> [? /[dup] /forallP H1 -> /ffunP H2 |/negPf -> //].
congr Some; apply/ffunP => x; rewrite !ffunE.
apply/eqP; rewrite -eqz_nat; apply/eqP.
move: (H2 x); rewrite !ffunE => ->.
case: ltrgt0P => [?|?|v0].
  by rewrite subn0 PoszD gtz0_abs.
 rewrite addn0 -subzn -?lez_nat ltz0_abs // ?opprK //.
 by rewrite -subr_ge0 opprK; move: (H1 x); rewrite !ffunE.
by rewrite v0 subn0 PoszD.
Qed.

Lemma reachable_Petri_of_VAS (V : VAS) :
 forall (m0 m : markingVAS dim),
 reachable' (@nextVAS _ V) m0 m <-> reachable (Petri_of_VAS_m V m0) (Petri_of_VAS_m _ m).
Proof.
move=> m0 m; rewrite /Petri_of_VAS_m; split => -[s].
 elim/last_ind: s => [|s t IH] in m *; first by case => ->; exists [::].
 rewrite foldm_rcons_some => -[m' [/IH [s' m0_s'_m'] m'_to_m]].
 exists (rcons s' t); rewrite foldm_rcons_some; exists m'; split => //.
 by rewrite -Petri_of_VAS_next omap_id.
elim/last_ind: s => /= [|s t IH] in m *; first by case => ->; exists [::].
rewrite foldm_rcons_some => -[m' [/IH [s' H] m'_t_m]].
exists (rcons s' t); rewrite foldm_rcons_some; exists m'; split => //.
move: m'_t_m; rewrite -Petri_of_VAS_next.
by case: (nextVAS m' t).
Qed.

End VAS2Petri.

Section Petri2VASS.
Variable pn : petri_net.
Definition VASS_of_Petri_state : finType :=
 option (transition pn).
Definition VASS_of_Petri_dim : nat := #|place pn|.
Definition VASS_of_Petri_marking (m : marking pn) : 
 vnat (VASS_of_Petri_dim) := [ffun i => m (enum_val i)].
Definition VASS_of_Petri_pre (t : transition pn) :
 VASS_of_Petri_state * vint VASS_of_Petri_dim * VASS_of_Petri_state :=
  (None,
  fflift (fun n => - n%:Z)%R (VASS_of_Petri_marking (pre t)),
  Some t).
Definition VASS_of_Petri_post (t : transition pn):
 VASS_of_Petri_state * vint VASS_of_Petri_dim * VASS_of_Petri_state :=
  (Some t,
  fflift (fun n => n%:Z)%R (VASS_of_Petri_marking (post t)),
  None).
Definition VASS_of_Petri_t :
 VASS VASS_of_Petri_dim VASS_of_Petri_state :=
  [fset VASS_of_Petri_pre t | t : transition pn] `|`
  [fset VASS_of_Petri_post t | t : transition pn].
Definition Petri_of_VASS_marking (m : vnat VASS_of_Petri_dim) :
 marking pn := [ffun p : place pn => m (enum_rank p)].

Lemma VASS_of_Petri_markingK :
 cancel VASS_of_Petri_marking Petri_of_VASS_marking.
Proof. 
 by move=> ?; apply/ffunP => ?; rewrite !ffunE enum_rankK.
Qed.

Lemma Petri_of_VASS_markingK :
 cancel Petri_of_VASS_marking VASS_of_Petri_marking .
Proof.
 by move=> m; apply/ffunP => ?; rewrite !ffunE enum_valK.
Qed.

Lemma VASS_of_Petri_Transitionable (pt : transition pn) (pm : marking pn):
 (pre pt <= pm) =
 [forall i , 0 <= (\val (VASS_of_Petri_marking pm)
 + (fflift (fun n => - n%:Z)%R (VASS_of_Petri_marking (pre pt)))) i]%R.
Proof.
apply/forallP/forallP => /[swap] [x /(_ (enum_val x)) | p /(_ (enum_rank p))].
 by rewrite !ffunE subr_ge0.
by rewrite !ffunE subr_ge0 enum_rankK.
Qed.

Lemma reachable_VASS_of_Petri (m0 m : marking pn) :
 reachable m0 m ->
 reachable' (@nextVASS _ _ VASS_of_Petri_t) 
  (None, VASS_of_Petri_marking m0) (None, VASS_of_Petri_marking m).
Proof.
case => s; elim/last_ind : s => [|s t IH] in m *.
 by case => ->; exists [::].
rewrite foldm_rcons_some => -[m' [/IH [s' ?] m'_t_m]].
have T1 : VASS_of_Petri_pre t \in VASS_of_Petri_t.
 by rewrite !inE in_imfset.
have T2 : VASS_of_Petri_post t \in VASS_of_Petri_t.
 by rewrite !inE in_imfset ?orbT.
exists (s' ++ [:: [` T1]; [` T2]]).
rewrite foldm_cat_some; exists (None, VASS_of_Petri_marking m'); split => //=.
rewrite /nextVASS !SubK /=.
move: m'_t_m; rewrite /nextm.
case: ifP => // /[dup] /forallP ? H1 [/ffunP H2].
rewrite VASS_of_Petri_Transitionable in H1.
rewrite /vtrans insubT /= eqxx SubK insubT.
 apply/forallP => i; rewrite !ffunE addr_ge0 //. 
 by move: H1 => /forallP /(_ i); rewrite !ffunE.
move=> ?; congr (Some (None, _)).
apply: val_inj; rewrite SubK.
by apply/ffunP=> i; rewrite !ffunE -H2 !ffunE PoszD subzn.
Qed.

Lemma reachable_Petri_of_VASS' (m0 : nat ^ (VASS_of_Petri_dim)) 
(conf : confVASS (VASS_of_Petri_dim) (VASS_of_Petri_state)) :
 reachable' (@nextVASS _ _ VASS_of_Petri_t) (None,m0) conf ->
 match conf with
 |(None, m) =>
   reachable (Petri_of_VASS_marking m0) (Petri_of_VASS_marking m)
 |(Some t, m') => 
   exists m : nat ^ (VASS_of_Petri_dim),
    reachable (Petri_of_VASS_marking m0) (Petri_of_VASS_marking m)
     /\ pre t <= Petri_of_VASS_marking m
     /\ Petri_of_VASS_marking m' = Petri_of_VASS_marking m :-: pre t
 end.
Proof.
case => s; elim/last_ind: s => [|s' t' IH] /= in conf *.
 by move=> -[<-]; exists [::].
rewrite foldm_rcons_some /nextVASS => -[c []].
case: c (IH c) => -[t|] m' H /H {IH} {H}.
 move=> -[m'' [[s Hs]] [? H]].
 case/fsetUP : (valP t'); first by case/imfsetP => ? _ ->.
 case/imfsetP => x _ ->.
 case: ifP => // /eqP [->].
 rewrite /vtrans insubT.
  by apply/forallP => i; rewrite !ffunE.
 move=> ? [<-]; exists (s ++ [:: t]).
 rewrite foldm_cat_some; exists (Petri_of_VASS_marking m''); split => //=.
 rewrite /nextm ifT //= -H; congr Some.
 by apply/ffunP => i; rewrite !ffunE absz_nat enum_rankK.
move=> -[s H].
case/fsetUP : (valP t'); last by case/imfsetP => ? _ ->.
case/imfsetP => x _ -> /=.
rewrite /vtrans; case: insubP => // ? /forallP H1 /ffunP H2 [<-].
exists m'; repeat split; first by exists s.
 apply/forallP => p; move: (H1 (enum_rank p)).
 by rewrite !ffunE subr_ge0 enum_rankK.
apply/ffunP => p; move: (H2 (enum_rank p)).
by rewrite !ffunE enum_rankK; lia.
Qed.

Lemma reachable_Petri_of_VASS (m0 m : marking pn) :
 reachable' (@nextVASS _ _ VASS_of_Petri_t)  (None, VASS_of_Petri_marking m0) (None, VASS_of_Petri_marking m)
 -> reachable m0 m.
Proof.
 by move/reachable_Petri_of_VASS'; rewrite !VASS_of_Petri_markingK.
Qed.

Lemma reachable_Petri_VASS (m0 m : marking pn) :
 reachable m0 m
 <-> reachable' (@nextVASS _ _ VASS_of_Petri_t)  (None, VASS_of_Petri_marking m0) (None, VASS_of_Petri_marking m).
Proof.
 split; first exact: reachable_VASS_of_Petri.
 exact: reachable_Petri_of_VASS.
Qed.
End Petri2VASS.

Section VASS2VAS.
Variables (dim : nat) (state : finType) (vass : VASS dim state).
Variable a b : state -> nat.
Hypothesis hypo_ab : ab_aligned a b.
Local Notation vs := (vs a b).
Local Notation vst := (vst a b).
  
Definition VAS_of_VASS_m (c : confVASS dim state) : (markingVAS (dim + 3)) :=
 let: (q, m) := c in vcat m (vs q 0%R).
Definition VAS_of_VASS_01 (b' : bool) (q : state) 
 : vint (dim + 3) := vcat (0%R : vint dim) (vst q q (b'%:R)%R).
Definition VAS_of_VASS_2 (p q : state) (v : vint dim)
 : vint (dim + 3) := vcat v (vst p q 2%R).
Definition VAS_of_VASS_t : VAS (dim+3) := 
 [fset VAS_of_VASS_01 b' q | b' : bool, q : state] 
 `|` [fset let: (p,v,q) := t in VAS_of_VASS_2 p q v | t in vass].

Definition reachable {S T : Type} (next : S -> T -> option S) (x0 x : S) :=
 exists s : seq T, foldm next x0 s = Some x.
 
Lemma vtransE_vs (p p' q : state) (i i': 'Z_3) : 
 vtrans (vs p i) (vst p' q i') =  
 if (p' == p) && (i' == i) then Some (vs q (i + 1)%R) else None.
Proof. by rewrite (ab_aligned_vs hypo_ab). Qed.

Lemma vs_inj (q q' : state) (i i' : 'Z_3) :
 vs q i = vs q' i' -> q = q' /\ i = i'.
Proof.
 move/(congr1 (@vtrans 3 ^~ (vst q q i))); rewrite !vtransE_vs !eqxx /=.
 by case: ifP => // /andP [/eqP -> /eqP ->].
Qed.

Lemma VAS_of_VASS_reachable (c0 c : confVASS dim state) :
 reachable (@nextVASS _ _ vass) c0 c -> 
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) (VAS_of_VASS_m c).
Proof.
 case=> s; elim/last_ind: s => [|s' x IH] in c *.
  by case => ->; exists [::].
 rewrite foldm_rcons_some => -[[q'' m'']] [/IH] {IH}.
 case: c => [q' m'] [t'] Ht'; case E: (val x) => [[p v] p'] /[dup] H.
 rewrite /nextVASS E; move: E; case: ifP => // /eqP -> /[swap].
 case E': (vtrans m'' v) => [w|//] [-> H'] E.
 have T1 (b' : bool) : VAS_of_VASS_01 b' q'' \in VAS_of_VASS_t.
  by rewrite !inE; apply/orP; left; rewrite in_imfset2.
 have T2 : VAS_of_VASS_2 q'' q' v \in VAS_of_VASS_t.
  apply/fsetUP; right; apply/imfsetP => /=. 
  by exists (val x); [apply: valP|rewrite E].
 exists (t' ++ [:: [` T1 false]; [` T1 true]; [` T2]]).
 rewrite foldm_cat_some; exists (VAS_of_VASS_m (q'', m'')); split => //. 
 rewrite /= /nextVAS /= vtrans_vcat vtransE_vs vtrans0 !eqxx /=.
 rewrite vtrans_vcat vtransE_vs vtrans0 !eqxx /=.
 by rewrite vtrans_vcat vtransE_vs E' H' !eqxx /=.
Qed.

Lemma VASS_of_VAS_reachable' (c0 : confVASS dim state) (vm : markingVAS (dim+3)) :
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) vm ->
 exists q m i, vm = vcat m (vs q i) /\ reachable (@nextVASS _ _ vass) c0 (q,m).
Proof.
 case => t; elim/last_ind: t => [|s x IH] in vm *.
  case: c0 => [q0 m0]. case=> <-; exists q0, m0, 0%R; split => //. 
  by exists [::].
 rewrite foldm_rcons_some /nextVAS => -[vm'] [].
 move/IH => -[q' [m' [i]]] [-> H_reach] {IH}.
 case/fsetUP: (valP x).
  case/imfset2P => /= b' _ [r _] ->.
  rewrite /VAS_of_VASS_01 vtrans_vcat vtrans0 vtransE_vs.
  case: ifP => // /andP [/eqP -> /eqP <-] [<-].
  by exists q', m', ((b'%:R) + 1)%R.
 case/imfsetP => /= v Hv ->. case E: v => /= [pm q''].
 case: pm => p m'' in E *.
 rewrite vtrans_vcat vtransE_vs.
 case E': vtrans => [m|//]. move: E => /[swap].
 case: ifP => // /andP [/eqP -> /eqP <-] [] <- E.
 exists q'',m,0%R; split => //.
 case: H_reach=> t Ht.
 exists (rcons t [` Hv]).
 rewrite foldm_rcons_some; exists (q', m');split => //.
 by rewrite /nextVASS /= E eqxx E'. 
Qed.
 
Lemma VASS_of_VAS_reachable (c0 c: confVASS dim state) :
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) (VAS_of_VASS_m c) ->
 reachable (@nextVASS _ _ vass) c0 c.
Proof. 
 case: c => q m /VASS_of_VAS_reachable' [q' [m' [i []]]].
 rewrite /VAS_of_VASS_m.
 move/(congr1 (@vsplit _ _ _)). rewrite !vcatK => -[<-].
 by move/vs_inj => [->].
Qed.

Lemma reachable_VASS_VAS (c0 c: confVASS dim state) :
 reachable (@nextVASS _ _ vass) c0 c <-> 
 reachable (@nextVAS _ VAS_of_VASS_t) (VAS_of_VASS_m c0) (VAS_of_VASS_m c).
Proof. 
 split; first exact: VAS_of_VASS_reachable.
 exact: VASS_of_VAS_reachable.
Qed.

End VASS2VAS.