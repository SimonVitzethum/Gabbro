module

public import Grammatik.Logik.Ruf.Schnittstellen.Kandidaten
public import Grammatik.Logik.Ruf.Schnittstellen.Einschluss
public import Grammatik.Logik.Ruf.Schnittstellen.Lokal
public import Grammatik.Logik.Ruf.Schnittstellen.Rufstelle
public import Grammatik.Logik.Ruf.Schnittstellen.Hoare
public import Grammatik.Logik.Ruf.Schnittstellen.Prefix
public import Grammatik.Logik.Ruf.Schnittstellen.Pruefung

@[expose] public section

namespace Gabbro.Grammatik.C06

/-- Two targets share this scalar signature; the local table is read-only. -/
def sig : Signatur Unit Empty Empty Empty where
  params := [.int 0 10]
  erg := some (.int 0 10)
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def decl : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 10
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun _ => 0
  sigNr := fun _ => sig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by cases h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- `true` requires 1 and ensures equality; `false` requires 2 and ensures a
    lower bound. The common interface requires 3 and ensures the lower bound.
    Predicate texts differ, and both implications are strict on some values. -/
def prog : Programm decl where
  invariante := fun i => nomatch i
  requires := fun (f : Bool) => if f then .le (.lit 1) (.var .here) else .le (.lit 2) (.var .here)
  ensures := fun (f : Bool) => if f then .eq (.var .here) (.var (.there .here))
    else .le (.var (.there .here)) (.var .here)
  rumpf := fun _ => .ret (.val (.var .here)) (List.Perm.refl [])
  ptrVertrag := fun _ =>
    { pre := .le (.lit 3) (.var .here), post := .le (.var (.there .here)) (.var .here) }

/-- O43 holds for every admitted pair and arbitrary worlds, arguments/results,
    rather than just the particular returning bodies of this fixture. -/
theorem refinement : PtrVerfeinert prog := by
  intro f n hf
  cases f
  · constructor
    · intro s0 ρ hp
      change decide (3 ≤ (ρ.get .here).n) = true at hp
      change decide (2 ≤ (ρ.get .here).n) = true
      simp only [decide_eq_true_eq] at hp ⊢
      omega
    · intro s0 s1 ρ v _ hv
      change decide ((ρ.get .here).n ≤ v.n) = true at hv ⊢
      exact hv
  · constructor
    · intro s0 ρ hp
      change decide (3 ≤ (ρ.get .here).n) = true at hp
      change decide (1 ≤ (ρ.get .here).n) = true
      simp only [decide_eq_true_eq] at hp ⊢
      omega
    · intro s0 s1 ρ v _ hv
      change decide (v.n = (ρ.get .here).n) = true at hv
      change decide ((ρ.get .here).n ≤ v.n) = true
      simp only [decide_eq_true_eq] at hv ⊢
      omega

def world (k : Wert decl (.int 0 10)) : World decl where
  slots := fun _ _ _ => k
  globs := fun e => nomatch e
  spur := []

def entry : World decl := world ⟨0, by decide, by decide⟩
def later : World decl := world ⟨7, by decide, by decide⟩
def arguments : Env decl sig.params := .cons ⟨3, by decide, by decide⟩ .nil
def pointer : Wert decl (.fnptr 0) := ⟨true, rfl⟩
def operand : Expr decl sig.params [] (.fnptr 0) := .fnref true 0 rfl
def operands : Args decl sig.params [] sig.params := .cons (.var .here) .nil

theorem ptrVerfeinert_zeuge :
    PtrVerfeinert prog ∧ decl.passt true 0 = true ∧ decl.passt false 0 = true ∧
      (prog.ptrVertrag 0).preHolds entry arguments ∧
      (prog.ptrVertrag 0).postHolds entry later arguments ⟨3, by decide, by decide⟩ :=
  ⟨refinement, rfl, rfl, rfl, rfl⟩

theorem ptrRufPflicht_req_zeuge :
    PtrVerfeinert prog ∧ PtrRufPflicht prog operand operands entry arguments ∧
      ReqAmEintritt prog true entry (umsig pointer.property arguments) :=
  ⟨refinement, rfl, PtrVerfeinert.req refinement pointer entry arguments rfl⟩

/-- Neither target contract is collapsed into the common interface. -/
theorem concrete_contracts_differ :
    ReqAmEintritt prog true entry (.cons ⟨1, by decide, by decide⟩ .nil) ∧
    ¬ ReqAmEintritt prog false entry (.cons ⟨1, by decide, by decide⟩ .nil) ∧
    EnsAmRueck prog false entry later arguments ⟨4, by decide, by decide⟩ ∧
    ¬ EnsAmRueck prog true entry later arguments ⟨4, by decide, by decide⟩ := by
  exact ⟨rfl, (by intro h; cases h), rfl, (by intro h; cases h)⟩

/-- A true interface pre does not license either target's stronger requires. -/
def unguarded : Programm decl :=
  { prog with ptrVertrag := fun n => CallContract.trivial decl (decl.sigNr n) }

theorem default_does_not_discharge_O43 : ¬ PtrVerfeinert unguarded := by
  intro h
  have hr := (h true 0 rfl).1 entry (.cons ⟨0, by decide, by decide⟩ .nil) rfl
  change false = true at hr
  cases hr

theorem inventory_functions (f : decl.Fn) : f ∈ [false, true] := by
  cases f
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem inventory_signatures (f : decl.Fn) (n : Nat) (hf : decl.passt f n = true) :
    n ∈ [0] := by
  have hn : 0 = n := of_decide_eq_true hf
  subst n
  exact List.mem_cons_self

theorem ptrVerfeinert_iff_kandidaten_zeuge :
    ptrKandidaten decl [false, true] [0] = [(false, 0), (true, 0)] ∧
      (∀ (f : decl.Fn) (n : Nat), (f, n) ∈ ptrKandidaten decl [false, true] [0] →
        ∀ hf : decl.passt f n = true, PtrZielVerfeinert prog f n hf) :=
  ⟨rfl, (ptrVerfeinert_iff_kandidaten prog [false, true] [0]
    inventory_functions inventory_signatures).mp refinement⟩

/-- This post reads `old(table[0])` despite the signature writing no table. -/
def oldContract : CallContract decl sig where
  pre := .le (.slot () () (.lit 0) (by intro _ h; cases h)) (.var .here)
  post := .eq (.var .here) (.oldS () () (.lit 0) (by intro _ h; cases h))

theorem old_world_and_read_only_zeuge :
    oldContract.preHolds entry arguments ∧ ¬ oldContract.preHolds later arguments ∧
    oldContract.postHolds entry later arguments ⟨0, by decide, by decide⟩ ∧
    ¬ oldContract.postHolds later later arguments ⟨0, by decide, by decide⟩ ∧
    oldContract.orte = [.inl (), .inl ()] ∧ sig.schreibt () = false ∧
    oldContract.atomicFreeB (fun _ => true) = false := by
  exact ⟨rfl, (by intro h; cases h), rfl, (by intro h; cases h), rfl, rfl, rfl⟩

/-- One bad second target refutes the universal duty even though the first
    target and all structural signatures are unchanged. -/
def badSecondTarget : Programm decl :=
  { prog with ensures := fun (f : Bool) => if f then prog.ensures f else .tru }

theorem weaker_second_target_post_refused : ¬ PtrVerfeinert badSecondTarget := by
  intro h
  have hp := (h false 0 rfl).2 entry later arguments ⟨0, by decide, by decide⟩ rfl rfl
  change false = true at hp
  cases hp

/-- Requiring equality as the interface post reverses covariance for the
    lower-bound target: a permitted concrete result of 4 is a counterexample. -/
def strongerInterfacePost : Programm decl :=
  { prog with ptrVertrag := fun _ =>
    { pre := .le (.lit 3) (.var .here), post := .eq (.var .here) (.var (.there .here)) } }

theorem stronger_interface_post_refused : ¬ PtrVerfeinert strongerInterfacePost := by
  intro h
  have hp := (h false 0 rfl).2 entry later arguments ⟨4, by decide, by decide⟩ (by rfl) (by rfl)
  change false = true at hp
  cases hp

/-- A target whose requires is stronger than the interface pre is refused:
    `true` needs `5 ≤ x` but the interface only promises `3 ≤ x`
    (counterexample `x = 4`). -/
def strongerTargetPre : Programm decl :=
  { prog with requires := fun (f : Bool) => if f then .le (.lit 5) (.var .here) else prog.requires f }

theorem stronger_target_pre_refused : ¬ PtrVerfeinert strongerTargetPre := by
  intro h
  have hr := (h true 0 rfl).1 entry (.cons ⟨4, by decide, by decide⟩ .nil) (by rfl)
  change false = true at hr
  cases hr

/-- Reversed implication is refused, both ways. The target pre does not imply
    the interface pre (`x = 1` satisfies `true`'s requires but not the
    interface `3 ≤ x`) ... -/
theorem reversed_pre_refused :
    ¬ (∀ (s0 : World decl) (ρ : Env decl sig.params),
      ReqAmEintritt prog true s0 (umsig pointer.property ρ) →
      (prog.ptrVertrag 0).preHolds s0 ρ) := by
  intro h
  have hr := h entry (.cons ⟨1, by decide, by decide⟩ .nil) (by rfl)
  change false = true at hr
  cases hr

/-- ... and the interface post does not imply the target ensures (`x = 4`
    satisfies the interface `param ≤ result` but not `true`'s equality). -/
theorem reversed_post_refused :
    ¬ (∀ (s0 s1 : World decl) (ρ : Env decl sig.params) (v : ErgVal decl (decl.erg true)),
      (prog.ptrVertrag 0).postHolds s0 s1 ρ (ptrResult pointer.property v) →
      EnsAmRueck prog true s0 s1 (umsig pointer.property ρ) v) := by
  intro h
  have hp := h entry later arguments ⟨4, by decide, by decide⟩ (by rfl)
  change false = true at hp
  cases hp

/-- The conjunct reformulation fires on the jointly inhabited fixture: every
    interface-pre conjunct (here: the single `3 ≤ x`) implies the selected
    target's requires. -/
theorem refinement_konjunkt_zeuge :
    (∀ (s0 : World decl) (ρ : Env decl sig.params),
      (∀ c ∈ konjunkte ((prog.ptrVertrag 0).pre), wahr? (eval s0 c s0 ρ) = true) →
      ReqAmEintritt prog true s0 (umsig pointer.property ρ)) :=
  ((ptrZielVerfeinert_konjunkt prog true 0 pointer.property).mp
    (refinement true 0 pointer.property)).1

/-- A contract-respecting abstract handler; it is not a source interpreter. -/
def handler (f : decl.Fn) (σ : World decl) (ρ : Env decl (decl.params f)) : RufAusgang f :=
  .ok σ (ρ.get .here)

theorem handler_contracts : RespektiertVertraege prog handler := by
  intro f σ ρ _ s1 v hout
  change RufAusgang.ok σ (ρ.get .here) = RufAusgang.ok s1 v at hout
  cases hout
  cases f
  · change decide ((ρ.get .here).n ≤ (ρ.get .here).n) = true
    exact decide_eq_true (Int.le_refl _)
  · change decide ((ρ.get .here).n = (ρ.get .here).n) = true
    exact decide_eq_true rfl

def oracle : Orakel decl where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun g => nomatch g

def permissions : RufPasst decl (vertragVon decl true) sig [] where
  hw := fun _ h => h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], List.Sublist.refl []⟩
  hh := fun L => nomatch L

def statement : Stmt decl (vertragVon decl true) false sig.params [] [] :=
  .callInd operand operands permissions rfl

/-- All hypotheses of the indirect Hoare rule hold jointly, the call returns
    result 3, and both the selected target and interface contracts survive. -/
theorem hoare_callInd_zeuge :
    RespektiertVertraege prog handler ∧ PtrVerfeinert prog ∧
    execStmt oracle 0 handler statement entry arguments = Ausgang.ok entry arguments ∧
    (∃ v, handler true entry (umsig pointer.property arguments) = RufAusgang.ok entry v ∧
      EnsAmRueck prog true entry entry (umsig pointer.property arguments) v ∧
      (prog.ptrVertrag 0).postHolds entry entry arguments (ptrResult pointer.property v)) := by
  have ht := hoare_callInd (V := vertragVon decl true) (l := false) prog oracle 0 handler
    handler_contracts refinement operand operands permissions rfl entry arguments
  have hp := ht entry arguments ⟨rfl, rfl, rfl⟩ entry arguments rfl
  exact ⟨handler_contracts, refinement, rfl, hp.2⟩

/-- Prefix replay fires on the jointly inhabited call: the interface pre at
    the operand-entry world replays across a reflexive agreement. -/
theorem ptrPre_prefix_zeuge :
    (prog.ptrVertrag 0).preHolds entry arguments ∧
    (prog.ptrVertrag 0).preHolds entry arguments := by
  exact ⟨rfl,
    Gabbro.Grammatik.ptrPre_prefix prog entry entry arguments rfl
      (GleichAuf.refl _ _)⟩

/-- The local caller duty replays across the prefix and still selects the
    same target with its concrete requires. -/
theorem ptrPflicht_prefix_zeuge :
    PtrRufPflicht prog operand operands entry arguments ∧
    PtrRufPflicht prog operand operands entry arguments ∧
      ReqAmEintritt prog true entry (umsig pointer.property arguments) := by
  have h : PtrRufPflicht prog operand operands entry arguments := rfl
  have hrep := Gabbro.Grammatik.ptrPflicht_prefix prog operand operands entry entry
    arguments h (GleichAuf.refl _ _) rfl
  exact ⟨h, hrep, Gabbro.Grammatik.PtrRufPflicht.req refinement hrep⟩

/-- The replayed duty opens the concrete gate at the same world. -/
theorem ptrTor_prefix_zeuge :
    torRuf prog handler true entry (umsig pointer.property arguments) =
      handler true entry (umsig pointer.property arguments) := by
  have h := Gabbro.Grammatik.ptrTor_prefix_stmt refinement handler operand operands
    entry entry arguments rfl (GleichAuf.refl _ _) rfl
  exact h

/-- Indirect closure is already decided: every admitted target of an
    indirect site is in the closed set. Both same-shape targets are admitted
    at `0`; the closed set contains the selected one, with all premises
    (closed graph, site admission, conformance, member list) jointly. -/
theorem abgK_indirekt_schliesst_zeuge :
    (fun _ : decl.Fn => true) true = true :=
  Gabbro.Grammatik.abgK_indirekt_schliesst (P := prog) (fs := [false, true])
    (f := true) (n := 0) (g := true)
    (Z := fun _ => true) (fun f _ => by cases f <;> rfl) rfl rfl rfl
    inventory_functions


/-- Finite interfaces: nontrivial only at `0`, trivial elsewhere. The table
    `[0]` carries every nontrivial contract, so the finite check decides the
    infinite freeness duty. Footprints are empty (value-only predicates), so
    no shared atomic is hidden. -/
def progFin : Programm decl :=
  { prog with ptrVertrag := fun
      | 0 => prog.ptrVertrag 0
      | n + 1 => CallContract.trivial decl (decl.sigNr (n + 1)) }

theorem progFin_trivial_ausserhalb (n : Nat) (h : n ∉ [0]) :
    (progFin.ptrVertrag n).pre.orte = [] ∧ (progFin.ptrVertrag n).post.orte = [] := by
  cases n with
  | zero => exact absurd List.mem_cons_self h
  | succ k => exact ⟨rfl, rfl⟩

theorem ptrVertragsFreiB_zeuge :
    ptrVertragsFreiB progFin [0] (.inl ()) = true ∧
    PtrVertragsFrei progFin (.inl ()) := by
  exact ⟨rfl,
    Gabbro.Grammatik.ptrVertragsFreiB_ok progFin_trivial_ausserhalb rfl⟩

/-- A full callback cycle through a parameter: the interface pre at the
    actual arguments, the selected target's concrete requires and ensures,
    and the interface post on the transported result. Table reads flow
    through `oldContract`-style orte (below) and rights through `SigPasst`
    (source probes `param_ok`/`rechte_ok`). -/
theorem callback_param_table_result_zeuge :
    (prog.ptrVertrag 0).preHolds entry arguments ∧
    ReqAmEintritt prog true entry (umsig pointer.property arguments) ∧
    EnsAmRueck prog true entry later (umsig pointer.property arguments)
      ⟨3, by decide, by decide⟩ ∧
    (prog.ptrVertrag 0).postHolds entry later arguments
      (ptrResult pointer.property ⟨3, by decide, by decide⟩) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A proved implementation behind the interface (the thunk stand-in for a
    foreign body): it respects every contract, refines the interface, and
    the interface pre holds at the call arguments. -/
theorem proved_foreign_thunk_zeuge :
    RespektiertVertraege prog handler ∧ PtrVerfeinert prog ∧
      (prog.ptrVertrag 0).preHolds entry arguments :=
  ⟨handler_contracts, refinement, rfl⟩

/-- A contract with a nonempty footprint (table reads in both halves):
    each half flows into the whole, and emptiness of a shared carrier splits
    per half, so no shared atomic hides in either. -/
theorem nonempty_effects_flow_zeuge :
    oldContract.pre.orte = [Sum.inl ()] ∧
    oldContract.post.orte = [Sum.inl ()] ∧
    oldContract.pre.orte ⊆ oldContract.orte ∧
    oldContract.post.orte ⊆ oldContract.orte ∧
    (∀ c ∈ oldContract.pre.orte, (fun _ : decl.Tab ⊕ decl.Glob => false) c = false) ∧
    (∀ c ∈ oldContract.post.orte, (fun _ : decl.Tab ⊕ decl.Glob => false) c = false) := by
  refine ⟨rfl, rfl, fun _ h => List.mem_append_left _ h,
    fun _ h => List.mem_append_right _ h, fun _ _ => rfl, fun _ _ => rfl⟩

/-- A forged image pointer is refused: no function conforms to signature
    number `1`, so no `fnptr 1` value selects `true`. -/
theorem forged_image_pointer_refused :
    decl.passt true 1 = false ∧ ¬ ∃ v : Wert decl (.fnptr 1), v.val = true := by
  refine ⟨rfl, fun h => ?_⟩
  obtain ⟨⟨f, hf⟩, hv⟩ := h
  subst hv
  exact absurd hf (by decide)

/-- Evaluating the interface post at the wrong entry world is refused: the
    `old`-reading post holds from `entry` but not from `later` for the same
    result, so the current world cannot stand in for the entry world. -/
theorem old_current_mixup_refused :
    oldContract.postHolds entry later arguments ⟨0, by decide, by decide⟩ ∧
      ¬ oldContract.postHolds later later arguments ⟨0, by decide, by decide⟩ :=
  ⟨rfl, by intro h; cases h⟩

/-- A contract reading a shared-atomic carrier is detected: with the carrier
    shared, `atomicFreeB` is `false`, so the interface is not admittable as
    atomically free. -/
theorem hidden_shared_atomic_refused :
    oldContract.atomicFreeB (fun _ => true) = false :=
  rfl

/-- At program level: a unit whose interface reads a shared atomic is not
    `PtrVertragsFrei` there. -/
def badAtomProg : Programm decl :=
  { prog with ptrVertrag := fun _ => oldContract }

theorem hidden_shared_atomic_prog_refused :
    ¬ PtrVertragsFrei badAtomProg (.inl ()) := by
  intro h
  exact (h 0).1 (by decide)

end Gabbro.Grammatik.C06

#print axioms Gabbro.Grammatik.PtrVerfeinert
#print axioms Gabbro.Grammatik.ptrVerfeinert_iff_kandidaten
#print axioms Gabbro.Grammatik.hoare_callInd
#print axioms Gabbro.Grammatik.C06.refinement
#print axioms Gabbro.Grammatik.C06.hoare_callInd_zeuge
#print axioms Gabbro.Grammatik.ptrPre_prefix
#print axioms Gabbro.Grammatik.ptrPflicht_prefix
#print axioms Gabbro.Grammatik.ptrVertragsFreiB_ok
#print axioms Gabbro.Grammatik.abgK_indirekt_schliesst
#print axioms Gabbro.Grammatik.C06.ptrPre_prefix_zeuge
#print axioms Gabbro.Grammatik.C06.ptrVertragsFreiB_zeuge
#print axioms Gabbro.Grammatik.C06.stronger_target_pre_refused
#print axioms Gabbro.Grammatik.C06.reversed_pre_refused
#print axioms Gabbro.Grammatik.C06.reversed_post_refused
#print axioms Gabbro.Grammatik.C06.refinement_konjunkt_zeuge
#print axioms Gabbro.Grammatik.C06.callback_param_table_result_zeuge
#print axioms Gabbro.Grammatik.C06.proved_foreign_thunk_zeuge
#print axioms Gabbro.Grammatik.C06.nonempty_effects_flow_zeuge
#print axioms Gabbro.Grammatik.C06.forged_image_pointer_refused
#print axioms Gabbro.Grammatik.C06.old_current_mixup_refused
#print axioms Gabbro.Grammatik.C06.hidden_shared_atomic_refused
#print axioms Gabbro.Grammatik.C06.hidden_shared_atomic_prog_refused
