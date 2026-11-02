module

public import Grammatik.Logik.Ruf.Schnittstellen.Kandidaten
public import Grammatik.Logik.Ruf.Schnittstellen.Lokal
public import Grammatik.Logik.Ruf.Schnittstellen.Rufstelle
public import Grammatik.Logik.Ruf.Schnittstellen.Hoare

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
  requires := fun f => if f then .le (.lit 1) (.var .here) else .le (.lit 2) (.var .here)
  ensures := fun f => if f then .eq (.var .here) (.var (.there .here))
    else .le (.var (.there .here)) (.var .here)
  rumpf := fun _ => .ret (.val (.var .here)) (List.Perm.refl [])
  ptrVertrag := fun _ =>
    ⟨.le (.lit 3) (.var .here), .le (.var (.there .here)) (.var .here)⟩

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
  exact ⟨rfl, by intro h; cases h, rfl, by intro h; cases h⟩

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
  exact ⟨rfl, by intro h; cases h, rfl, by intro h; cases h, rfl, rfl, rfl⟩

/-- One bad second target refutes the universal duty even though the first
    target and all structural signatures are unchanged. -/
def badSecondTarget : Programm decl :=
  { prog with ensures := fun f => if f then prog.ensures f else .tru }

theorem weaker_second_target_post_refused : ¬ PtrVerfeinert badSecondTarget := by
  intro h
  have hp := (h false 0 rfl).2 entry later arguments ⟨0, by decide, by decide⟩ rfl rfl
  change false = true at hp
  cases hp

/-- Requiring equality as the interface post reverses covariance for the
    lower-bound target: a permitted concrete result of 4 is a counterexample. -/
def strongerInterfacePost : Programm decl :=
  { prog with ptrVertrag := fun _ =>
    ⟨.le (.lit 3) (.var .here), .eq (.var .here) (.var (.there .here))⟩ }

theorem stronger_interface_post_refused : ¬ PtrVerfeinert strongerInterfacePost := by
  intro h
  have hp := (h false 0 rfl).2 entry later arguments ⟨4, by decide, by decide⟩ rfl rfl
  change false = true at hp
  cases hp

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
  have ht := hoare_callInd (V := vertragVon decl true) prog oracle 0 handler
    handler_contracts refinement operand operands permissions rfl entry arguments
  have hp := ht entry arguments ⟨rfl, rfl, rfl⟩ entry arguments rfl
  exact ⟨handler_contracts, refinement, rfl, hp.2⟩

end Gabbro.Grammatik.C06

#print axioms Gabbro.Grammatik.PtrVerfeinert
#print axioms Gabbro.Grammatik.ptrVerfeinert_iff_kandidaten
#print axioms Gabbro.Grammatik.hoare_callInd
#print axioms Gabbro.Grammatik.C06.refinement
#print axioms Gabbro.Grammatik.C06.hoare_callInd_zeuge
