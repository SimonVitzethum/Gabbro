/- C08: small kernel witnesses for the nontrivial software-call pre. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T10Run

@[expose] public section

namespace Gabbro.Grammatik

open Zielsatz

namespace CallSiteZeuge

def sig : Signatur Empty Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One caller and one software item; no memory, locks or providers. The
    parameter range contains both a passing value and the failing zero. -/
def decl : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun e => nomatch e
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun e => nomatch e
  eigner := fun e => nomatch e
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => sig
  eigner_nie_erzeugt := fun _ e => nomatch e
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => [.int 0 1]
  aerg := fun _ => none
  aschreibt := fun _ e => nomatch e
  agschreibt := fun _ e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ e => nomatch e
  ggeteilt_bewacht := fun e => nomatch e
  axHerkunft := fun _ => some .software
  axBeleg := fun _ => none

def contract : CallContract decl (decl.asignatur ()) where
  pre := .not (.eq (.var .here) (.lit 0))
  post := .tru

def args (b : Bool) : Args decl [] [] (decl.aparams ()) :=
  .cons (if b then .widen (by decide) (by decide) (.lit 1)
    else .widen (by decide) (by decide) (.lit 0)) .nil

def rho (b : Bool) : Env decl (decl.aparams ()) :=
  .cons (if b then ⟨1, by decide, by decide⟩ else ⟨0, by decide, by decide⟩) .nil

def call (b : Bool) : Stmt decl (vertragVon decl ()) false [] [] [] :=
  .axiomCall () (args b) rfl (fun e => nomatch e) (fun e => nomatch e)
    (fun e => nomatch e) (fun e => nomatch e)

def tail (b : Bool) : Endblock decl (vertragVon decl ()) false [] [] :=
  .cons (call b) (.ret .empty (by rfl))

/-- The second argument can be changed to zero without changing any type. -/
def program (b : Bool) : Programm decl where
  invariante := fun e => nomatch e
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .cons (call true) (tail b)
  axVertrag := fun _ => contract

def memory : Speicher decl where
  slots := fun e => nomatch e
  globs := fun e => nomatch e

def world : World decl := memory.welt []

/-- The first answer world; subsequent answers retain the trace at their own key. -/
def answer : World decl := world.fragt (.inl ())

def oracle : Orakel decl where
  wirktL := fun _ σ _ => ({ σ with spur := [] }, 0)
  regLiesL := fun e => nomatch e
  regSchreib := fun e => nomatch e
  sichtbarL := fun e => nomatch e

def unit : Einheit decl where
  P := program true
  S := SperrInv.leer decl
  Q := fun _ _ _ => true
  starts := [⟨(), .nil⟩]
  sp0 := memory

def key1 : World decl := world.fragt (.inl ())
def key2 : World decl := answer.fragt (.inl ())

def record (σ : World decl) (b : Bool) : AxEintrag decl :=
  ⟨(), σ, rho b, (σ, 0)⟩

def history (b : Bool) : List (AxEintrag decl) :=
  [record key1 true, record key2 b]

theorem keys_distinct : key1 ≠ key2 := by
  intro h
  have hl := congrArg (fun σ : World decl => σ.spur.length) h
  change 1 = 2 at hl
  omega

theorem pre_true (σ : World decl) : AxVor (program true).axVertrag () σ (rho true) := by
  rfl

theorem pre_false (σ : World decl) : ¬ AxVor (program true).axVertrag () σ (rho false) := by
  intro h
  change false = true at h
  cases h

theorem history_good : CallSitePflichtFremd (program true).axVertrag (history true) := by
  intro a σ ρ x hmem hsw
  cases a
  have h : (⟨(), σ, ρ, x⟩ : AxEintrag decl) = record key1 true ∨
      (⟨(), σ, ρ, x⟩ : AxEintrag decl) = record key2 true := by
    simpa only [history, List.mem_cons, List.not_mem_nil, or_false] using hmem
  rcases h with h | h
  all_goals
    have hr := congrArg
      (fun p : World decl × Env decl (decl.aparams ()) × (World decl × Int) => p.2.1)
      (eq_of_heq (Sigma.mk.inj h).2)
    change ρ = rho true at hr
    rw [hr]
    exact pre_true _

theorem history_bad : ¬ CallSitePflichtFremd (program true).axVertrag (history false) := by
  intro h
  exact pre_false key2 (h () key2 (rho false) (key2, 0)
    (by simp only [history, record, List.mem_cons, List.not_mem_nil, or_false, or_true]) rfl)

theorem foreign : ForeignPflicht unit oracle [] where
  vertrag := by
    intro a hsw σ ρ hpre v hv
    rfl
  dekodiert := by
    intro a hsw σ ρ
    change some (Sum.inl ()) ≠ none
    intro h
    cases h
  klauseln := by
    intro n
    exact Fin.elim0 n
  anbieter := providerRealisiert_nil oracle

theorem link (b : Bool) : PasstA oracle (history b) := by
  intro a σ ρ x hm
  have h : (⟨a, σ, ρ, x⟩ : AxEintrag decl) = record key1 true ∨
      (⟨a, σ, ρ, x⟩ : AxEintrag decl) = record key2 b := by
    simpa only [history, List.mem_cons, List.not_mem_nil, or_false] using hm
  rcases h with h | h
  all_goals
    have hσ := congrArg (fun e : AxEintrag decl => e.2.1) h
    have hx := congrArg (fun e : AxEintrag decl => e.2.2.2) h
    change (σ, 0) = x
    dsimp only [record] at hσ hx
    rw [hσ]
    exact hx.symm

theorem history_provenance (b : Bool) : SchluesselHerkunft (history b) := by
  intro e hm
  have he : e = record key1 true ∨ e = record key2 b := by
    simpa only [history, List.mem_cons, List.not_mem_nil, or_false] using hm
  rcases he with he | he
  · subst e
    exact ⟨world, rfl⟩
  · subst e
    exact ⟨answer, rfl⟩

/-- Both records use the actual T10 contract and declared-ensures transports. -/
theorem posts (σ : World decl) (hm : record σ true ∈ history true) :
    AxNach unit.P.axVertrag () σ (rho true) σ () ∧ unit.Q () σ () = true := by
  have fit : einpassenErg oracle.zeiger (decl.aerg ()) (0 : Int) = some () := rfl
  exact ⟨vertragANeu_sw_of_foreign foreign history_good (link true) (history_provenance true) hm rfl fit,
    qAmDatensatz_of_foreign foreign history_good (link true) (history_provenance true)
      (fun _ _ _ _ _ _ _ => rfl) hm rfl fit⟩

def start (b : Bool) : RufMaschineG decl :=
  RufStartG (program b) memory (fun _ => ⟨(), .nil⟩)

def afterFirst (b : Bool) : RufMaschineG decl where
  speicher := memory
  faeden := rufUpdateG (start b).faeden 0
    { stapel := []
      kopf :=
        { f := ()
          rho := .nil
          s0 := world
          rest := ⟨false, [], [], .nil, .ende (tail b)⟩ }
      spur := answer.spur
      log := ((start b).faeden 0).log }
  lauf := rufEigenG 0 [.fremd (.inl ())]
  start := world

/-- The first foreign call really fires; the second call is its continuation. -/
theorem first_step (b : Bool) :
    RufSchrittG (program b) oracle 0 (start b) 0 (afterFirst b) := by
  refine RufSchrittG.blatt (start b) 0 false [] [] [] (call true) (tail b) .nil
    rfl rfl ?_ answer .nil [.fremd (.inl ())] rfl rfl ?_
  · intro L
    exact nomatch L
  · intro L
    exact nomatch L

/-- The second call also fires, including the well-typed zero-argument case.
    The machine has no precondition check; rejecting that case is user duty. -/
theorem second_step (b : Bool) :
    ∃ M : RufMaschineG decl, RufSchrittG (program b) oracle 0 (afterFirst b) 0 M := by
  refine ⟨_, RufSchrittG.blatt (afterFirst b) 0 false [] [] [] (call b)
    (.ret .empty (by rfl)) .nil rfl rfl ?_ key2 .nil [.fremd (.inl ())] ?_ ?_ ?_⟩
  · intro L
    exact nomatch L
  · cases b <;> rfl
  · cases b <;> rfl
  · intro L
    exact nomatch L

theorem record_sites (b : Bool) : ∀ e ∈ history b,
    CallSiteErreichbar (program b) oracle 0 (fun _ => False) (start b)
      ⟨e.1, e.2.1, e.2.2.1⟩ := by
  intro e hm
  have he : e = record key1 true ∨ e = record key2 b := by
    simpa only [history, List.mem_cons, List.not_mem_nil, or_false] using hm
  rcases he with he | he
  · subst e
    exact ⟨start b, memory, 0, .start, fun c _ => traegerGleich_refl _ c, rfl⟩
  · subst e
    exact ⟨afterFirst b, memory, 0,
      .schritt _ _ 0 .start (gx_aus_g (first_step b)),
      fun c _ => traegerGleich_refl _ c, by
        simp only [RufMaschineG.foreignCallKey, afterFirst, rufUpdateG_self]
        cases b <;> rfl⟩

/-- A reachable second call with argument zero refutes the run duty itself. -/
theorem run_bad : ¬ CallSitePflichtLauf (program false) oracle 0 (fun _ => False) (start false) := by
  intro h
  exact pre_false key2 (h () key2 (rho false)
    (record_sites false (record key2 false)
      (by simp only [history, List.mem_cons, List.not_mem_nil, or_false, or_true])) rfl)

end CallSiteZeuge

/-- ZEUGE: one software item, a satisfiable and falsifiable pre, two distinct
    recorded question keys, the duty at both calls, and both replay posts. -/
theorem callSitePflicht_zeuge :
    CallSiteZeuge.decl.axHerkunft () = some .software ∧
    CallSiteZeuge.key1 ≠ CallSiteZeuge.key2 ∧
    CallSitePflichtFremd CallSiteZeuge.unit.P.axVertrag (CallSiteZeuge.history true) ∧
    ¬ CallSitePflichtFremd CallSiteZeuge.unit.P.axVertrag (CallSiteZeuge.history false) ∧
    ForeignPflicht CallSiteZeuge.unit CallSiteZeuge.oracle [] ∧
    ∀ σ : World CallSiteZeuge.decl,
      CallSiteZeuge.record σ true ∈ CallSiteZeuge.history true →
      AxNach CallSiteZeuge.unit.P.axVertrag () σ (CallSiteZeuge.rho true)
        σ () ∧ CallSiteZeuge.unit.Q () σ () = true := by
  refine ⟨rfl, CallSiteZeuge.keys_distinct, CallSiteZeuge.history_good,
    CallSiteZeuge.history_bad, CallSiteZeuge.foreign, CallSiteZeuge.posts⟩

/-- Empty software histories use precisely the existing nil transport. -/
theorem callSitePflichtFremd_leer_zeuge :
    CallSitePflichtFremd CallSiteZeuge.unit.P.axVertrag [] :=
  callSitePflichtFremd_nil _

/-- The history witness has two actual machine calls and reachable keys;
    changing only the second argument to zero refutes the run duty. -/
theorem callSitePflicht_run_zeuge :
    (∃ M : RufMaschineG CallSiteZeuge.decl,
      RufSchrittG (CallSiteZeuge.program true) CallSiteZeuge.oracle 0
        (CallSiteZeuge.afterFirst true) 0 M) ∧
    (∀ e ∈ CallSiteZeuge.history true,
      CallSiteErreichbar (CallSiteZeuge.program true) CallSiteZeuge.oracle 0 (fun _ => False)
        (CallSiteZeuge.start true) ⟨e.1, e.2.1, e.2.2.1⟩) ∧
    ¬ CallSitePflichtLauf (CallSiteZeuge.program false) CallSiteZeuge.oracle 0 (fun _ => False)
      (CallSiteZeuge.start false) :=
  ⟨CallSiteZeuge.second_step true, CallSiteZeuge.record_sites true, CallSiteZeuge.run_bad⟩

end Gabbro.Grammatik
