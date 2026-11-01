module

public import Grammatik.Zielsatz.Atomar.AtomarPflicht
public import Grammatik.Speichermodell.Atomar.AtomarSem
public import Grammatik.Speichermodell.Atomar.AtomarRec
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrt
public import Grammatik.Zielsatz.Atomar.AtomarAkzeptiertZeuge
public import Grammatik.GabbroV.GvAtomRely
public import Grammatik.GabbroV.GvAtomKoerper.Teil1

@[expose] public section

namespace Gabbro.Grammatik.GvAtomKoerper
open Gabbro.Grammatik.Zielsatz NIZeuge AtomarXZeuge
variable {D : Deklaration}

theorem hBeide_pin0 (s₁ s₂ : Speicher nD) (w : World nD) :
    pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂ [] w = w := by
  unfold pinA
  rw [if_neg (by decide), if_neg (by decide)]

/-- `leseA` through the pin at the store read (fires on the folded form). -/
theorem hBeide_lese1 (s₁ s₂ : Speicher nD) (w : World nD) (Λ : List (Res nD)) :
    leseA (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) w Λ [.inr NGlob.konfig]
    = mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        (w.lese Λ [.inr NGlob.konfig]) s₁ := by
  unfold leseA
  rw [hBeide_pin1]

/-- `leseA` through the pin at the test read. -/
theorem hBeide_lese2 (s₁ s₂ : Speicher nD) (w : World nD) (Λ : List (Res nD)) :
    leseA (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) w Λ
      [.inr NGlob.konfig, .inl NTab.tabB]
    = mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
        [.inr NGlob.konfig, .inl NTab.tabB] (w.lese Λ [.inr NGlob.konfig, .inl NTab.tabB]) s₂ := by
  unfold leseA
  rw [hBeide_pin2]

/-- `leseA` through the pin off both reads is the plain read. -/
theorem hBeide_lese0 (s₁ s₂ : Speicher nD) (w : World nD) (Λ : List (Res nD)) :
    leseA (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
      [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) w Λ []
    = w.lese Λ [] := by
  unfold leseA
  rw [hBeide_pin0]

/-- The pinned store value: `s₁`'s `konfig`. -/
theorem hBeide_g1 (s₁ : Speicher nD) (w : World nD) :
    (mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig] w s₁).globs
      NGlob.konfig = s₁.globs NGlob.konfig :=
  mischT_globs _ _ w s₁ _ ⟨List.mem_cons_self, hPBeide_konfig_geteilt⟩

/-- The pinned test value: `s₂`'s `konfig`. -/
theorem hBeide_g2 (s₂ : Speicher nD) (w : World nD) :
    (mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
      [.inr NGlob.konfig, .inl NTab.tabB] w s₂).globs NGlob.konfig
    = s₂.globs NGlob.konfig :=
  mischT_globs _ _ w s₂ _ ⟨List.mem_cons_self, hPBeide_konfig_geteilt⟩

/-- The test's slot read sees the live world (`tabB` is never shared). -/
theorem hBeide_slot (s₂ : Speicher nD) (w : World nD) (k : Int) :
    (mischT (GeteiltA hPBeide [NFn.kern, NFn.zaehlB])
      [.inr NGlob.konfig, .inl NTab.tabB] w s₂).slots NTab.tabB k ()
    = w.slots NTab.tabB k () := by
  apply mischT_slot_beiseite
  intro h
  exact tab_nicht_geteilt hPBeide _ NTab.tabB h.2

/-- The closed index reads `0` (at `tabB`, the witness's slot). -/
theorem hBeide_idx0 {Γ : Ctx} (w : World nD) (ρ : Env nD Γ) :
    (eval w (nI0 : Expr nD Γ [] (.index (nD.count NTab.tabB))) w ρ).n = 0 := by
  rfl

/-- Any closed `0` index reads `0` (unfolded form, schematic proofs). -/
theorem hBeide_idx0w {Γ : Ctx} (w : World nD) (ρ : Env nD Γ)
    (h1 : (0 : Int) ≤ 0) (h2 : (0 : Int) ≤ 0) :
    (eval w (Expr.widen h1 h2 (Expr.lit 0 : Expr nD Γ [] (.int 0 0))) w ρ).n
      = 0 := by
  rfl

/-- The closed index reads nothing. -/
theorem hBeide_orte_nI0 :
    Expr.orte (nI0 : Expr nD [] [] (.index (nD.count NTab.tabB))) = [] := by
  rfl

/-- `eval` of a global read is the world's global (by definition;
    the access proof stays schematic, so this fires on every occurrence). -/
theorem hBeide_evalGlob {Γ : Ctx} (w : World nD) (ρ : Env nD Γ)
    (hg : gdarf nD NGlob.konfig []) :
    eval w (.glob NGlob.konfig hg) w ρ = w.globs NGlob.konfig := by
  rfl

/-- `eval` of the slot read (by definition; index and access proofs stay
    schematic, the index computes later). -/
theorem hBeide_evalSlot {Γ : Ctx} (w : World nD) (ρ : Env nD Γ)
    (i : Expr nD Γ [] (.index (nD.count NTab.tabB)))
    (hd : darf nD NTab.tabB []) :
    eval w (.slot NTab.tabB () i hd) w ρ
    = w.slots NTab.tabB (eval w i w ρ).n () := by
  rfl

/-- A plain read changes only the trace: slots stay. -/
theorem hBeide_lese_slots (w : World nD) (Λ : List (Res nD))
    (X : List (nD.Tab ⊕ nD.Glob)) (k : Int) :
    ((w.lese Λ X).slots NTab.tabB k ()) = w.slots NTab.tabB k () := by
  rfl

/-- Either branch writes literal `1` from any start world (it reads
    nothing shared, so even the kernel computes it). -/
theorem hZweigEins_eins (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (w₂ : World nD) (ρ : Env nD []) :
    ∃ σ₂, execBlockHA (V := vertragVon nD NFn.zaehlB) S O' U
      (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R hZweigEins w₂ ρ
      = .ok σ₂ ρ ∧ (σ₂.slots NTab.tabB 0 ()).n = 1 := by
  exact ⟨_, rfl, rfl⟩

/-- The tail returns, keeping `tabB[0]`. -/
theorem hSchwanz_behält (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ₂ : World nD) (ρ : Env nD []) :
    ∃ σ' v, execEndHA (V := vertragVon nD NFn.zaehlB) S O' U
      (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R hSchwanzLeer σ₂ ρ
      = .zurueck σ' v ∧ (σ'.slots NTab.tabB 0 ()).n = (σ₂.slots NTab.tabB 0 ()).n := by
  exact ⟨_, _, rfl, rfl⟩

/-- The stored value is `s₁`'s `konfig`. -/
theorem hBeide_stored_is_s1 (w₁ : World nD) (s₁ : Speicher nD) :
    ((w₁.schreibSlot NTab.tabB [] 0 () (s₁.globs NGlob.konfig)).slots
      NTab.tabB 0 ()) = s₁.globs NGlob.konfig := by
  simp only [World.schreibSlot, World.storeSlot, World.merke]
  rfl

/-- The program runs the both-covered body (by definition). -/
theorem hPBeide_rumpf : hPBeide.rumpf NFn.zaehlB = hRumpfBeide := by
  rfl

/-- Under every pinned run the body answers `tabB[0] = 1` (green version,
    restored verbatim from the pre-kill commit). -/
theorem hBeide_wert (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    tabBNach (execEndHA (V := vertragVon nD NFn.zaehlB) S O' U
    (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R
      (hPBeide.rumpf NFn.zaehlB) σ ρ) = 1 := by
  rw [hPBeide_rumpf]
  simp only [hRumpfBeide, hLies, hC, hZweigEins, hSetze, hSchwanzLeer, nI0, nW,
    execEndHA, execStmtHA, execBlockHA, Expr.orte, wahr?, eval,
    List.nil_append, List.cons_append, List.append_nil,
    hBeide_lese1, hBeide_lese2, hBeide_lese0,
    hBeide_idx0w, hBeide_g1, hBeide_g2, hBeide_slot]
  split <;> rename_i heq <;>
    (simp only [hBeide_lese0, ErgExpr.orte, tabBNach, hBeide_lese_slots]
     split at heq <;> cases heq <;> rfl)

/-- A `1` answer comes from a value return (all other outcomes read `-1`). -/
theorem tabBNach_zurueck {V : Vertrag nD} {l : Bool} {Γ : Ctx}
    (o : EndAusgang V l Γ) (h : tabBNach o = 1) : ∃ σ' v, o = .zurueck σ' v := by
  cases o with
  | zurueck σ' v => exact ⟨σ', v, rfl⟩
  | why σ' r => simp only [tabBNach] at h; omega
  | leave h σ' ρ' => simp only [tabBNach] at h; omega
  | next h σ' ρ' => simp only [tabBNach] at h; omega
  | logik e => simp only [tabBNach] at h; omega
  | hardware e => simp only [tabBNach] at h; omega

/-- Every pinned run returns (from the `= 1` fact). -/
theorem hBeide_zurueck (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD)
    (s₁ s₂ : Speicher nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    ∃ σ' v, execEndHA (V := vertragVon nD NFn.zaehlB) S O' U
      (pinA (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) [.inr NGlob.konfig]
        [.inr NGlob.konfig, .inl NTab.tabB] s₁ s₂) passes R
      (hPBeide.rumpf NFn.zaehlB) σ ρ
      = .zurueck σ' v :=
  tabBNach_zurueck _ (hBeide_wert S O' U s₁ s₂ passes R σ ρ)

/-- **The person's duty holds on the witness**: every pinned run answers
    `1` (both outcomes), always returns, and never hits `.logik`. -/
theorem hBeide_personenPflicht (passes : Nat) :
    FlagPersonenPflicht hPBeide (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) passes NFn.zaehlB
      [.inr NGlob.konfig] [.inr NGlob.konfig, .inl NTab.tabB] := by
  refine ⟨fun O' _ _ _ U _ s₁ s₂ R _ _ σ ρ _ => ⟨fun σ' v h => ?_, fun g h => ?_⟩,
    fun O' _ _ _ U _ s₁ s₂ R _ _ σ ρ _ e h => ?_⟩
  · have h1 := hBeide_wert SchwachZeuge.nS O' U s₁ s₂ passes R σ ρ
    rw [h] at h1
    simp only [tabBNach] at h1
    show decide ((σ'.slots NTab.tabB 0 ()).n = 1) = true
    exact decide_eq_true h1
  · obtain ⟨σ', v, h'⟩ := hBeide_zurueck SchwachZeuge.nS O' U s₁ s₂ passes
      (torRuf hPBeide R) σ ρ
    rw [h'] at h
    cases h
  · obtain ⟨σ', v, h'⟩ := hBeide_zurueck SchwachZeuge.nS O' U s₁ s₂ passes R σ ρ
    rw [h'] at h
    cases h

/-- The witness body has the flag shape (by definition). -/
theorem hBeide_shape :
    hPBeide.rumpf NFn.zaehlB
      = .cons hLies (.cons (.ite hC hZweigEins hZweigEins) hSchwanzLeer) := by
  rfl

/-- The witness store source, named once so every occurrence matches
    syntactically (the transfer, the store fact and the read lists share
    this exact term). -/
def eSrcWitness : Expr nD (nD.params NFn.zaehlB)
    (Signatur.anfang nD (nD.signatur NFn.zaehlB)) (nD.typ NTab.tabB ()) :=
  (.glob NGlob.konfig (nGd _ _))

/-- The witness store is the shared-flag store. -/
theorem hBeide_store :
    ∃ (hw : (vertragVon nD NFn.zaehlB).schreibt NTab.tabB = true)
      (hL : darf nD NTab.tabB (Signatur.anfang nD (nD.signatur NFn.zaehlB))),
      hLies = .assignSlot NTab.tabB () nI0 eSrcWitness hw hL := by
  exact ⟨rfl, nDarf _ _, rfl⟩

/-- The non-pinned witness reads avoid the shared set (vacuous: none). -/
theorem hBeide_frei :
    ∀ o ∈ blockOrteP hPBeide hZweigEins ++ blockOrteP hPBeide hZweigEins
      ++ endblockOrteP hPBeide hSchwanzLeer,
      ¬ GeteiltA hPBeide [NFn.kern, NFn.zaehlB] o := by
  rw [hBeide_frei_liste]
  intro o h
  simp only [List.mem_nil_iff] at h

/-- **The transfer fires on the witness**: the both-covered `hP` shape
    meets its contract against every atomic environment. -/
theorem hBeide_relyDuty (passes : Nat) :
    KoerperGutSA hPBeide passes (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) NFn.zaehlB :=
  flagKoerper_relyDuty hPBeide SchwachZeuge.nS (axWahr nD)
    (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) passes NFn.zaehlB
    hLies (.ite hC hZweigEins hZweigEins) hSchwanzLeer
    NTab.tabB () nI0 eSrcWitness hC hZweigEins hZweigEins
    hBeide_shape hBeide_store rfl (by decide) hBeide_frei
    (hBeide_personenPflicht passes)

/-- Owed invariants at a value return: vacuous (`nD` declares none). -/
theorem hBeide_invGutSA (passes : Nat) :
    InvGutSA hPBeide passes (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) NFn.zaehlB := by
  intro O' hr hl hq U hU A hA R hR hV σ ρ hReq σ' v he
  intro i hi _
  cases hi

/-- Owed invariants at a reason return: vacuous likewise. -/
theorem hBeide_invGutGrundA (passes : Nat) :
    InvGutGrundA hPBeide passes (axWahr nD) SchwachZeuge.nS
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) NFn.zaehlB := by
  intro O' hr hl hq U hU A hA R hR hV σ ρ hReq σ' r he
  intro i hi _
  cases hi

/-- **The full rely duty on the witness**: body triple (both branches
    covered) plus the vacuous invariant duties. -/
theorem hBeide_relyDuty_voll (passes : Nat) :
    Gabbro.Grammatik.GabbroV.GvAtomRely.GvRelyDuty hPBeide SchwachZeuge.nS (axWahr nD)
      (GeteiltA hPBeide [NFn.kern, NFn.zaehlB]) passes NFn.zaehlB :=
  ⟨hBeide_relyDuty passes, hBeide_invGutSA passes, hBeide_invGutGrundA passes⟩

/-! ## 9. Planted body outside the class -/

open AtomarXZeuge in
/-- Planted body: the same flag test, but with NO pinning store (the test
    reads the live shared value directly). A real body that runs -- just
    not in the class: there is no pinned read to case-split on. -/
def hRumpfFalsch : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons (.ite hC hZweigEins hZweigEins) hSchwanzLeer

open AtomarXZeuge in
/-- The planted program (contracts unchanged). -/
def hPFalsch : Programm nD :=
  ({ AtomarXZeuge.hP with rumpf := fun f => match f with
    | .zaehlB => hRumpfFalsch
    | f => AtomarXZeuge.hP.rumpf f } : Programm nD)

/-- The predicate rejects it, by deciding the computation. -/
theorem hFalsch_abgelehnt :
    istFlagKoerper hPFalsch NFn.zaehlB NGlob.konfig NTab.tabB = false := by
  rfl

/- CUTS: what is not proved or not covered.
    PROVED here: `istFlagKoerper`, `flagKoerperLesen`, `pinA` (+ `pinA_havoc`),
    `leseA_pinA_X₁/X₂`, `FlagPersonenPflicht`, `flagKoerper_run_gleich`,
    `flagKoerper_relyDuty` (the transfer for `KoerperGutSA`); the witness
    (`hRumpfBeide`, `hPBeide`, class/decide facts, `GeteiltA` facts,
    pinned-run values, `hBeide_personenPflicht`, `hBeide_relyDuty`,
    `hBeide_invGutSA/GrundA`, full `hBeide_relyDuty_voll`).
    NOT proved / not covered:
    * heterogeneous (non-uniform) chains: not this file's subject;
      see `GvSplits.lean`.
    * invariant duties beyond invariant-free programs: the witness's
      `InvGutSA/GrundA` hold vacuously (`nD.invs = []`); programs WITH
      table invariants need per-invariant coverage in the person's duty.
    * no tactic integration: nothing here changes `gabbro_calls` or
      `programmlogik/`; these are the sound proof rules such integration
      would invoke.
    * the planted rejection is PROVED (`hFalsch_abgelehnt`: a flag test
      with no pinning store is rejected by `decide`). -/
#print axioms Gabbro.Grammatik.GvAtomKoerper.istFlagKoerper
#print axioms Gabbro.Grammatik.GvAtomKoerper.flagKoerperLesen
#print axioms Gabbro.Grammatik.GvAtomKoerper.pinA
#print axioms Gabbro.Grammatik.GvAtomKoerper.pinA_havoc
#print axioms Gabbro.Grammatik.GvAtomKoerper.leseA_pinA_X₁
#print axioms Gabbro.Grammatik.GvAtomKoerper.leseA_pinA_X₂
#print axioms Gabbro.Grammatik.GvAtomKoerper.FlagPersonenPflicht
#print axioms Gabbro.Grammatik.GvAtomKoerper.flagKoerper_run_gleich
#print axioms Gabbro.Grammatik.GvAtomKoerper.flagKoerper_relyDuty
#print axioms Gabbro.Grammatik.GvAtomKoerper.hRumpfBeide
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPBeide
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_in_klasse
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lesen_leer
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPBeide_konfig_geteilt
#print axioms Gabbro.Grammatik.GvAtomKoerper.tab_nicht_geteilt
#print axioms Gabbro.Grammatik.GvAtomKoerper.mischT_globs
#print axioms Gabbro.Grammatik.GvAtomKoerper.mischT_slot_beiseite
#print axioms Gabbro.Grammatik.GvAtomKoerper.hZweigEins
#print axioms Gabbro.Grammatik.GvAtomKoerper.hSchwanzLeer
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_frei_liste
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_pin1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_pin2
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_pin0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese2
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_g1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_g2
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_slot
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_idx0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_idx0w
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_orte_nI0
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_lese_slots
#print axioms Gabbro.Grammatik.GvAtomKoerper.hZweigEins_eins
#print axioms Gabbro.Grammatik.GvAtomKoerper.hSchwanz_behält
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_stored_is_s1
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_evalGlob
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_evalSlot
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_wert
#print axioms Gabbro.Grammatik.GvAtomKoerper.tabBNach_zurueck
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_zurueck
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPBeide_rumpf
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_personenPflicht
#print axioms Gabbro.Grammatik.GvAtomKoerper.eSrcWitness
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_shape
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_store
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_frei
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_relyDuty
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_invGutSA
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_invGutGrundA
#print axioms Gabbro.Grammatik.GvAtomKoerper.hBeide_relyDuty_voll
#print axioms Gabbro.Grammatik.GvAtomKoerper.hRumpfFalsch
#print axioms Gabbro.Grammatik.GvAtomKoerper.hPFalsch
#print axioms Gabbro.Grammatik.GvAtomKoerper.hFalsch_abgelehnt

end Gabbro.Grammatik.GvAtomKoerper
