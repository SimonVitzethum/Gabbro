/-
  File:     Grammatik/Geteilt.lean
  Subject:  **Shared, as a construction** -- closed-world reachability from thread
            entries plus concurrent sets, and the proof `geteilt_treu`.

  GOAL (lane 28, D1): turn `D1` (shared) from an explanation into a construction.
  In `Syntax.lean`, `D.geteilt` / `D.ggeteilt` are bare declarations, and in
  `Wettlauf.lean` the premise (W5) -- "an unshared carrier belongs to one thread" --
  is assumed per run (`Gesittet.ungeteilt`, justified by the Rust pass `H013`).
  This file builds the middle: a finite declaration `Bau` (thread entries, call
  edges, footprints, the carrier flags, the declared concurrent pairs) together
  with reachability computed FROM the entries, and proves `geteilt_treu`: a
  carrier declared unshared is reachable by at most one thread. The corollary
  `ungeteilt_aus_baulauf` has exactly the shape of (W5), so `kein_wettlauf`
  can consume it instead of the pass.

  LOUD FAILURE: there is no default `Bau`, no axiom, and no `sorry`. To apply
  `geteilt_treu` to a concrete declaration you must supply
  `h : pruefeUngeteilt B fuel = true`, which is decided by computation
  (`rfl` / `decide`). A declaration that wrongly marks a shared carrier
  unshared -- or forgets a reaching thread in `eintritt` / `ruft` -- makes the
  checker compute `false`, and the `rfl` fails at elaboration. The wrong
  declaration breaks the proof loudly, not silently.

  Mirror (this file is standalone -- the lane forbids editing the `Grammatik.lean`
  index, so it cannot be imported yet; names are chosen to wire up later):

  | here                  | there (`Syntax` / `Wettlauf`)              |
  |-----------------------|--------------------------------------------|
  | `Carrier := Nat`      | `D.Tab ⊕ D.Glob` (tables and globals, one) |
  | `Fn := Nat`           | `D.Fn`                                     |
  | `Bau.eintritt`        | thread entries (`entry` / `boot` roots)    |
  | `Bau.ruft`            | static call-edge over-approximation        |
  | `Bau.schreibtFn`      | `D.schreibt` / `D.gschreibt` (footprints)  |
  | `Bau.geteilt`         | `D.geteilt` / `D.ggeteilt`                 |
  | `Bau.neben`           | `Nebeneinander` (`concurrent { … }` sets)  |
  | `RuftStarN`/`ErreichtBau` | closed-world reachability               |
  | `ungeteilt_aus_baulauf`  | (W5) `Gesittet.ungeteilt`               |

  CUTS (booked, not hidden):
  C1. Table/global collapse: one `Carrier` stands for both; the split
      (`geteilt_treu` per table vs. per global) returns with the wiring.
      Narrowed (lane 130): §8 proves the fold/split round-trips and the
      code-injectivity shapes; the per-side `geteilt_treu` wiring is open.
  C2. Executable footprint: `schreibtFn` is declared per function HERE, but
      `Extraktion.lean` (lane 78) computes it from the effects
      (`fussAus` over `D.schreibt`/`D.gschreibt`, `fussTreue_aus_bau`) -- the
      call edges likewise (`ruftDirekt` traversal W-EXT, `kantenTreue_aus_bau`).
      What stays a premise is the dynamic coverage (`BauLauf`): every access
      of the run is covered by static reachability, stated explicitly.
  C3. Concurrent sets are a finite pair list, not the `Nebeneinander` relation;
      `Extraktion.lean` computes the list from the declaration (`nebenAus`,
      `paarTreue_aus_bau`/`paarVoll_aus_bau`) and speaks `Nebeneinander`
      (`Wettlauf.lean` §6) at the fidelity shapes.
  C4. Marks (W4) are derived, not assumed: `Marken.lean` proves single-threaded
      stands per `Verlauf`, and `Wettlauf.lean` §7 projects `Einfaedig` into
      `marke_eindeutig`. Only (W5) is derived HERE.
  C5. `fuel` is the declared exploration bound, mirroring `passes`/`fuel` of
      `Semantik.exec`: the checker and the reachability speak about the SAME
      fuel, so neither can outrun the other.

  Core only: no `mathlib`, no import at all (not even the sibling files, see the
  mirror note above). Zero `sorry`.
-/

namespace Gabbro.Grammatik.Geteilt

/-! ## 1. The declaration: entries, edges, footprints, flags, pairs -/

/-- Functions, as ids. Mirrors `D.Fn`. -/
abbrev Fn := Nat

/-- Carriers, as ids. Mirrors `D.Tab ⊕ D.Glob` (cut C1). -/
abbrev Carrier := Nat

/-- The closed-world declaration of one unit: who starts, who calls whom, who
    touches what, what is shared, and which pairs run together. -/
structure Bau where
  /-- Thread `f` starts in `eintritt[f]?`; threads past the end never step. -/
  eintritt : List Fn
  /-- Static call edges (over-approximation; cut C2). -/
  ruft : Fn → List Fn
  /-- Direct carrier footprint per function (cut C2). -/
  schreibtFn : Fn → List Carrier
  /-- `shared`: the flag under test. Mirrors `D.geteilt` / `D.ggeteilt`. -/
  geteilt : Carrier → Bool
  /-- All carriers of the unit (the checker's domain). -/
  traeger : List Carrier
  /-- Declared concurrent pairs (cut C3: finite list, not a relation). -/
  neben : List (Nat × Nat)

/-! ## 2. Reachability, from the entries -/

/-- Call reachability in at most `n` steps. `refl` at any `n`, so this is
    "reachable within `n`", matching the fuel-bounded computation below. -/
inductive RuftStarN (ruft : Fn → List Fn) : Nat → Fn → Fn → Prop where
  | refl (n : Nat) (e : Fn) : RuftStarN ruft n e e
  | schritt {n : Nat} {a b c : Fn} :
      RuftStarN ruft n a b → c ∈ ruft b → RuftStarN ruft (n + 1) a c

/-- A star fits in one more fuel. -/
theorem sternMono (ruft : Fn → List Fn) (n a b : Nat)
    (h : RuftStarN ruft n a b) : RuftStarN ruft (n + 1) a b := by
  induction h with
  | refl m e => exact RuftStarN.refl _ _
  | schritt hstar hmem ih => exact RuftStarN.schritt ih hmem

/-- The executable side: functions reachable within `fuel` steps. -/
def schrittBis (ruft : Fn → List Fn) (fuel : Nat) (e : Fn) : List Fn :=
  match fuel with
  | 0 => [e]
  | n + 1 => schrittBis ruft n e ++ (schrittBis ruft n e).flatMap ruft

theorem schrittBis_zero (ruft : Fn → List Fn) (e : Fn) :
    schrittBis ruft 0 e = [e] := rfl

theorem schrittBis_succ (ruft : Fn → List Fn) (e : Fn) (n : Nat) :
    schrittBis ruft (n + 1) e =
      schrittBis ruft n e ++ (schrittBis ruft n e).flatMap ruft := rfl

/-- The entry reaches itself, at any fuel. -/
theorem mem_schrittBis_refl (ruft : Fn → List Fn) (n e : Fn) :
    e ∈ schrittBis ruft n e := by
  induction n with
  | zero => simp [schrittBis_zero]
  | succ n ih =>
      rw [schrittBis_succ]
      exact List.mem_append.mpr (Or.inl ih)

/-- Soundness: what the computation finds, the star derives. -/
theorem mem_schrittBis_stern (ruft : Fn → List Fn) (n : Nat) (e a : Fn)
    (ha : a ∈ schrittBis ruft n e) : RuftStarN ruft n e a := by
  induction n generalizing e a with
  | zero =>
      rw [schrittBis_zero] at ha
      obtain rfl : a = e := by simpa using ha
      exact RuftStarN.refl _ _
  | succ n ih =>
      rw [schrittBis_succ, List.mem_append] at ha
      rcases ha with ha | ha
      · exact sternMono _ _ _ _ (ih e a ha)
      · obtain ⟨g₀, hg₀, hmem⟩ := List.mem_flatMap.mp ha
        exact RuftStarN.schritt (ih e g₀ hg₀) hmem

/-- Completeness: what the star derives, the computation finds. -/
theorem stern_mem_schrittBis (ruft : Fn → List Fn) (n e a : Nat)
    (h : RuftStarN ruft n e a) : a ∈ schrittBis ruft n e := by
  induction h with
  | refl m x => exact mem_schrittBis_refl ruft m x
  | schritt hstar hmem ih =>
      rw [schrittBis_succ]
      exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨_, ih, hmem⟩))

/-- The two sides coincide: computation and construction. -/
theorem mem_schrittBis_genau (ruft : Fn → List Fn) (n e a : Nat) :
    a ∈ schrittBis ruft n e ↔ RuftStarN ruft n e a :=
  ⟨fun hmem => mem_schrittBis_stern _ _ _ _ hmem,
    fun hstar => stern_mem_schrittBis _ _ _ _ hstar⟩

/-- Thread `f` reaches carrier `c` within `fuel`: its entry calls (in `fuel`
    steps) a function whose footprint holds `c`. -/
def ErreichtBau (B : Bau) (fuel : Nat) (f : Nat) (c : Carrier) : Prop :=
  ∃ e g, B.eintritt[f]? = some e ∧ RuftStarN B.ruft fuel e g ∧ c ∈ B.schreibtFn g

/-- The executable carrier set of one thread. -/
def traegerBis (B : Bau) (fuel : Nat) (f : Nat) : List Carrier :=
  match B.eintritt[f]? with
  | none => []
  | some e => (schrittBis B.ruft fuel e).flatMap B.schreibtFn

theorem traegerBis_none (B : Bau) (fuel f : Nat) (h : B.eintritt[f]? = none) :
    traegerBis B fuel f = [] := by
  unfold traegerBis
  rw [h]

theorem traegerBis_some (B : Bau) (fuel f : Nat) (e : Fn)
    (h : B.eintritt[f]? = some e) :
    traegerBis B fuel f = (schrittBis B.ruft fuel e).flatMap B.schreibtFn := by
  unfold traegerBis
  rw [h]

/-- Carrier computation and carrier construction coincide. -/
theorem traegerBis_genau (B : Bau) (fuel f : Nat) (c : Carrier) :
    c ∈ traegerBis B fuel f ↔ ErreichtBau B fuel f c := by
  constructor
  · intro hmem
    cases hentry : B.eintritt[f]? with
    | none =>
        rw [traegerBis_none B fuel f hentry] at hmem
        simp at hmem
    | some e =>
        rw [traegerBis_some B fuel f e hentry] at hmem
        obtain ⟨g, hg, hgc⟩ := List.mem_flatMap.mp hmem
        exact ⟨e, g, hentry, (mem_schrittBis_genau _ _ _ _).mp hg, hgc⟩
  · rintro ⟨e, g, he, hstar, hgc⟩
    rw [traegerBis_some B fuel f e he]
    exact List.mem_flatMap.mpr ⟨g, (mem_schrittBis_genau _ _ _ _).mpr hstar, hgc⟩

/-! ## 3. The checker: unshared means reached by at most one -/

/-- Threads reaching `c` within `fuel` (closed world: only entries count). -/
def erreicher (B : Bau) (fuel : Nat) (c : Carrier) : List Nat :=
  (List.range B.eintritt.length).filter fun f => decide (c ∈ traegerBis B fuel f)

theorem erreicher_genau (B : Bau) (fuel : Nat) (c f : Nat) :
    f ∈ erreicher B fuel c ↔ f < B.eintritt.length ∧ c ∈ traegerBis B fuel f := by
  unfold erreicher
  constructor
  · intro hmem
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hmem
    exact ⟨List.mem_range.mp h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr h1, decide_eq_true h2⟩

/-- The check over a carrier list: every unshared carrier has at most one
    reaching thread. -/
def ungeteiltOk : List Carrier → Bau → Nat → Bool
  | [], _, _ => true
  | c :: cs, B, fuel =>
      (B.geteilt c || decide ((erreicher B fuel c).length ≤ 1)) &&
        ungeteiltOk cs B fuel

/-- The declaration check: run `ungeteiltOk` over all carriers. -/
def pruefeUngeteilt (B : Bau) (fuel : Nat) : Bool :=
  ungeteiltOk B.traeger B fuel

/-- At most one element passes the filter: two witnesses agree. -/
theorem filter_hoechstens_eins {α : Type} {p : α → Bool} {l : List α} {a b : α}
    (h : (l.filter p).length ≤ 1) (ha : a ∈ l.filter p)
    (hb : b ∈ l.filter p) : a = b := by
  match hm : l.filter p with
  | [] => simp [hm] at ha
  | [x] =>
      have ha' : a = x := by simpa [hm] using ha
      have hb' : b = x := by simpa [hm] using hb
      rw [ha', hb']
  | y₁ :: y₂ :: ys =>
      have h2 : 2 ≤ (l.filter p).length := by
        rw [hm]; simp only [List.length_cons]; omega
      omega

/-- Soundness of the check: success means every unshared carrier in the list
    has at most one reaching thread. -/
theorem ungeteiltOk_genau (cs : List Carrier) (B : Bau) (fuel : Nat)
    (h : ungeteiltOk cs B fuel = true) (c : Carrier) (hmem : c ∈ cs)
    (hu : B.geteilt c = false) : (erreicher B fuel c).length ≤ 1 := by
  induction cs with
  | nil => simp at hmem
  | cons d ds ih =>
      have hmem' : c = d ∨ c ∈ ds := by simpa using hmem
      have hcons : ungeteiltOk (d :: ds) B fuel =
          ((B.geteilt d || decide ((erreicher B fuel d).length ≤ 1)) &&
            ungeteiltOk ds B fuel) := rfl
      rw [hcons, Bool.and_eq_true] at h
      obtain ⟨hd, hrest⟩ := h
      rcases hmem' with rfl | hmemds
      · rw [Bool.or_eq_true] at hd
        rcases hd with hd | hd
        · simp [hu] at hd
        · exact of_decide_eq_true hd
      · exact ih hrest hmemds

/-- An entry hit bounds the thread: the world is closed. -/
theorem eintritt_schranke (l : List Fn) (f : Nat) (e : Fn)
    (h : l[f]? = some e) : f < l.length :=
  Classical.byContradiction fun hcon =>
    have hcon' : l.length ≤ f := by omega
    have hn : l[f]? = none := List.getElem?_eq_none hcon'
    by rw [hn] at h; simp at h

/-! ## 4. The theorem: an unshared carrier has one thread -/

/-- **Shared, faithfully (`geteilt_treu`).** If the check passes and `c` is
    declared unshared, any two threads reaching `c` are the same thread. -/
theorem geteilt_treu (B : Bau) (fuel : Nat) (h : pruefeUngeteilt B fuel = true)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (f g : Nat) (hf : ErreichtBau B fuel f c) (hg : ErreichtBau B fuel g c) :
    f = g := by
  have hlen :=
    ungeteiltOk_genau B.traeger B fuel (by simpa [pruefeUngeteilt] using h) c hmem hu
  obtain ⟨ef, gf, hef, hstf, hcbf⟩ := hf
  obtain ⟨eg, gg, heg, hstg, hcbg⟩ := hg
  have hflt : f < B.eintritt.length := eintritt_schranke _ _ _ hef
  have hglt : g < B.eintritt.length := eintritt_schranke _ _ _ heg
  have hfb : c ∈ traegerBis B fuel f :=
    (traegerBis_genau B fuel f c).mpr ⟨ef, gf, hef, hstf, hcbf⟩
  have hgb : c ∈ traegerBis B fuel g :=
    (traegerBis_genau B fuel g c).mpr ⟨eg, gg, heg, hstg, hcbg⟩
  have ha : f ∈ erreicher B fuel c := (erreicher_genau B fuel c f).mpr ⟨hflt, hfb⟩
  have hb : g ∈ erreicher B fuel c := (erreicher_genau B fuel c g).mpr ⟨hglt, hgb⟩
  exact filter_hoechstens_eins hlen ha hb

/-! ## 5. Dynamics: the (W5) shape over runs -/

/-- One access: thread and carrier. Mirrors `Wettlauf.Schritt` cut down to
    accesses (lock events play no role in (W5)). -/
abbrev SchrittC := Nat × Carrier

/-- **(W5) from declarations.** Two accesses to the same declared-unshared
    carrier are by the same thread -- provided every access is covered by static
    reachability (cut C2: the body-extraction obligation, stated, not hidden). -/
theorem ungeteilt_aus_bau (B : Bau) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true) (l : List SchrittC)
    (hdeck : ∀ s ∈ l, ErreichtBau B fuel s.1 s.2)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (s₁ s₂ : SchrittC) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = c) : s₁.1 = s₂.1 := by
  have e1 := hdeck s₁ h₁
  have e2 := hdeck s₂ h₂
  rw [← hg] at e2
  rw [hc] at e1 e2
  exact geteilt_treu B fuel h c hmem hu s₁.1 s₂.1 e1 e2

/-- A closed-world run: accesses are covered AND only declared pairs
    interleave (entries plus concurrent sets, cut C3). -/
def BauLauf (B : Bau) (fuel : Nat) (l : List SchrittC) : Prop :=
  (∀ s ∈ l, ErreichtBau B fuel s.1 s.2) ∧
    (∀ s₁ ∈ l, ∀ s₂ ∈ l,
      s₁.1 = s₂.1 ∨ (s₁.1, s₂.1) ∈ B.neben ∨ (s₂.1, s₁.1) ∈ B.neben)

/-- **Closed world, sentence form.** Every stepping thread has an entry:
    no entry, no step. (The companion of `Wettlauf.nur_deklariert_teilt_lauf`,
    which is likewise the definition, applied.) -/
theorem lauf_hat_eintritt (B : Bau) (fuel : Nat) (l : List SchrittC)
    (hl : BauLauf B fuel l) (s : SchrittC) (hs : s ∈ l) :
    ∃ e, B.eintritt[s.1]? = some e := by
  obtain ⟨e, _, he, _, _⟩ := hl.1 s hs
  exact ⟨e, he⟩

/-- **Only declared pairs share the run, sentence form.** In a closed-world
    run, two steps of different threads name a declared pair. -/
theorem nur_deklariert_teilt_lauf (B : Bau) (fuel : Nat) (l : List SchrittC)
    (hl : BauLauf B fuel l)
    (s₁ s₂ : SchrittC) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l) (hfg : s₁.1 ≠ s₂.1) :
    (s₁.1, s₂.1) ∈ B.neben ∨ (s₂.1, s₁.1) ∈ B.neben := by
  rcases hl.2 s₁ h₁ s₂ h₂ with h | h | h
  · exact absurd h hfg
  · exact Or.inl h
  · exact Or.inr h

/-- **(W5) over closed-world runs**, the form `kein_wettlauf` consumes. -/
theorem ungeteilt_aus_baulauf (B : Bau) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true) (l : List SchrittC)
    (hl : BauLauf B fuel l)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (s₁ s₂ : SchrittC) (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = c) : s₁.1 = s₂.1 :=
  ungeteilt_aus_bau B fuel h l hl.1 c hmem hu s₁ s₂ h₁ h₂ hg hc

/-! ## 6. Speech probe: the checker computes, the theorem applies -/

/-- Two threads, one carrier each, both unshared: the check passes. -/
def miniB : Bau where
  eintritt := [0, 1]
  ruft := fun _ => []
  schreibtFn := fun | 0 => [7] | _ => [9]
  geteilt := fun _ => false
  traeger := [7, 9]
  neben := [(0, 1)]

/-- The checker decides by computation: a wrong flag would make this `rfl`
    fail at elaboration -- the loud break. -/
example : pruefeUngeteilt miniB 3 = true := rfl

/-- The theorem applies to the concrete declaration. -/
example (h1 : ErreichtBau miniB 3 0 7) (h2 : ErreichtBau miniB 3 0 7) :
    (0 : Nat) = 0 :=
  geteilt_treu miniB 3 rfl 7 (by decide) rfl 0 0 h1 h2

#print axioms Gabbro.Grammatik.Geteilt.geteilt_treu
#print axioms Gabbro.Grammatik.Geteilt.ungeteilt_aus_baulauf
#print axioms Gabbro.Grammatik.Geteilt.nur_deklariert_teilt_lauf

/-! ## 7. Entwurf: Trennung von Tabelle und Global neben `Carrier` (ändert nichts Bestehendes) -/

/-- Tabellen-Träger als eigene Sorte, daneben `Carrier` (Schnitt C1, Entwurf:
    bindet die heutigen Beweise nicht um). -/
abbrev TabCarrier := Nat

/-- Global-Träger als eigene Sorte, daneben `Carrier` (Schnitt C1, Entwurf:
    bindet die heutigen Beweise nicht um). -/
abbrev GlobCarrier := Nat

/-- Faltung einer Seite: Tabelle nach zusammengelegtem Träger. -/
def carrierVonTab : TabCarrier → Carrier := fun t => t

/-- Faltung einer Seite: Global nach zusammengelegtem Träger. -/
def carrierVonGlob : GlobCarrier → Carrier := fun g => g

/-- Spiegel einer Seite: zusammengelegter Träger nach Tabelle. -/
def tabVonCarrier : Carrier → TabCarrier := fun c => c

/-- Spiegel einer Seite: zusammengelegter Träger nach Global. -/
def globVonCarrier : Carrier → GlobCarrier := fun c => c

/-- Faltung der geteilten Sorte in den zusammengelegten Träger. -/
def carrierVonSplit : TabCarrier ⊕ GlobCarrier → Carrier
  | .inl t => carrierVonTab t
  | .inr g => carrierVonGlob g

/-- Teilung des zusammengelegten Trägers in die geteilte Sorte; die
    Kennzeichnung `istTab` bleibt Behauptung der späteren Verdrahtung und wird
    hier nicht festgelegt. -/
def splitVonCarrier (istTab : Carrier → Bool) (c : Carrier) :
    TabCarrier ⊕ GlobCarrier :=
  if istTab c then .inl (tabVonCarrier c) else .inr (globVonCarrier c)

/-- Rundweg-Gestalt Tabelle: Spiegeln faltet zurück. -/
def tabRundweg (t : TabCarrier) : Prop :=
  tabVonCarrier (carrierVonTab t) = t

/-- Rundweg-Gestalt Global: Spiegeln faltet zurück. -/
def globRundweg (g : GlobCarrier) : Prop :=
  globVonCarrier (carrierVonGlob g) = g

/-- Rundweg-Gestalt Falten nach Teilen: Falten macht Teilen rückgängig. -/
def faltTeileForm (istTab : Carrier → Bool) (c : Carrier) : Prop :=
  carrierVonSplit (splitVonCarrier istTab c) = c

/-- Rundweg-Gestalt Teilen nach Falten, Tabellenseite. -/
def teileFaltFormTab (istTab : Carrier → Bool) (t : TabCarrier) : Prop :=
  splitVonCarrier istTab (carrierVonSplit (Sum.inl t)) = Sum.inl t

/-- Rundweg-Gestalt Teilen nach Falten, Globalseite. -/
def teileFaltFormGlob (istTab : Carrier → Bool) (g : GlobCarrier) : Prop :=
  splitVonCarrier istTab (carrierVonSplit (Sum.inr g)) = Sum.inr g

/-! ## 8. The split round-trips, proved (changes nothing above)

    The §7 shapes are Prop-defs; here they are discharged from the split
    types. `tabRundweg`/`globRundweg` hold for every carrier, `faltTeileForm`
    for every tag function (both branches fold back to `c`), and the two
    `teileFalt` forms hold under the matching tag premise -- the split can
    only return the injected side when the tag names it.

    The three `…Form` defs below mirror the `hinj`/`hdisj` premises that
    `Extraktion.lean` carries at `geteiltTab_trifft`/`geteiltGlob_trifft`/
    `geteiltAus_glob`: code injectivity per half and separation of the
    halves. Injectivity holds for the identity codes of cut C1 and is proved;
    separation does NOT hold in general (both halves fold through the same
    `Nat`) and stays a stated shape for downstream lanes to assume. -/

/-- Table round-trip: mirroring folds back. -/
theorem tabRundweg_holds (t : TabCarrier) : tabRundweg t := rfl

/-- Global round-trip: mirroring folds back. -/
theorem globRundweg_holds (g : GlobCarrier) : globRundweg g := rfl

/-- Fold after split is the identity, whatever the tag says: both branches
    fold back to `c`. -/
theorem faltTeile_holds (istTab : Carrier → Bool) (c : Carrier) :
    faltTeileForm istTab c := by
  unfold faltTeileForm splitVonCarrier
  by_cases h : istTab c = true
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

/-- Split after fold returns the table injection, provided the tag marks the
    folded code as a table. -/
theorem teileFaltTab_holds (istTab : Carrier → Bool) (t : TabCarrier)
    (h : istTab (carrierVonSplit (Sum.inl t)) = true) :
    teileFaltFormTab istTab t := by
  unfold teileFaltFormTab splitVonCarrier
  rw [if_pos h]
  rfl

/-- Split after fold returns the global injection, provided the tag marks the
    folded code as a global. -/
theorem teileFaltGlob_holds (istTab : Carrier → Bool) (g : GlobCarrier)
    (h : istTab (carrierVonSplit (Sum.inr g)) = false) :
    teileFaltFormGlob istTab g := by
  unfold teileFaltFormGlob splitVonCarrier
  have hne : ¬ istTab (carrierVonSplit (Sum.inr g)) = true := by
    rw [h]
    exact Bool.false_ne_true
  rw [if_neg hne]
  rfl

/-- Table-code injectivity as a shape: the `hinj` premise
    (`geteiltTab_trifft`) over the split table type. -/
def tabInjForm (tabs : List TabCarrier) : Prop :=
  ∀ t₁ ∈ tabs, ∀ t₂ ∈ tabs, carrierVonTab t₁ = carrierVonTab t₂ → t₁ = t₂

/-- Global-code injectivity as a shape: the `hinj` premise
    (`geteiltGlob_trifft`) over the split global type. -/
def globInjForm (globs : List GlobCarrier) : Prop :=
  ∀ g₁ ∈ globs, ∀ g₂ ∈ globs, carrierVonGlob g₁ = carrierVonGlob g₂ → g₁ = g₂

/-- Separation of the carrier halves as a shape: the `hdisj` premise
    (`geteiltAus_glob`) -- no table code meets a global code. Stated, not
    proved: under the identity codes of cut C1 it fails in general. -/
def halvesDisjointForm (tabs : List TabCarrier)
    (globs : List GlobCarrier) : Prop :=
  ∀ t ∈ tabs, ∀ g ∈ globs, carrierVonTab t ≠ carrierVonGlob g

/-- Table codes are injective: the codes ARE the carriers (cut C1). -/
theorem tabInj_all (tabs : List TabCarrier) : tabInjForm tabs := by
  intro t₁ _ t₂ _ h
  exact h

/-- Global codes are injective: the codes ARE the carriers (cut C1). -/
theorem globInj_all (globs : List GlobCarrier) : globInjForm globs := by
  intro g₁ _ g₂ _ h
  exact h

#print axioms Gabbro.Grammatik.Geteilt.tabRundweg_holds
#print axioms Gabbro.Grammatik.Geteilt.globRundweg_holds
#print axioms Gabbro.Grammatik.Geteilt.faltTeile_holds
#print axioms Gabbro.Grammatik.Geteilt.teileFaltTab_holds
#print axioms Gabbro.Grammatik.Geteilt.teileFaltGlob_holds
#print axioms Gabbro.Grammatik.Geteilt.tabInj_all
#print axioms Gabbro.Grammatik.Geteilt.globInj_all

/-! ## 9. World extension: the Seite partition over split carriers -/

/- C7 coordination: the Tab/Glob Bau -- which tables and globals exist
   and who writes them -- is owned by another wave. This section touches
   ONLY the World-partition defs: which side each split carrier sits on
   (`WeltSeiteBau`, `weltSeite`), what a cross-partition world step is
   (`WeltSchritt`, `quertWelt`, `weltRein`, `weltQuerSchritt`), and the
   discharge that separation forbids it
   (`getrennteWelt_keinQuerschritt`). The Adressraum side carries the
   region version (`Adressraum.WeltSeite`, `querSchritt`,
   `getrennteSeite_keinQuerschritt`); the fold between the two is
   `carrierVonSplit` (§7), whose round-trips §8 proves. -/

/-- The two sides, mirrored from `Adressraum.Seite` without the import:
    this file stays dependency-free (see the header mirror note). -/
inductive WSeite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- The Seite partition over split world carriers: every table and every
    global sits on exactly one side. -/
def WeltSeiteBau :=
  TabCarrier ⊕ GlobCarrier → WSeite

/-- The side of one split world carrier under the partition. -/
def weltSeite (p : WeltSeiteBau) (c : TabCarrier ⊕ GlobCarrier) : WSeite :=
  p c

/-- A one-carrier world step: the carrier it touches and the side it
    runs on. An exec step runs ON one side; crossing is touching the
    other side's carrier. -/
structure WeltSchritt where
  traeger : TabCarrier ⊕ GlobCarrier
  seite : WSeite

/-- The step crosses the partition exactly when the touched carrier sits
    on the other side than the step runs on. -/
def quertWelt (p : WeltSeiteBau) (s : WeltSchritt) : Prop :=
  p s.traeger ≠ s.seite

/-- A step confined to its side: touched carrier and running side agree. -/
def weltRein (p : WeltSeiteBau) (s : WeltSchritt) : Prop :=
  p s.traeger = s.seite

/-- Confinement is the negation of crossing, by shape. -/
theorem weltRein_keinQueren (p : WeltSeiteBau) (s : WeltSchritt) :
    weltRein p s ↔ ¬ quertWelt p s := by
  unfold weltRein quertWelt
  constructor
  · intro h hc
    exact hc h
  · intro h
    by_cases heq : p s.traeger = s.seite
    · exact heq
    · exact absurd heq h

/-- A cross-partition world step: the same folded carrier touched once
    running user-side, once running kernel-side, both confined -- one
    carrier, both sides. `f` is the fold into the checked carrier
    (`carrierVonSplit`, §7); the Tab/Glob Bau behind it is owned
    elsewhere. -/
def weltQuerSchritt (p : WeltSeiteBau)
    (f : TabCarrier ⊕ GlobCarrier → Carrier) (a b : WeltSchritt) : Prop :=
  f a.traeger = f b.traeger ∧ a.seite = .user ∧ b.seite = .kern ∧
    weltRein p a ∧ weltRein p b

/-- **Discharge: separation entails no cross-partition world step.** If
    the partition factors through the fold -- the same folded code sits
    on the same side (the carrier-level separation premise; cf.
    `halvesDisjointForm`, stated where the codes collide and proved
    where they cannot) -- then no single folded carrier is touched
    confined from both sides at once. -/
theorem getrennteWelt_keinQuerschritt (p : WeltSeiteBau)
    (f : TabCarrier ⊕ GlobCarrier → Carrier)
    (hf : ∀ c₁ c₂, f c₁ = f c₂ → p c₁ = p c₂)
    (a b : WeltSchritt) (h : weltQuerSchritt p f a b) : False := by
  obtain ⟨hfold, ha, hb, hain, hbin⟩ := h
  unfold weltRein at hain hbin
  rw [ha] at hain
  rw [hb] at hbin
  have hsame : p a.traeger = p b.traeger := hf _ _ hfold
  rw [hain, hbin] at hsame
  simp at hsame

/-- Speech probe: a single-sided partition factors through any fold, so
    the discharge applies. -/
example (f : TabCarrier ⊕ GlobCarrier → Carrier)
    (c₁ c₂ : TabCarrier ⊕ GlobCarrier) (_ : f c₁ = f c₂) :
    (fun _ => WSeite.user) c₁ = (fun _ => WSeite.user) c₂ :=
  rfl

#print axioms Gabbro.Grammatik.Geteilt.weltRein_keinQueren
#print axioms Gabbro.Grammatik.Geteilt.getrennteWelt_keinQuerschritt
/-! ## 10. Owner marks on the producer path -- the sharing-level application

    `Syntax.lean:149` carries `eigner_nie_erzeugt` -- no signature produces an
    owner mark -- and `SYNTAX.md:1625` books it as true but unapplied. §5 of
    `Typen.lean` applies it to one call step; here it is applied to the closed
    world: along every call chain from the entries, the produced marks carry
    no owner mark, so an owner mark held anywhere in the world traces back to
    an entry's initial holdings. That entry context -- which linear value
    becomes the first mark, and at whose hands -- is the producer story `D026`
    waits for. Nothing below modifies `Bau` or the world-partition regions;
    the owner declaration stands beside them and reads the existing
    reachability (`schrittBis`, `geteilt_treu`) without touching it.
-/

/-- Owner marks, as numbers. Mirrors `D.Marke` cut down to identity. -/
abbrev OwnerMarke := Nat

/-- Who holds the first mark: the owner declaration beside the closed world.
    `eignerVon` folds `D.eigner` to the closed-world `Carrier`; `anfang` names
    the entry's initial holdings (the `Signaturkopf` story of `Marken.lean`
    cut C4); `erzeugtFn` mirrors `S.produziert` along the call graph. -/
structure OwnerAnfang where
  /-- Owner marks per carrier (`D.eigner`, folded). -/
  eignerVon : Carrier → List OwnerMarke
  /-- Initial holdings per entry function: the marks the entry starts with. -/
  anfang : Fn → List OwnerMarke
  /-- Produced marks per function (mirrors `S.produziert`). -/
  erzeugtFn : Fn → List OwnerMarke
  /-- The applied theorem: no function produces an owner mark
      (`eigner_nie_erzeugt`, `Syntax.lean:149`). A premise here, as `Bau`
      fields are premises above -- the wiring instantiates it. -/
  eigner_nie_erzeugt : ∀ f m, m ∈ erzeugtFn f → ¬ ∃ c, m ∈ eignerVon c

/-- Every mark produced along the reachable calls from entry `e`. -/
def weltErzeugt (W : OwnerAnfang) (ruft : Fn → List Fn) (fuel : Nat)
    (e : Fn) : List OwnerMarke :=
  (schrittBis ruft fuel e).flatMap W.erzeugtFn

/-- **The reachable producer path carries no owner mark.** Whatever the calls
    from the entries produce, no owner mark is among it. -/
theorem eigner_nie_in_welt (W : OwnerAnfang) (ruft : Fn → List Fn)
    (fuel : Nat) (e : Fn)
    (m : OwnerMarke) (hm : m ∈ weltErzeugt W ruft fuel e) :
    ¬ ∃ c, m ∈ W.eignerVon c := by
  unfold weltErzeugt at hm
  obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp hm
  exact W.eigner_nie_erzeugt g m hg

/-- **The first mark comes from the entry.** An owner mark held anywhere in
    the closed world -- initial holdings or produced along the calls -- was
    in the entry's initial holdings: the produced half cannot carry it. -/
theorem eigner_erster_aus_anfang (W : OwnerAnfang) (ruft : Fn → List Fn)
    (fuel : Nat) (e : Fn)
    (m : OwnerMarke) (_hmE : ∃ c, m ∈ W.eignerVon c)
    (hmem : m ∈ W.anfang e ++ weltErzeugt W ruft fuel e) :
    m ∈ W.anfang e := by
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · exact absurd _hmE (eigner_nie_in_welt W ruft fuel e m h)

/-- **Owner-guarded and unshared means one thread.** An owner-guarded carrier
    that the declaration leaves unshared is reached by at most one thread --
    `geteilt_treu` applied to the owner case. The proof goes through
    unshared-ness; the owner premise selects the carriers this speaks about,
    and the two theorems above name where their first mark comes from. -/
theorem eigner_ungeteilt_ein_faden (B : Bau) (W : OwnerAnfang) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true)
    (c : Carrier) (hmem : c ∈ B.traeger) (hu : B.geteilt c = false)
    (m : OwnerMarke) (_hm : m ∈ W.eignerVon c)
    (f g : Nat) (hf : ErreichtBau B fuel f c) (hg : ErreichtBau B fuel g c) :
    f = g :=
  geteilt_treu B fuel h c hmem hu f g hf hg

#print axioms Gabbro.Grammatik.Geteilt.eigner_nie_in_welt
#print axioms Gabbro.Grammatik.Geteilt.eigner_erster_aus_anfang
#print axioms Gabbro.Grammatik.Geteilt.eigner_ungeteilt_ein_faden

/-! ## 11. Run-to-Bau wiring: the joint run over split carriers

    What §5 leaves open (cut C2, booked in the header): `ungeteilt_aus_baulauf`
    speaks about runs of folded carriers (`SchrittC = Nat × Carrier`). The (W5)
    shape downstream (`Gesittet.ungeteilt`, `ExecEng.ungeteilt`, `hungeteilt`)
    speaks about runs over the SPLIT sort (`D.Tab ⊕ D.Glob`): two accesses name
    the same split carrier `o`, and the flag is read through the fold. This
    section wires the joint run to the Bau: `ungeteilt_aus_lauf` lifts
    `geteilt_treu` from Bau-reachability to run-reachability over split
    carriers, discharging the `hungeteilt` shape for runs. `carrierVonSplit`
    (§7) is read, never rewritten; the §8 round-trips carry the tag-stable
    helpers (`faltLauf_split_stabil`, `laufTag_tab`, `laufTag_glob`).

    Narrowing, stated explicitly (no silent premise):

    N1. Entry discipline (cut C2, as in §5): the joint run is covered -- every
        access is reached statically (`BauLauf` over the fold: coverage plus
        only-declared-pairs-interleave). A run step outside static reachability
        is refused, not guessed.
    N2. Same split carrier: both steps name one split carrier `o`
        (`s₁.2 = s₂.2 = o`). Cross-side aliasing -- `inl t` vs `inr g` folding
        to one code -- is outside this section: ruling it out is
        `halvesDisjointForm` (§8), stated there and failing under the identity
        codes in general, so a downstream lane assumes it.
    No race-freedom is assumed: the conclusion holds for any two accesses,
    whether or not their threads interleave. -/

/-- A joint run over split carriers: thread and split carrier per access.
    Mirrors the `Lauf D` accesses behind `Gesittet.ungeteilt`, cut down to
    carrier identity (lock events play no role in (W5)). -/
abbrev LaufSplit := List (Nat × (TabCarrier ⊕ GlobCarrier))

/-- The fold of a joint run into the checked carrier run. -/
def faltLauf (l : LaufSplit) : List SchrittC :=
  l.map fun s => (s.1, carrierVonSplit s.2)

/-- Every split access folds into the folded run. -/
theorem mem_faltLauf (l : LaufSplit) (s : Nat × (TabCarrier ⊕ GlobCarrier))
    (h : s ∈ l) : (s.1, carrierVonSplit s.2) ∈ faltLauf l :=
  List.mem_map.mpr ⟨s, h, rfl⟩

/-- **Tag-stable fold.** Splitting a folded run carrier folds back to itself,
    under ANY tag -- `faltTeile_holds` (§8) applied to run carriers: the fold
    the checker reads is the fold the run touched, whichever side the tag
    names. -/
theorem faltLauf_split_stabil (istTab : Carrier → Bool)
    (o : TabCarrier ⊕ GlobCarrier) :
    carrierVonSplit (splitVonCarrier istTab (carrierVonSplit o)) =
      carrierVonSplit o :=
  faltTeile_holds istTab (carrierVonSplit o)

/-- **Per-side tag reading, table side.** Under the explicit tag-match premise
    the split of a folded table code returns the table injection --
    `teileFaltTab_holds` (§8) applied to run carriers. -/
theorem laufTag_tab (istTab : Carrier → Bool) (t : TabCarrier)
    (h : istTab (carrierVonSplit (Sum.inl t)) = true) :
    splitVonCarrier istTab (carrierVonSplit (Sum.inl t)) = Sum.inl t :=
  teileFaltTab_holds istTab t h

/-- **Per-side tag reading, global side.** Under the explicit tag-match premise
    the split of a folded global code returns the global injection --
    `teileFaltGlob_holds` (§8) applied to run carriers. -/
theorem laufTag_glob (istTab : Carrier → Bool) (g : GlobCarrier)
    (h : istTab (carrierVonSplit (Sum.inr g)) = false) :
    splitVonCarrier istTab (carrierVonSplit (Sum.inr g)) = Sum.inr g :=
  teileFaltGlob_holds istTab g h

/-- **Unshared from the joint run (`ungeteilt_aus_lauf`).** If the check passes
    and the folded joint run is covered (narrowing N1), two accesses naming the
    same split carrier `o` (narrowing N2) whose folded code is declared
    unshared are by the same thread -- `geteilt_treu` lifted from
    Bau-reachability to run-reachability, in the shape `hungeteilt` consumes. -/
theorem ungeteilt_aus_lauf (B : Bau) (fuel : Nat)
    (h : pruefeUngeteilt B fuel = true) (l : LaufSplit)
    (hl : BauLauf B fuel (faltLauf l))
    (o : TabCarrier ⊕ GlobCarrier)
    (hmem : carrierVonSplit o ∈ B.traeger)
    (hu : B.geteilt (carrierVonSplit o) = false)
    (s₁ s₂ : Nat × (TabCarrier ⊕ GlobCarrier))
    (h₁ : s₁ ∈ l) (h₂ : s₂ ∈ l)
    (hg : s₁.2 = s₂.2) (hc : s₁.2 = o) : s₁.1 = s₂.1 := by
  have e1 : (s₁.1, carrierVonSplit s₁.2) ∈ faltLauf l := mem_faltLauf l s₁ h₁
  have e2 : (s₂.1, carrierVonSplit s₂.2) ∈ faltLauf l := mem_faltLauf l s₂ h₂
  have hg' : carrierVonSplit s₁.2 = carrierVonSplit s₂.2 :=
    congrArg carrierVonSplit hg
  have hc' : carrierVonSplit s₁.2 = carrierVonSplit o :=
    congrArg carrierVonSplit hc
  exact ungeteilt_aus_baulauf B fuel h (faltLauf l) hl (carrierVonSplit o)
    hmem hu (s₁.1, carrierVonSplit s₁.2) (s₂.1, carrierVonSplit s₂.2)
    e1 e2 hg' hc'

/-- Speech probe: the checker computes over the split run's fold, and the
    theorem applies to the concrete declaration. -/
example (hl : BauLauf miniB 3 (faltLauf [(0, Sum.inl (7 : TabCarrier))])) :
    (0 : Nat) = 0 :=
  ungeteilt_aus_lauf miniB 3 rfl _ hl (Sum.inl (7 : TabCarrier))
    (by decide) rfl (0, Sum.inl (7 : TabCarrier)) (0, Sum.inl (7 : TabCarrier))
    (List.mem_cons.mpr (Or.inl rfl)) (List.mem_cons.mpr (Or.inl rfl)) rfl rfl

#print axioms Gabbro.Grammatik.Geteilt.mem_faltLauf
#print axioms Gabbro.Grammatik.Geteilt.faltLauf_split_stabil
#print axioms Gabbro.Grammatik.Geteilt.laufTag_tab
#print axioms Gabbro.Grammatik.Geteilt.laufTag_glob
#print axioms Gabbro.Grammatik.Geteilt.ungeteilt_aus_lauf

end Gabbro.Grammatik.Geteilt

