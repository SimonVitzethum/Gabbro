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
  C2. Executable footprint: `schreibtFn` is declared per function, not extracted
      from `Stmt`/`Block` bodies -- that extraction is the missing joint model
      (same cut as `Wettlauf.lean` §5: no Owicki-Gries step yet). Dynamic
      coverage (`BauLauf`) therefore stays a premise, stated explicitly.
  C3. Concurrent sets are a finite pair list, not the `Nebeneinander` relation.
  C4. Marks (W4) are untouched; only (W5) is derived here.
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

end Gabbro.Grammatik.Geteilt

