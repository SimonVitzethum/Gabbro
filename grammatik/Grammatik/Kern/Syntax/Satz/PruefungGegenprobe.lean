/- C16 inventory item 15: counterprobe binding, artifact identity and
    measured status.

    The external `expects` name is bound uniquely to its check: `SondenBindung`
    is the check carrying the name with its exact text with no other-named
    check of the unit carrying that name, and `SondenEindeutig` is the
    unit-wide one-to-one ownership (pairwise distinct sonde names, `none`
    skipped) decided exactly by `sondenEindeutigB`. `SondenArtefakt` is the
    artifact identity (external name, build mode, image); `Gemessen` is the
    measured status -- a `durchgefallen` run on the matching artifact with a
    false verdict. Absence stays unmeasured (`nichtGelaufen` never measures),
    an unexpected true verdict fails that measurement, and a stale artifact
    (wrong name or mode) measures nothing. -/
module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungMessung

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Gegenprobe

/-- The sonde names of a unit: the external name of every bound counterprobe,
    in unit order. -/
def sondenNamen : List (CheckDecl D) → List String
  | [] => []
  | c :: rest =>
    match c.sonde with
    | none => sondenNamen rest
    | some (n, _) => n :: sondenNamen rest

/-- One-to-one counterprobe ownership: no two checks of the unit share a
    sonde name. -/
def SondenEindeutig (checks : List (CheckDecl D)) : Prop :=
  (sondenNamen checks).Nodup

/-- One-to-one ownership, decided. -/
def sondenEindeutigB : List (CheckDecl D) → Bool
  | [] => true
  | c :: rest =>
    match c.sonde with
    | none => sondenEindeutigB rest
    | some (n, _) =>
      !(rest.any fun d => match d.sonde with
        | none => false
        | some (m, _) => decide (m = n)) && sondenEindeutigB rest

/-- A name in the unit's sonde list is carried by some check of the unit. -/
theorem sondenNamen_mem {rest : List (CheckDecl D)} {n : String}
    (hm : n ∈ sondenNamen rest) : ∃ d ∈ rest, ∃ t, d.sonde = some (n, t) := by
  revert hm
  induction rest with
  | nil => intro hm; simp [sondenNamen] at hm
  | cons d ds ih =>
    intro hm
    cases hd : d.sonde with
    | none =>
      have e : sondenNamen (d :: ds) = sondenNamen ds := by
        simp [sondenNamen, hd]
      rw [e] at hm
      obtain ⟨d', hmem, t, ht⟩ := ih hm
      exact ⟨d', List.mem_cons.mpr (Or.inr hmem), t, ht⟩
    | some p =>
      obtain ⟨m, t⟩ := p
      have e : sondenNamen (d :: ds) = m :: sondenNamen ds := by
        simp [sondenNamen, hd]
      rw [e] at hm
      rcases List.mem_cons.mp hm with he | hm'
      · exact ⟨d, List.mem_cons.mpr (Or.inl rfl), t, by rw [he]; exact hd⟩
      · obtain ⟨d', hmem, t', ht⟩ := ih hm'
        exact ⟨d', List.mem_cons.mpr (Or.inr hmem), t', ht⟩

/-- A check of the unit carrying a sonde name puts it in the unit's list. -/
theorem sondenNamen_mem_of {d : CheckDecl D} {rest : List (CheckDecl D)}
    {n : String} {t' : String} (hd : d ∈ rest)
    (ht : d.sonde = some (n, t')) : n ∈ sondenNamen rest := by
  revert hd ht
  induction rest with
  | nil => intro hd _; simp at hd
  | cons e es ih =>
    intro hd ht
    cases he : e.sonde with
    | none =>
      have e' : sondenNamen (e :: es) = sondenNamen es := by
        simp [sondenNamen, he]
      rw [e']
      rcases List.mem_cons.mp hd with rfl | hd
      · simp [ht] at he
      · exact ih hd ht
    | some p =>
      obtain ⟨m, t⟩ := p
      have e' : sondenNamen (e :: es) = m :: sondenNamen es := by
        simp [sondenNamen, he]
      rw [e']
      rcases List.mem_cons.mp hd with rfl | hd
      · have h3 : some (m, t) = some (n, t') := by rw [← he]; exact ht
        have hmn : m = n := congrArg Prod.fst (Option.some.inj h3)
        rw [hmn]
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih hd ht))

/-- The decider is exact. -/
theorem sondenEindeutigB_ok {checks : List (CheckDecl D)} :
    sondenEindeutigB checks = true ↔ SondenEindeutig checks := by
  induction checks with
  | nil => simp [sondenEindeutigB, sondenNamen, SondenEindeutig]
  | cons c rest ih =>
    cases hs : c.sonde with
    | none =>
      have e1 : sondenNamen (c :: rest) = sondenNamen rest := by
        simp [sondenNamen, hs]
      have e2 : sondenEindeutigB (c :: rest) = sondenEindeutigB rest := by
        simp [sondenEindeutigB, hs]
      unfold SondenEindeutig
      rw [e1, e2]
      exact ih
    | some p =>
      obtain ⟨n, t⟩ := p
      have e1 : sondenNamen (c :: rest) = n :: sondenNamen rest := by
        simp [sondenNamen, hs]
      have e2 : sondenEindeutigB (c :: rest) =
          (!(rest.any fun d => match d.sonde with
            | none => false
            | some (m, _) => decide (m = n)) && sondenEindeutigB rest) := by
        simp [sondenEindeutigB, hs]
      unfold SondenEindeutig
      rw [e1, e2, List.nodup_cons, Bool.and_eq_true]
      constructor
      · intro h
        obtain ⟨hhead, hrest⟩ := h
        have hmem : n ∉ sondenNamen rest := by
          intro hm
          obtain ⟨d, hmem, t', ht⟩ := sondenNamen_mem hm
          have hfire : (rest.any fun d => match d.sonde with
              | none => false
              | some (m, _) => decide (m = n)) = true := by
            rw [List.any_eq_true]
            exact ⟨d, hmem, by simp [ht]⟩
          simp [hfire] at hhead
        exact ⟨hmem, ih.mp hrest⟩
      · intro h
        obtain ⟨hmem, hrest⟩ := h
        refine ⟨?_, ih.mpr hrest⟩
        rw [Bool.not_eq_true']
        rw [List.any_eq_false]
        intro d hd
        cases hd' : d.sonde with
        | none => simp
        | some q =>
          obtain ⟨m, t'⟩ := q
          have hne : m ≠ n := by
            intro heq
            rw [heq] at hd'
            exact hmem (sondenNamen_mem_of hd hd')
          simp [hne]

/-- The unique binding: the check carries the external name with its exact
    text, and no other-named check of the unit carries that name. -/
def SondenBindung (checks : List (CheckDecl D)) (c : CheckDecl D)
    (name text : String) : Prop :=
  c.sonde = some (name, text) ∧ c ∈ checks ∧
    ∀ d ∈ checks, d.name ≠ c.name → d.sonde.map Prod.fst ≠ some name

/-- A bound name stands in the unit's sonde list. -/
theorem sonde_name_in_namen {checks : List (CheckDecl D)} {c : CheckDecl D}
    {name text : String} (h : SondenBindung checks c name text) :
    name ∈ sondenNamen checks := by
  obtain ⟨hs, hc, _⟩ := h
  exact sondenNamen_mem_of hc (by rw [hs])

/-- The artifact identity: the external name, the build mode and the image
    the run was measured on. -/
structure SondenArtefakt where
  name : String
  testbau : Bool
  bild : String

/-- The artifact fits the check: a bound sonde, the same build mode, and the
    check's exact text under the artifact's name. -/
def artefaktPasst (c : CheckDecl D) (a : SondenArtefakt) : Prop :=
  c.sonde.isSome ∧ c.testbau = a.testbau ∧ ∃ t, c.sonde = some (a.name, t)

/-- The measured status: a `durchgefallen` run on the matching artifact with
    a false verdict. An untrusted log is evidence metadata, never a Lean
    axiom discharging a universal claim. -/
def Gemessen (c : CheckDecl D) (a : SondenArtefakt) (st : ProbenStand)
    (r : CheckReport) : Prop :=
  st = .durchgefallen ∧ r.urteil = false ∧ artefaktPasst c a

/-- Absence stays unmeasured: `nichtGelaufen` never measures. -/
theorem nichtGelaufen_unmeasured {c : CheckDecl D} {a : SondenArtefakt}
    {st : ProbenStand} {r : CheckReport} (h : st = .nichtGelaufen) :
    ¬ Gemessen c a st r := by
  intro g
  obtain ⟨hst, _, _⟩ := g
  exact absurd (h.symm.trans hst) (by decide)

/-- An unexpected true verdict fails that measurement. -/
theorem bestanden_kein_mass {c : CheckDecl D} {a : SondenArtefakt}
    {st : ProbenStand} {r : CheckReport} (h : r.urteil = true) :
    ¬ Gemessen c a st r := by
  intro g
  exact Bool.false_ne_true (g.2.1.symm.trans h)

/-- A stale artifact (wrong name or mode) measures nothing. -/
theorem fremd_artefakt {c : CheckDecl D} {a : SondenArtefakt}
    {st : ProbenStand} {r : CheckReport} (h : ¬ artefaktPasst c a) :
    ¬ Gemessen c a st r := by
  intro g
  exact h g.2.2

/-! ## Fixtures: a bound sonde, measured and refused -/

/-- The fixture check with a bound counterprobe in the test build. -/
def pruefCSonde : CheckDecl pruefD :=
  { pruefC with sonde := some ("ext", "assert x"), testbau := true }

/-- The matching artifact: the test image under the bound name. -/
def sondeTest : SondenArtefakt := ⟨"ext", true, "test"⟩

/-- The negative report the counterprobe run observed. -/
def sondeBerichtFalsch : CheckReport :=
  { proben := [], boeden := [], urteil := false }

/-- The single bound sonde owns its name. -/
theorem sondenEindeutig_zeuge : SondenEindeutig [pruefCSonde] :=
  sondenEindeutigB_ok.mp rfl

/-- A duplicated sonde name breaks the ownership. -/
theorem sondenKonflikt_zeuge :
    ¬ SondenEindeutig [pruefCSonde, pruefCSonde] := fun h => by
  have hb := sondenEindeutigB_ok.mpr h
  simp [sondenEindeutigB, pruefCSonde] at hb

/-- The fixture binding: the check carries its name and text, alone. -/
theorem sondenBindung_zeuge :
    SondenBindung [pruefCSonde] pruefCSonde "ext" "assert x" :=
  ⟨rfl, List.mem_singleton_self _,
    fun d hd hne =>
      absurd (congrArg CheckDecl.name (List.mem_singleton.mp hd)) hne⟩

/-- The bound name stands in the unit's sonde list. -/
theorem sonde_name_in_namen_zeuge : "ext" ∈ sondenNamen [pruefCSonde] :=
  sonde_name_in_namen sondenBindung_zeuge

/-- The measured counterprobe: failed run, false verdict, matching artifact. -/
theorem gemessen_zeuge :
    Gemessen pruefCSonde sondeTest .durchgefallen sondeBerichtFalsch :=
  ⟨rfl, rfl, by decide, rfl, "assert x", rfl⟩

/-- The unrun counterprobe stays unmeasured. -/
theorem ungemessen_zeuge :
    ¬ Gemessen pruefCSonde sondeTest .nichtGelaufen sondeBerichtFalsch :=
  nichtGelaufen_unmeasured rfl

/-- A stale artifact name measures nothing. -/
theorem artefakt_fremd_zeuge :
    ¬ artefaktPasst pruefCSonde ⟨"alt", true, "test"⟩ := by
  intro h
  obtain ⟨_, _, t, ht⟩ := h
  have ht' : (some ("ext", "assert x") : Option (String × String)) =
      some ("alt", t) := ht
  simp at ht'

end Gegenprobe

end Gabbro.Grammatik
