/-
  File:      Grammatik/Isabelle/VerbundKonstruktor.lean
  Port of:   beweise/Verbund_Konstruktor.thy (template `verbund.konstruktor`, S18)

  The generated constructor sets every field exactly once and leaves none
  uninitialized. The two halves are ONE as soon as the declaration is
  well-formed: when the association list has exactly the field list as its key
  sequence, both hold at once -- none twice and none missing. The actual
  theorem: under coverage, reading a field yields EXACTLY the value the
  constructor wrote there.

  Adaptations (same content, Lean core without mathlib):
  - `feld` is `String` (Isabelle: `type_synonym feld = string`).
  - `map_of` becomes the explicit reader `liest`; sets become membership
    statements (`x ∈ map fst zs ↔ x ∈ fs` for the "same set" half).
  - `distinct` becomes the explicit `keineDopplung` (same definition).
-/

namespace Gabbro.Grammatik.Isabelle.VerbundKonstruktor

/-- A field name. (Isabelle: `type_synonym feld = string`.) -/
abbrev Feld := String

/-- Well-formed: no field twice. (Isabelle: `wohlgeformt`.) -/
def wohlgeformt (fs : List Feld) : Prop := fs.Nodup

/-- Coverage: the association list has exactly the field list as its key
    sequence. The STRICTER form: declaration ORDER, not just the same set --
    chosen because a field list in a `format` IS an order anyway.
    (Isabelle: `deckt`.) -/
def deckt (fs : List Feld) (zs : List (Feld × Nat)) : Prop :=
  (zs.map Prod.fst) = fs

/-- Read a field. (Isabelle: `liest`, `map_of`.) -/
def liest : List (Feld × Nat) → Feld → Option Nat
  | [], _ => none
  | (a, b) :: rest, f => if a = f then some b else liest rest f

/-- The two halves are ONE: under coverage the keys are distinct AND the same
    set. (Isabelle: `deckt_setzt_jedes_genau_einmal`.) -/
theorem deckt_setzt_jedes_genau_einmal (fs : List Feld) (zs : List (Feld × Nat))
    (hwf : wohlgeformt fs) (hdk : deckt fs zs) :
    (zs.map Prod.fst).Nodup ∧ ∀ x, x ∈ zs.map Prod.fst ↔ x ∈ fs := by
  simp only [deckt] at hdk
  rw [hdk]
  exact ⟨hwf, fun x => Iff.rfl⟩

/-- Coverage misses none: every declared field occurs.
    (Isabelle: `deckt_laesst_keins_aus`.) -/
theorem deckt_laesst_keins_aus (fs : List Feld) (zs : List (Feld × Nat))
    (hdk : deckt fs zs) (f : Feld) (hdrin : f ∈ fs) :
    ∃ v, (f, v) ∈ zs := by
  revert hdk hdrin
  induction zs generalizing fs f with
  | nil =>
    intro hdk hdrin
    simp only [deckt, List.map_nil] at hdk
    rw [←hdk] at hdrin
    simp at hdrin
  | cons p rest ih =>
    intro hdk hdrin
    simp only [deckt, List.map_cons] at hdk
    rw [←hdk] at hdrin
    simp only [List.mem_cons] at hdrin
    rcases hdrin with rfl | hmem
    · obtain ⟨a, b⟩ := p
      exact ⟨b, List.mem_cons.mpr (Or.inl rfl)⟩
    · obtain ⟨v, hm⟩ := ih (rest.map Prod.fst) f rfl hmem
      exact ⟨v, List.mem_cons.mpr (Or.inr hm)⟩

/-- Reading is unique: under coverage, reading a field yields exactly the
    value the constructor wrote there. (Isabelle: `ablesung_ist_eindeutig`.) -/
theorem ablesung_ist_eindeutig (fs : List Feld) (zs : List (Feld × Nat))
    (hwf : wohlgeformt fs) (hdk : deckt fs zs)
    (f : Feld) (v : Nat) (hdrin : (f, v) ∈ zs) :
    liest zs f = some v := by
  revert hwf hdk hdrin
  induction zs generalizing fs f with
  | nil =>
    intro _ _ hdrin
    simp at hdrin
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    intro hwf hdk hdrin
    have hdk' : a :: rest.map Prod.fst = fs := hdk
    have hwf' : fs.Nodup := hwf
    rw [←hdk'] at hwf'
    rw [List.nodup_cons] at hwf'
    obtain ⟨hnotin, hrest⟩ := hwf'
    simp only [List.mem_cons] at hdrin
    simp only [liest]
    rcases Decidable.em (a = f) with haf | haf
    · rw [if_pos haf]
      rcases hdrin with heq | hmem
      · have hbv : b = v := by
          have h2 := congrArg Prod.snd heq
          simpa using h2.symm
        rw [hbv]
      · exfalso
        apply hnotin
        have hmem' : f ∈ rest.map Prod.fst := by
          rw [List.mem_map]
          exact ⟨(f, v), hmem, rfl⟩
        rw [←haf] at hmem'
        exact hmem'
    · rw [if_neg haf]
      rcases hdrin with heq | hmem
      · exfalso
        apply haf
        have h2 := congrArg Prod.fst heq
        simpa using h2.symm
      · exact ih (rest.map Prod.fst) f hrest rfl hmem

/-- Every field has a value. (Isabelle: `jedes_feld_hat_einen_wert`.) -/
theorem jedes_feld_hat_einen_wert (fs : List Feld) (zs : List (Feld × Nat))
    (hwf : wohlgeformt fs) (hdk : deckt fs zs)
    (f : Feld) (hdrin : f ∈ fs) :
    ∃ v, liest zs f = some v := by
  obtain ⟨v, hmem⟩ := deckt_laesst_keins_aus fs zs hdk f hdrin
  exact ⟨v, ablesung_ist_eindeutig fs zs hwf hdk f v hmem⟩

/-! ## Witness: a concrete struct -/

/-- Witness: the two-field struct `["x", "y"]` covered by `[("x", 1),
    ("y", 2)]` reads back exactly -- and every field has a value. No lemma
    above quantifies over syntax, so the inhabitation obligation is vacuous;
    this is a data-level witness. -/
theorem verbund_zeuge :
    liest [("x", 1), ("y", 2)] "x" = some 1 ∧
    liest [("x", 1), ("y", 2)] "y" = some 2 ∧
    (∃ v, liest [("x", 1), ("y", 2)] "y" = some v) := by
  have hwf : wohlgeformt ["x", "y"] := by
    simp [wohlgeformt, List.nodup_cons, List.nodup_nil]
  have hdk : deckt ["x", "y"] [("x", 1), ("y", 2)] := rfl
  refine ⟨?_, ?_, ⟨2, ?_⟩⟩
  · exact ablesung_ist_eindeutig _ _ hwf hdk _ _ (by decide)
  · exact ablesung_ist_eindeutig _ _ hwf hdk _ _ (by decide)
  · exact ablesung_ist_eindeutig _ _ hwf hdk _ _ (by decide)

/-! ## Bridge

  The Lean syntax ties a `format` (and a struct) to a `Tab` with `count 1`
  (`Syntax.lean` §9: "`format` = `Tab` mit `count 1`"), whose single slot's
  fields are named by `D.Feld`. That the EMITTER establishes `deckt` -- one
  value per declared field, in declaration order -- is the PL.3 bridge and is
  NOT shown here, exactly as the Isabelle theory does not show it (M-2
  there): a mutation setting a field TWICE or NOT AT ALL must fail, and this
  file's theorems say which damage that is. Named, not faked. -/

#print axioms Gabbro.Grammatik.Isabelle.VerbundKonstruktor.deckt_setzt_jedes_genau_einmal
#print axioms Gabbro.Grammatik.Isabelle.VerbundKonstruktor.deckt_laesst_keins_aus
#print axioms Gabbro.Grammatik.Isabelle.VerbundKonstruktor.ablesung_ist_eindeutig
#print axioms Gabbro.Grammatik.Isabelle.VerbundKonstruktor.jedes_feld_hat_einen_wert
#print axioms Gabbro.Grammatik.Isabelle.VerbundKonstruktor.verbund_zeuge

end Gabbro.Grammatik.Isabelle.VerbundKonstruktor
