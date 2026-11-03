module

public import Grammatik.Kern.Syntax.Syntax.Teil1
public import Grammatik.Kern.Syntax.Syntax.Teil1b

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The signature's owner interface is checked against a resolved nominal
    namespace. Ordinary consumes and owner handoff cannot spend one identity. -/
structure OwnerSignature (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (owners : List D.Marke) : Prop where
  resolved : ∀ m ∈ owners, ∃ t, m ∈ D.eigner t
  valid : S.owner.Valid (fun m => decide (m ∈ owners)) D.stufen
  ordinaryDisjoint : ∀ p ∈ S.konsumiert, p.1 ∉ S.owner.inputs.map Prod.fst

/-- Every exact combined input is available, with its original multiplicity
    checked by the canonical call premise. -/
theorem RufPasst.input_available {V : Vertrag D}
    {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    (h : RufPasst D V S Λ) {p : D.Marke × Nat} (hp : p ∈ S.inputMarks) :
    Res.vonMarke D p ∈ Λ := by
  obtain ⟨kept, hperm, hsub⟩ := h.hk
  exact hsub.subset (hperm.mem_iff.mp (List.mem_map.mpr ⟨p, hp, rfl⟩))

/-- A loan or moved argument cannot be supplied by copying an ordinary value. -/
theorem RufPasst.owner_input_available {V : Vertrag D}
    {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)}
    (h : RufPasst D V S Λ) {p : D.Marke × Nat} (hp : p ∈ S.owner.inputs) :
    Res.vonMarke D p ∈ Λ :=
  h.input_available (List.mem_append_right _ hp)

/-- Erasing resource inputs cannot introduce another resource. -/
theorem owner_resource_erase_mem {xs : List (D.Marke × Nat)} {Λ : List (Res D)}
    {r : Res D} (h : r ∈ xs.foldl (fun acc p => acc.erase (Res.vonMarke D p)) Λ) :
    r ∈ Λ := by
  induction xs generalizing Λ with
  | nil => exact h
  | cons x xs ih => exact List.mem_of_mem_erase (ih h)

/-- The canonical call transformer preserves owner provenance even when the
    returned stage differs. Ordinary production still cannot create an owner. -/
theorem owner_nachSig_from_input (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (hn : ∀ m s, (∃ t, m ∈ D.eigner t) → (m, s) ∉ S.produziert)
    (Λ : List (Res D)) (ha : ∀ p ∈ S.owner.inputs, Res.vonMarke D p ∈ Λ)
    {m : D.Marke} {s : Nat} (ho : ∃ t, m ∈ D.eigner t)
    (h : Res.marke m s ∈ nachSig D S Λ) :
    ∃ before, Res.marke m before ∈ Λ := by
  rcases List.mem_append.mp h with h | h
  · exact ⟨s, owner_resource_erase_mem h⟩
  · obtain ⟨⟨n, stage⟩, hp, he⟩ := List.mem_map.mp h
    cases he
    rcases List.mem_append.mp hp with hp | hp
    · exact False.elim (hn m s ho hp)
    · obtain ⟨before, hb⟩ := S.owner.output_from_input hp
      exact ⟨before, ha (m, before) hb⟩

/-- The canonical direct-call rule supplies the provenance theorem's exact
    availability premise; no separate owner-call API or post-call transformer. -/
theorem RufPasst.owner_provenance {V : Vertrag D} {f : D.Fn} {Λ : List (Res D)}
    (hp : RufPasst D V (D.signatur f) Λ) {m : D.Marke} {s : Nat}
    (ho : ∃ t, m ∈ D.eigner t) (h : Res.marke m s ∈ nach D f Λ) :
    ∃ before, Res.marke m before ∈ Λ :=
  owner_nachSig_from_input (D.signatur f)
    (fun m s ⟨t, ht⟩ => D.eigner_nie_erzeugt (D.sig f) t m s ht)
    Λ (fun _ h => hp.owner_input_available h) ho h

/-- The old ordinary-only specialization preserves the exact stage. -/
theorem owner_nachSig_ordinary (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (hn : ∀ m s, (∃ t, m ∈ D.eigner t) → (m, s) ∉ S.produziert)
    (hf : S.owner = {}) (Λ : List (Res D)) {m : D.Marke} {s : Nat}
    (ho : ∃ t, m ∈ D.eigner t) (h : Res.marke m s ∈ nachSig D S Λ) :
    Res.marke m s ∈ Λ := by
  rcases List.mem_append.mp h with h | h
  · exact owner_resource_erase_mem h
  · obtain ⟨⟨n, stage⟩, hp, he⟩ := List.mem_map.mp h
    cases he
    have hprod : (m, s) ∈ S.produziert := by
      simpa only [Signatur.outputMarks, hf, OwnerFlow.outputs, List.filterMap_nil,
        List.append_nil] using hp
    exact False.elim (hn m s ho hprod)

end Gabbro.Grammatik
