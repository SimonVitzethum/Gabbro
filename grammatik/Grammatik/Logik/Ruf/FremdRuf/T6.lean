/- Part 6 of `FremdRuf` (C08): the provider transition in STEP form.

   `ProviderOk` (T4) is an inductive history judgment. A binding proves something
   about ONE step, not about a history, so the user obligation is the step form:
   `ProviderSchritt inv r` says what a record `r` must meet against the live
   inventory `inv` (frame, and exactly one of: fresh disjoint success grant, failure
   without grant, declared release of a live grant). `ProviderBindung O Kan` is the
   binding's promise -- every canonical (`Kan`) record linked to `O` meets its step against
   every inventory some realized history reaches -- and `providerRealisiert_aus_bindung`
   derives `ProviderRealisiert O H` for every history of canonical records linked to `O`.
   The disjointness leg of `ProviderTreueG` is then NOT a separate duty: freshness of
   every success grant makes the live inventory pairwise disjoint
   (`providerOk_paarweise`, `providerTreueG_of_realisiert`).

   Ghost data only: nothing here is emitted, and the physical injective mapping to the
   actual binding memory stays with C12/IR-06. -/
module

public import Grammatik.Logik.Ruf.FremdRuf.T5

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Overlap of two grants is symmetric. -/
theorem Konzession.ueberschneidet_symm {j k : Konzession D} (h : j.ueberschneidet k) :
    k.ueberschneidet j := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

/-- The record is the actual answer of the binding `O` at its entry world and arguments. -/
def RecordGebunden (O : Orakel D) (r : BoundaryRecord D) : Prop :=
  O.wirkt r.ax r.eingabe r.args = (r.ausgabe, r.roh)

/-- **One provider step against the live inventory `inv`**: the declared frame holds,
    and exactly one of: a success with a positive, aligned grant fresh against every
    live grant and no release; a failure with no grant and no release; a declared
    release of a live grant with no new grant. -/
def ProviderSchritt (inv : List (Konzession D)) (r : BoundaryRecord D) : Prop :=
  Rahmen (D.aschreibt r.ax) (D.agschreibt r.ax) r.eingabe r.ausgabe ∧
  ((r.erfolg = true ∧ ∃ k : Konzession D, r.konzession = some k ∧ 0 < k.laenge ∧
      0 < k.ausrichtung ∧ (∀ j ∈ inv, ¬ j.ueberschneidet k) ∧ r.freigabe = none) ∨
   (r.erfolg = false ∧ r.konzession = none ∧ r.freigabe = none) ∨
   (∃ key : D.Tab × Int, r.freigabe = some key ∧ r.konzession = none ∧
      ∃ k ∈ inv, k.schluessel = key))

/-- A realized history extends by one linked step that meets its step judgment. -/
theorem providerOk_schritt {O : Orakel D} {inv : List (Konzession D)}
    {H : List (BoundaryRecord D)} (h : ProviderOk O inv H) {r : BoundaryRecord D}
    (link : RecordGebunden O r) (hs : ProviderSchritt inv r) :
    ProviderOk O (grantSchritt inv r) (H ++ [r]) := by
  obtain ⟨frame, hcase⟩ := hs
  rcases hcase with ⟨ok, k, hk, pos, align, frisch, frei⟩ | ⟨ok, nogrant, frei⟩ |
      ⟨key, hk, nogrant, live⟩
  · rw [grantSchritt_erfolg inv r k frei ok hk]
    exact ProviderOk.erfolg h r link frame ok k hk pos align frisch frei
  · rw [grantSchritt_fehler inv r frei ok nogrant]
    exact ProviderOk.fehler h r link frame ok nogrant frei
  · rw [grantSchritt_freigabe inv r key hk]
    exact ProviderOk.freigabe h r link frame key hk nogrant live

/-- **The binding's promise (C08 user obligation, step form).** Every CANONICAL record linked
    to `O` meets its provider step against every inventory a realized history reaches. `Kan`
    is the decoding of the declared grant identity (success, grant, release) from the actual
    answer and the item's boundary clauses: a record is a fact about the answer, so the
    promise concerns the records the answer determines, never an arbitrary record whose free
    grant fields claim more (such a promise would be unsatisfiable). Software providers
    discharge it from their proved implementation; it is not a hardware assumption. -/
def ProviderBindung (O : Orakel D) (Kan : BoundaryRecord D → Prop) : Prop :=
  ∀ (inv : List (Konzession D)) (H : List (BoundaryRecord D)), ProviderOk O inv H →
    ∀ r : BoundaryRecord D, RecordGebunden O r → Kan r → ProviderSchritt inv r

/-- Every history whose records are linked to `O` and canonical is realized when `O` keeps
    the promise. -/
theorem providerRealisiert_aus_bindung {O : Orakel D} {Kan : BoundaryRecord D → Prop}
    (hb : ProviderBindung O Kan) :
    ∀ H : List (BoundaryRecord D), (∀ r ∈ H, RecordGebunden O r ∧ Kan r) →
      ProviderRealisiert O H := by
  have key : ∀ n : Nat, ∀ H : List (BoundaryRecord D), H.length = n →
      (∀ r ∈ H, RecordGebunden O r ∧ Kan r) → ProviderRealisiert O H := by
    intro n
    induction n with
    | zero =>
      intro H hl _
      have h0 : H = [] := List.eq_nil_of_length_eq_zero hl
      rw [h0]
      exact providerRealisiert_nil O
    | succ n ih =>
      intro H hl hg
      rcases List.eq_nil_or_concat H with h0 | ⟨L, r, hLr⟩
      · rw [h0]
        exact providerRealisiert_nil O
      · rw [List.concat_eq_append] at hLr
        rw [hLr] at hl hg
        have hl' : L.length = n := by simpa using hl
        obtain ⟨inv, hinv⟩ := ih L hl' (fun r' hr' => hg r' (List.mem_append_left _ hr'))
        have hr : RecordGebunden O r ∧ Kan r :=
          hg r (List.mem_append_right _ (List.mem_singleton_self r))
        rw [hLr]
        exact ⟨grantSchritt inv r, providerOk_schritt hinv hr.1 (hb inv L hinv r hr.1 hr.2)⟩
  intro H hg
  exact key H.length H rfl hg

/-- A realized history keeps its live grants pairwise disjoint: success grants are fresh. -/
theorem providerOk_paarweise {O : Orakel D} {inv : List (Konzession D)}
    {H : List (BoundaryRecord D)} (h : ProviderOk O inv H) :
    inv.Pairwise (fun j k => ¬ j.ueberschneidet k) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | erfolg h r link frame ok k hk pos align frisch frei ih =>
    rw [List.pairwise_append]
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [hb]
    exact frisch a ha
  | fehler h r link frame ok nogrant frei ih => exact ih
  | freigabe h r link frame key hk nogrant live ih => exact ih.filter _

/-- The disjointness leg of `ProviderTreueG` is implied by its realization leg. -/
theorem providerTreueG_of_realisiert {O : Orakel D} {H : List (BoundaryRecord D)}
    (h : ProviderRealisiert O H) : ProviderTreueG O H := by
  refine ⟨h, ?_⟩
  obtain ⟨inv, hinv⟩ := h
  have heq : inv = GrantInventory H := providerOk_inventar hinv
  have hpw : (GrantInventory H).Pairwise (fun j k => ¬ j.ueberschneidet k) := by
    rw [← heq]
    exact providerOk_paarweise hinv
  intro i j hne
  rcases Nat.lt_or_gt_of_ne (fun hij => hne (Fin.ext hij)) with hlt | hgt
  · exact hpw.rel_getElem_of_lt i.2 j.2 hlt
  · intro hov
    exact hpw.rel_getElem_of_lt j.2 i.2 hgt (Konzession.ueberschneidet_symm hov)

/-- Provider fidelity from the binding's promise, for every history linked to `O`. -/
theorem providerTreueG_aus_bindung {O : Orakel D} {Kan : BoundaryRecord D → Prop}
    (hb : ProviderBindung O Kan) {H : List (BoundaryRecord D)}
    (hg : ∀ r ∈ H, RecordGebunden O r ∧ Kan r) : ProviderTreueG O H :=
  providerTreueG_of_realisiert (providerRealisiert_aus_bindung hb H hg)

end Gabbro.Grammatik
