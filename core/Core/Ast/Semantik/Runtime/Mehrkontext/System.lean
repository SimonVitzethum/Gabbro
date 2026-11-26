/-
  File:      core/Core/Ast/Semantik/Runtime/Mehrkontext/System.lean
  Subject:   THE SYSTEM OF FORMS OVER ALL CONTEXTS (MK-01). `I.Bestimmt` and `I.Fortschritt` hold for the
             forms of every context, not only for the entry context (`system_bestimmt`,
             `system_fortschritt`). Satisfiability (`mehrkontext_erfuellbar`): a fragment with the body of the
             entry context and the body of a handler, in a machine state where the handler has been delivered,
             in which both contexts have their own head, both steps are `I` steps, the two orders of the steps
             reach the same state, and each context advanced its own frame.
-/
module

public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Runtime.Mehrkontext.Start

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- The head of a context is an instruction of the code. -/
theorem kopf_mem {code : List Befehl} {s : Zustand} {c : Kontext} {b : Befehl}
    (head : kopf code s c = some b) : b ∈ code := by
  unfold kopf at head
  repeat' split at head
  all_goals first | exact List.mem_of_getElem? head | cases head

/-- **`I.Bestimmt` for the frame-only forms of every context.** An access instruction chooses the value it
    reads (the memory model's choice, `Speicherwahl`), so the determinacy of a system with access
    instructions is the one of `ZugriffBestimmtAussage` (up to the value read), not this one. -/
theorem system_bestimmt (code : List Befehl) (privat : ∀ b ∈ code, b.Privat) :
    Ideal.IBestimmt (system code) := by
  intro c s w es es' s1 s2 ⟨i, hi, h1⟩ ⟨j, hj, h2⟩
  rw [hi] at hj
  cases hj
  exact (i.bestimmt (privat i (kopf_mem hi))) c s w es es' s1 s2 h1 h2

/-- **`I.Fortschritt` for the frame-only forms of every context.** A context without a head is finished; a
    context with one has its `I` step. -/
theorem system_fortschritt (code : List Befehl) (privat : ∀ b ∈ code, b.Privat) :
    Ideal.IFortschritt (system code) :=
  Ideal.fortschritt_aus_regeln (system code) (fun _ _ finished => finished)
    (fun b s c head =>
      Or.inl ⟨(), [b.plan (s.lokal c) 0], b.nach c s,
        (b.ideal_privat (privat b (kopf_mem head)) c s () [b.plan (s.lokal c) 0]
          (b.nach c s)).2 ⟨rfl, rfl⟩⟩)

/-- A fragment with two bodies: the entry context writes the literal `1` to the temporary `0`, the
    handler `0 0 0` writes the literal `2` to the same temporary of its own frame. -/
def zweiKontexte : Fragment :=
  (Fragment.einzel (.literal 0 1)).anhaengen
    ((Fragment.einzel (.literal 0 2)).rumpf (fun c => decide (c = .handler 0 0 0)))

theorem zweiKontexte_eintritte : zweiKontexte.eintritte (.handler 0 0 0) = some 1 := rfl

/-- **Satisfiability of the multi-context system.** After the machine delivers the interrupt to the
    handler `0 0 0` of the fragment, both contexts have their own head; both steps are `I` steps in
    both orders; the orders reach the same state; and each context advanced its own frame:
    the entry context holds `1`, the handler `2`, both at the temporary `0`. -/
theorem mehrkontext_erfuellbar (platform : Plattform) (start : AussenStart) :
    let E := zweiKontexte.einheit platform
    let c : Kontext := .handler 0 0 0
    let s₁ := Zustandseintritt (I.start E start).2 0 (0, 0) c false
    let b₁ : Befehl := .literal 0 1
    let b₂ : Befehl := .literal 0 2
    E.system.kopf s₁ eintritt = some b₁ ∧ E.system.kopf s₁ c = some b₂ ∧
      E.system.IErreichbar s₁ (b₂.nach c (b₁.nach eintritt s₁)) ∧
      E.system.IErreichbar s₁ (b₁.nach eintritt (b₂.nach c s₁)) ∧
      b₂.nach c (b₁.nach eintritt s₁) = b₁.nach eintritt (b₂.nach c s₁) ∧
      ((b₂.nach c (b₁.nach eintritt s₁)).lokal eintritt).pc = 1 ∧
      ((b₂.nach c (b₁.nach eintritt s₁)).lokal c).pc = 2 ∧
      (((b₂.nach c (b₁.nach eintritt s₁)).lokal eintritt).zahl 0).map (fun z => z.zahl.wert) = some 1 ∧
      (((b₂.nach c (b₁.nach eintritt s₁)).lokal c).zahl 0).map (fun z => z.zahl.wert) = some 2 := by
  intro E c s₁ b₁ b₂
  have differ : Kontext.handler 0 0 0 ≠ eintritt := fun same => Kontext.noConfusion same
  have head₁ : E.system.kopf s₁ eintritt = some b₁ := rfl
  have head₂ : E.system.kopf s₁ c = some b₂ := by
    have entry : zweiKontexte.eintritte c = some 1 := zweiKontexte_eintritte
    exact (handler_beginnt_im_rumpf zweiKontexte platform start 0 (0, 0) c false differ entry).trans rfl
  -- the other context's step leaves a head in place
  have head₂' : E.system.kopf (b₁.nach eintritt s₁) c = some b₂ := by
    have same : kopf zweiKontexte.code (b₁.nach eintritt s₁) c = kopf zweiKontexte.code s₁ c :=
      kopf_kontextgleich rfl (b₁.nach_lokal_anderer differ s₁)
    exact same.trans head₂
  have head₁' : E.system.kopf (b₂.nach c s₁) eintritt = some b₁ := by
    have same : kopf zweiKontexte.code (b₂.nach c s₁) eintritt = kopf zweiKontexte.code s₁ eintritt :=
      kopf_kontextgleich rfl (b₂.nach_lokal_anderer (Ne.symm differ) s₁)
    exact same.trans head₁
  have step₁ : E.system.IErreichbar s₁ (b₁.nach eintritt s₁) :=
    .schritt eintritt () [plan] .start ⟨b₁, head₁, rfl, rfl⟩
  have step₂ : E.system.IErreichbar s₁ (b₂.nach c s₁) :=
    .schritt c () [plan] .start ⟨b₂, head₂, rfl, rfl⟩
  have both : E.system.IErreichbar s₁ (b₂.nach c (b₁.nach eintritt s₁)) :=
    .schritt c () [plan] step₁ ⟨b₂, head₂', rfl, rfl⟩
  have both' : E.system.IErreichbar s₁ (b₁.nach eintritt (b₂.nach c s₁)) :=
    .schritt eintritt () [plan] step₂ ⟨b₁, head₁', rfl, rfl⟩
  exact ⟨head₁, head₂, both, both', b₂.nach_kommutiert b₁ differ s₁, rfl, rfl, rfl, rfl⟩

end Gabbro.Core.Ast.Semantik
