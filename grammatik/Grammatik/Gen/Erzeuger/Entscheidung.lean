/-
  File:      Grammatik/Gen/Erzeuger/Entscheidung.lean
  Subject:   The model's PROOF ARGUMENTS are decidable once the carriers are enumerated: `∀ t : D.Tab`, `∀ g`,
             `∀ L` over an `Aufz` declaration, and the call premise `RufPasst`. The generator decides each
             proof argument with these instances (`if h : P then ... else []`), so a generated term carries a
             real proof, never an assumption.
-/
import Grammatik.Gen.Erzeuger.Grund
import Batteries.Data.List.Perm

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration}

instance decAllTab [Aufz D] (P : D.Tab → Prop) [DecidablePred P] : Decidable (∀ t, P t) :=
  decidable_of_iff (∀ t ∈ Aufz.tab (D := D), P t) ⟨fun h t => h t (Aufz.tab_mem t), fun h t _ => h t⟩

instance decAllGlob [Aufz D] (P : D.Glob → Prop) [DecidablePred P] : Decidable (∀ g, P g) :=
  decidable_of_iff (∀ g ∈ Aufz.glob (D := D), P g) ⟨fun h g => h g (Aufz.glob_mem g), fun h g _ => h g⟩

instance decAllLock [Aufz D] (P : D.Lock → Prop) [DecidablePred P] : Decidable (∀ l, P l) :=
  decidable_of_iff (∀ l ∈ Aufz.lock (D := D), P l) ⟨fun h l => h l (Aufz.lock_mem l), fun h l _ => h l⟩

/-- `∃ c, o = some c ∧ p c` for an option `o`. -/
instance decExOpt {α : Type} (o : Option α) (p : α → Prop) [DecidablePred p] :
    Decidable (∃ c, o = some c ∧ p c) :=
  match o with
  | none => isFalse (by rintro ⟨c, hc, _⟩; cases hc)
  | some c =>
    if h : p c then isTrue ⟨c, rfl, h⟩
    else isFalse (by rintro ⟨c', hc, hp⟩; cases hc; exact h hp)

/-- `∀ c, o = some c → q c` for an option `o`. -/
instance decAllOpt {α : Type} (o : Option α) (q : α → Prop) [DecidablePred q] :
    Decidable (∀ c, o = some c → q c) :=
  match o with
  | none => isTrue (by intro c hc; cases hc)
  | some c =>
    if h : q c then isTrue (by intro c' hc; cases hc; exact h)
    else isFalse (fun hh => h (hh c rfl))

instance decUntermulti {α : Type} [DecidableEq α] (k Λ : List α) : Decidable (Untermulti k Λ) :=
  decidable_of_iff (List.Subperm k Λ)
    ⟨fun ⟨l, h1, h2⟩ => ⟨l, h1.symm, h2⟩, fun ⟨l, h1, h2⟩ => ⟨l, h1.symm, h2⟩⟩

/-- **The call premise is decidable.** -/
instance decRufPasst [Aufz D] (V : Vertrag D) (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) :
    Decidable (RufPasst D V S Λ) :=
  decidable_of_iff
    ((∀ t, S.schreibt t = true → V.schreibt t = true) ∧ (∀ g, S.gschreibt g = true → V.gschreibt g = true) ∧
      Untermulti (S.konsumiert.map (Res.vonMarke D)) Λ ∧ (∀ L, L ∈ S.haelt → Res.held L ∈ Λ) ∧
      (∀ L, Res.held L ∈ Λ → L ∉ S.haelt → ∃ c, S.boden = some c ∧ D.rang L < c) ∧
      (∀ c, V.boden = some c → ∃ c', S.boden = some c' ∧ c ≤ c'))
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun h => ⟨h.hw, h.hg, h.hk, h.hh, h.hx, h.hb⟩⟩

end Gabbro.Grammatik.Gen
