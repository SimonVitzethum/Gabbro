module

public import Core.Beobachtung.Fluss.Beschriftung.Sicht
public import Core.Beobachtung.Fluss.Quellfragment

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Beobachtung

/-- The fragment unit with declared flow levels. It is `Fragment.einheit` with one change:
    the local state of every context is compared through the public view of the declaration.
    The unit has no output journal and no released value yet; those belong to the next stage. -/
def Fragment.beschriftet (p : Fragment) (platform : Plattform) (β : Beschriftung) : Einheit :=
  { p.einheit platform with
    fluss := { fragmentFlussdaten with
      lokal := fun _ => ⟨1, fun _ => ∅, fun r _ => r.sicht β⟩ } }

/-- The per-form duty of the labelled flow rule: at program counter `pc`, two frames with
    equal public views are taken to frames with equal public views. -/
def Befehl.SichtErhaltendBei (β : Beschriftung) (pc : Nat) (f : Befehl) : Prop :=
  ∀ (r₁ r₂ : Rahmen) (live : Nat → Bool), r₁.pc = pc → r₁.sicht β = r₂.sicht β →
    (f.auswerten r₁ live).sicht β = (f.auswerten r₂ live).sicht β

theorem kopf_code {code : List Befehl} {s : Zustand} {c : Kontext} {f : Befehl}
    (h : kopf code s c = some f) : code[(s.lokal c).pc]? = some f := by
  unfold kopf at h
  repeat' split at h
  all_goals first | exact h | cases h

/-- **The labelled flow rule is a source rule.** If every instruction of the fragment keeps the
    public view of the frame at each position where it stands, the labelled unit satisfies
    `FlussLokal`. The start rule needs nothing: the entry frame does not read the start's
    inputs yet, and the unit has no journal. -/
theorem Fragment.beschriftet_fluss_lokal (p : Fragment) (platform : Plattform) (β : Beschriftung)
    (form : ∀ (pc : Nat) (f : Befehl), p.code[pc]? = some f → f.SichtErhaltendBei β pc) :
    FlussLokal (p.beschriftet platform β) := by
  constructor
  · intro s₁ s₂ gleich
    have regionen : s₁.regions = s₂.regions := congrArg (fun proj => proj.2.2.1) gleich
    refine ⟨?_, fun _ => rfl, fun _ => rfl, ?_, rfl, fun _ => rfl⟩
    · intro c _ _
      simp only [I.start, Fragment.beschriftet, Fragment.einheit, startdaten, Zustand.start, regionen]
    · simp only [I.start, Fragment.beschriftet, Fragment.einheit, startdaten, Zustand.start, regionen]
  · intro f
    constructor
    · intro c v w plan u _
      refine ⟨⟨rfl, fun _ _ _ mem => (List.not_mem_nil mem).elim⟩, fun privat => ?_⟩
      exact (Bool.false_ne_true privat.symm).elim
    · intro _ c v₁ w₁ p₁ u₁ v₂ w₂ p₂ u₂ gleich links rechts
      have transfer₁ : [p₁] = [Ast.Semantik.plan] ∧ u₁ = f.nach c v₁ := links.2
      have transfer₂ : [p₂] = [Ast.Semantik.plan] ∧ u₂ = f.nach c v₂ := rechts.2
      rw [(List.cons.inj transfer₁.1).1, (List.cons.inj transfer₂.1).1, transfer₁.2, transfer₂.2]
      obtain ⟨lokale, ende, initial, rechte, leihen, antwort⟩ := gleich
      refine ⟨⟨?_, ende, initial, rechte, leihen, antwort⟩, rfl, rfl⟩
      have region : Zustand.regionLive v₁ c = Zustand.regionLive v₂ c := by
        funext slot
        simp only [Zustand.regionLive, rechte, leihen]
      have kopf₁ : p.code[(v₁.lokal c).pc]? = some f := kopf_code (code := p.code) links.1
      intro d _ _
      change ((Function.update v₁.lokal c (f.auswerten (v₁.lokal c) (Zustand.regionLive v₁ c))) d).sicht β =
        ((Function.update v₂.lokal c (f.auswerten (v₂.lokal c) (Zustand.regionLive v₂ c))) d).sicht β
      rw [region]
      by_cases hd : d = c
      · subst hd
        rw [Function.update_self, Function.update_self]
        exact form _ f kopf₁ (v₁.lokal d) (v₂.lokal d) _ rfl (lokale d ⟨0, Nat.zero_lt_succ _⟩ rfl)
      · rw [Function.update_of_ne hd, Function.update_of_ne hd]
        exact lokale d ⟨0, Nat.zero_lt_succ _⟩ rfl

end Gabbro.Core.Ast.Semantik
