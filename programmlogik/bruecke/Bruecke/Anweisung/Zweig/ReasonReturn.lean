module
public import Bruecke.Kette.Verknuepfung
public import Bruecke.Anweisung.Lokal.Benannt
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- The existing Body return represents the separate reason channel by a tagged value. -/
theorem reasonReturn_step (ρB : Gabbro.Body.Env) (s : Gabbro.Body.State) (n : Nat) :
    Gabbro.Body.step ρB (reasonReturn n) s = .returned s (some (.reason (caseLabel n))) := rfl

theorem lowRetWhyStmt_ok {l : Bool} {c : Fin u.fns.length} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {n : Nat}
    {st : Stmt (declOf u) (verOf u c) l Γ Λ Λ}
    (h : lowRetStmt (l := l) u c Γ fn Λ [] (.why n) = .ok st) :
    ∃ (hn : n < (verOf u c).gruende) (hp : Λ.Perm (verOf u c).ende),
      st = .retWhy ⟨n, hn⟩ hp := by
  simp only [lowRetStmt] at h
  split at h
  · rename_i hn
    split at h
    · rename_i hp
      cases h
      exact ⟨hn, of_decide_eq_true hp, rfl⟩
    · cases h
  · cases h

theorem lowRetWhyEnd_ok {l : Bool} {c : Fin u.fns.length} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {n : Nat}
    {st : Endblock (declOf u) (verOf u c) l Γ Λ}
    (h : lowRetEnd (l := l) u c Γ fn Λ [] (.why n) = .ok st) :
    ∃ (hn : n < (verOf u c).gruende) (hp : Λ.Perm (verOf u c).ende),
      st = .retWhy ⟨n, hn⟩ hp := by
  simp only [lowRetEnd] at h
  split at h
  · rename_i hn
    split at h
    · rename_i hp
      cases h
      exact ⟨hn, of_decide_eq_true hp, rfl⟩
    · cases h
  · cases h

theorem lowEndWhy_ok {c : Fin u.fns.length} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {n : Nat}
    {st : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEnd u c Γ Λ fn (.why n) = .ok st) :
    ∃ (hn : n < (verOf u c).gruende) (hp : Λ.Perm (verOf u c).ende),
      st = .retWhy ⟨n, hn⟩ hp := by
  simp only [lowEnd] at h
  split at h
  · rename_i hn
    split at h
    · rename_i hp
      cases h
      exact ⟨hn, of_decide_eq_true hp, rfl⟩
    · cases h
  · cases h

/-- No answer-table sample is needed for a local reason return. -/
theorem ausgangZiel_why {l : Bool} {c : Fin u.fns.length}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {fn : UFn} {ids : List String} {σ : World (declOf u)}
    {s : Gabbro.Body.State} (r : Fin (verOf u c).gruende) (hW : WGRel u σ s.world) :
    AusgangZiel_G u C c R fn ids (Ausgang.why (l := l) (Γ := Γ) σ r) s [reasonReturn r.val] := by
  refine ⟨(fun _ h => by cases h), (fun _ _ h => by cases h),
    (fun _ _ h => by cases h), ?_, ?_⟩
  · intro leave hl σ' ρ' h
    cases leave <;> simp only [controlG, Bool.false_eq_true, ↓reduceIte] at h <;> cases h
  · intro σ' r' h
    cases h
    exact ⟨[], (by simp), (by simp [Oben]), List.Pairwise.nil,
      fun ρB _ _ => ⟨s, by simp only [Gabbro.Body.exec, reasonReturn_step], hW⟩⟩

end Gabbro.Bruecke
