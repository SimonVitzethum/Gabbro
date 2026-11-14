module
public import Bruecke.Anweisung.Lokal.Kopf
public import Bruecke.Realisierung
public import Bruecke.Anweisung.Lokal.Benannt
@[expose] public section

/-!
# Local-binding and trailing-return frame facts

A local binding leaves the world unchanged. A translated trailing return is either empty
or one return statement. The carried frame proof in `Kette/` reuses these two facts.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

theorem step_bindName (ρ : Gabbro.Body.Env) (n : String) (e : Gabbro.Body.Expr)
    (t : Gabbro.Body.State) :
    Gabbro.Body.step ρ (.bindName n e) t = .stuck ∨
      ∃ v, Gabbro.Body.step ρ (.bindName n e) t =
        .running ⟨t.world, Gabbro.Body.bindLocal t.local' n v⟩ := by
  simp only [Gabbro.Body.step]
  split
  · rename_i v _
    exact .inr ⟨v, rfl⟩
  · exact .inl rfl

theorem namedEnd_rets {fn : UFn} {ns : BodyNames} {r : URet} {eB : List Gabbro.Body.Stmt}
    (h : namedEnd u fn ns r = some eB) : ∀ x ∈ eB, ∃ e, x = .ret (some e) := by
  intro x hx
  cases r
  case empty =>
    simp only [namedEnd, Option.some.injEq] at h
    subst h
    cases hx
  case val v | wert v =>
    simp only [namedEnd] at h
    cases hs : namedSide u fn ns v with
    | none => rw [hs] at h; cases h
    | some e =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp at hx
      exact ⟨e, hx⟩
  case bool v =>
    simp only [namedEnd] at h
    cases hs : condZ u fn ns v with
    | none => rw [hs] at h; cases h
    | some e =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp at hx
      exact ⟨e, hx⟩
  all_goals simp only [namedEnd, reduceCtorEq] at h

end Gabbro.Bruecke
