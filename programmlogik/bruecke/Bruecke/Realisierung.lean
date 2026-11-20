module
public import Bruecke.Lauf
@[expose] public section


/-!
# Shared call-graph and realization facts

`Rang` requires each direct call to decrease a rank. `hyps_elim` supplies Body's call duties
from an environment's contracts and frames. The call lookup and membership lemmas connect
these duties to the carried set in `Kette/`.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. Static facts of the lowered statements -/

theorem any_mem {l : List String} {x : String} (h : l.any (· == x) = true) : x ∈ l := by
  rw [List.any_eq_true] at h
  obtain ⟨y, hy, he⟩ := h
  have : y = x := by simpa using he
  exact this ▸ hy

theorem step_assign (ρ : Gabbro.Body.Env) (cn : String) (idx : Gabbro.Body.Expr) (fld : String)
    (ve : Gabbro.Body.Expr) (t : Gabbro.Body.State) :
    Gabbro.Body.step ρ (.assign cn idx fld ve) t = .stuck ∨
      ∃ k v, Gabbro.Body.step ρ (.assign cn idx fld ve) t =
        .running ⟨Gabbro.Body.store t.world (.slot cn k fld) v, t.local'⟩ := by
  simp only [Gabbro.Body.step]
  split
  · rename_i k v _ _
    exact .inr ⟨k, v, rfl⟩
  · exact .inl rfl

theorem step_call (ρ : Gabbro.Body.Env) (g : String) (ps : List String) (es : List Gabbro.Body.Expr)
    (pre : Gabbro.Body.Expr) (t : Gabbro.Body.State) :
    Gabbro.Body.step ρ (.call g ps es pre) t = .stuck ∨
      ∃ t' : Gabbro.Body.State, t'.world = t.world ∧ Gabbro.Body.step ρ (.call g ps es pre) t =
        .running ⟨(ρ g t').1.world, t.local'⟩ := by
  simp only [Gabbro.Body.step]
  split
  · rename_i vs _
    split
    · exact .inr ⟨⟨t.world, Gabbro.Body.bindAll ps vs (fun _ => .absent)⟩, rfl, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-! ## 3. The environment, rank by rank -/

/-- **The call graph has a rank**: every call goes to a name of strictly smaller rank. Checked
    per unit (`rangB`). -/
def Rang (u : UProg) (rk : String → Nat) : Prop :=
  ∀ c : Fin u.fns.length, ∀ cname args, CallsIn (fnAt u c).body cname args →
    rk cname < rk (fnAt u c).name

/-- The promise of `gf` as the duty file states it. -/
def postP (u : UProg) (gf : UFn) : Gabbro.Body.State → Gabbro.Body.State →
    Option Gabbro.Body.Value → Prop :=
  fun s s' r => (postU u (wfU u) gf s s' r).getD False

theorem hyps_elim (wf : Gabbro.Body.State → Prop) (ρ : Gabbro.Body.Env) : ∀ (gs : List String) (C : Prop),
    (∀ g ∈ gs, ∃ gf, fnSuch u g = some gf ∧
      Gabbro.Body.Contract ρ g (preProp wf gf) (fun s s' r => (postU u wf gf s s' r).getD False) ∧
      Gabbro.Body.Frame ρ g (writesU gf)) → hyps u wf ρ gs C → C
  | [], C, _, h => h
  | g :: gs, C, hg, h => by
      obtain ⟨gf, hgf, hc, hfr⟩ := hg g (List.mem_cons_self ..)
      simp only [hyps, hgf] at h
      exact hyps_elim wf ρ gs C (fun g' hm => hg g' (List.mem_cons_of_mem _ hm)) (h hc hfr)

theorem mem_insertS {x y : String} : ∀ {l : List String}, y ∈ insertS x l → y = x ∨ y ∈ l
  | [], h => by simp [insertS] at h; exact .inl h
  | z :: zs, h => by
      unfold insertS at h
      split at h
      · simpa using h
      · split at h
        · exact .inr h
        · rcases List.mem_cons.mp h with h | h
          · exact .inr (h ▸ List.mem_cons_self ..)
          · rcases mem_insertS h with h | h
            · exact .inl h
            · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_sortDedup {y : String} : ∀ {l : List String}, y ∈ sortDedup l → y ∈ l
  | [], h => h
  | x :: xs, h => by
      rcases mem_insertS h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_sortDedup h)

theorem mem_calleesOf {f : UFn} {g : String} (h : g ∈ calleesOf f) :
    ∃ args, CallsIn f.body g args := by
  have h' := mem_sortDedup h
  rw [List.mem_filterMap] at h'
  obtain ⟨st, hst, hg⟩ := h'
  cases hc : directCall st with
  | none => simp only [hc, Option.map_none, reduceCtorEq] at hg
  | some p =>
    obtain ⟨name, args⟩ := p
    simp only [hc, Option.map_some, Option.some.injEq] at hg
    subst name
    exact ⟨args, st, hst, hc⟩

theorem fnSuch_mem {n : String} {gf : UFn} (h : fnSuch u n = some gf) :
    ∃ c : Fin u.fns.length, fnAt u c = gf ∧ gf.name = n := by
  have hm := List.mem_of_find?_eq_some h
  have hn := List.find?_some h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  exact ⟨⟨i, hi⟩, rfl, by simpa using hn⟩

end Gabbro.Bruecke
