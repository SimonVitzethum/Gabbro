/-
  File:      stage0/Stage0/Lauf/Memo.lean
  Subject:   **The program computed once.** The pipeline's program computes a function's body (and its contract) by
             lowering it again at every use; `memoP` tabulates them once and looks them up. `memoP_eq`: it is the
             same program.
-/
import Stage0.Laufzeit

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- The table of a dependent function over the functions of a unit. -/
def tabelleFn (u : UProg) {β : Fin u.fns.length → Type} (g : ∀ f, β f) : Array (Σ f : Fin u.fns.length, β f) :=
  Array.ofFn fun f => ⟨f, g f⟩

/-- A look-up in such a table, with the function's own value as the fallback. -/
def ausTabelle (u : UProg) {β : Fin u.fns.length → Type} (g : ∀ f, β f) (t : Array (Σ f : Fin u.fns.length, β f))
    (f : Fin u.fns.length) : β f :=
  match t[f.val]? with
  | some ⟨f', b⟩ => if h : f' = f then h ▸ b else g f
  | none => g f

theorem ausTabelle_eq (u : UProg) {β : Fin u.fns.length → Type} (g : ∀ f, β f) :
    ausTabelle u g (tabelleFn u g) = g := by
  funext f
  simp only [ausTabelle, tabelleFn]
  rw [Array.getElem?_ofFn]
  simp only [f.isLt, ↓reduceDIte, Fin.eta]

/-- **The program with its bodies and contracts computed once** (the tables are built when `memoP` is evaluated,
    outside the functions that read them). -/
def memoP (u : UProg) (P : Programm (declOf u)) : Programm (declOf u) :=
  let tR := tabelleFn u (β := fun f => Endblock (declOf u) (vertragVon (declOf u) f) false ((declOf u).params f)
    (Signatur.anfang (declOf u) ((declOf u).signatur f))) P.rumpf
  let tQ := tabelleFn u (β := fun f => Expr (declOf u) ((declOf u).params f)
    (Signatur.anfang (declOf u) ((declOf u).signatur f)) .bool) P.requires
  let tE := tabelleFn u (β := fun f => Expr (declOf u) (ErgCtx ((declOf u).params f) ((declOf u).erg f))
    (vertragVon (declOf u) f).ende .bool) P.ensures
  { P with
    rumpf := fun f => ausTabelle u P.rumpf tR f
    requires := fun f => ausTabelle u P.requires tQ f
    ensures := fun f => ausTabelle u P.ensures tE f }

theorem memoP_eq (u : UProg) (P : Programm (declOf u)) : memoP u P = P := by
  cases P
  simp only [memoP]
  congr 1
  · exact ausTabelle_eq u _
  · exact ausTabelle_eq u _
  · exact ausTabelle_eq u _

end Gabbro.Stage0
