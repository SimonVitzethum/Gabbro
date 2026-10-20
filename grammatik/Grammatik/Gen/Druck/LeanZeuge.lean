/-
  File:      Grammatik/Gen/Druck/LeanZeuge.lean
  Subject:   A WITNESS FILE for the cells of one program the generator emitted: the program as a Lean term
             (`LeanTerm.lean`) and the theorem that its cells lie in the generator's space (`RaumGut` for a valid
             program, `RaumSchlecht` for its one bad cell), proved by `raumGutIn_aus`/`raumSchlechtIn_aus` with every
             concrete side condition decided by the kernel. The file is untrusted text; the kernel checks it.
-/
import Grammatik.Gen.Druck.LeanTerm
import Grammatik.Gen.Abdeckung.Waehlen

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

/-- A cell as a Lean literal. -/
def Zelle.lean (x : Zelle) : String :=
  s!"⟨{x.komp}, {x.art}, {x.urteil}, [{String.intercalate ", " (x.atome.map toString)}]⟩"

/-- The contract `true` everywhere: only such programs are printed (a contract variant has no clause yet). -/
def Spez.ohneVertrag (z : Spez) (P : Programm z.deklaration) : Bool :=
  z.fnListe.all fun f => istWahrL (P.requires f) && istWahrL (P.ensures f)
where
  istWahrL {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} : Expr z.deklaration Γ Λ τ → Bool
    | .tru => true
    | _ => false

/-- The bodies of a program as Lean source: one clause per function. -/
def Spez.leanRuempfe (z : Spez) (P : Programm z.deklaration) : Except String String := do
  let n := z.fns.length
  let tab := fun (t : z.deklaration.Tab) => (show Fin z.tabs.length from t).val
  let glob := fun (g : z.deklaration.Glob) => (show Fin z.globs.length from g).val
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let lock := fun (L : z.deklaration.Lock) => (show Fin z.locks.length from L).val
  let ax := fun (a : z.deklaration.Ax) => (show Fin z.axs.length from a).val
  let feld := fun (t : z.deklaration.Tab) (f : z.deklaration.Feld t) => (show Fin _ from f).val
  let defs ← z.fnListe.mapM fun f => do
    let b ← LeanTerm.endblock tab glob fn lock ax feld (P.rumpf f)
    pure s!"def b{fn f} : Rumpf z.deklaration ⟨{fn f}, by decide⟩ :=\n  {b}\n\n"
  let klauseln := z.fnListe.map fun f => s!"  | ⟨{fn f}, _⟩ => b{fn f}\n"
  pure (String.join defs ++ "def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f\n" ++ String.join klauseln ++
    s!"  | ⟨n + {n}, h⟩ => absurd h (by have : z.fns.length = {n} := (by decide); omega)\n")

/-- **The witness file** of a program: member `i`, starts `ws`, the cells it witnesses. For a valid
    program (`c0 = none`) the theorem is `RaumGut`; for a single-fault program refused by `c0` it is `RaumSchlecht` of
    its one bad cell. -/
def Spez.leanZeuge (z : Spez) (i nc : Nat) (stamm : String) (P : Programm z.deklaration)
    (ws : List z.deklaration.Fn) (zellen : List Zelle) (c0 : Option (Fin 10)) : Except String String := do
  if !z.ohneVertrag P then throw "Lean print: contract variant"
  let r ← z.leanRuempfe P
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let flags := z.fnListe.map fun f => toString (P.unterbricht f)
  let wsT := String.intercalate ", " (ws.map fun w => s!"(⟨{fn w}, by decide⟩ : Fin z.fns.length)")
  let zs := String.intercalate ", " (zellen.map Zelle.lean)
  let kopf := s!"/-\n  File:      Grammatik/Gen/Zeugen/{stamm}.lean\n  Subject:   GENERATED witness (`gen-zelle`, `LeanZeuge.lean`): member {i}, the cells below lie in the generator's\n             space. Checked by the kernel; do not edit.\n-/\nimport Grammatik.Gen.Abdeckung.Satz.Raum\nimport Grammatik.Gen.Erzeuger.Entscheidung\nimport Grammatik.Korpus.Zeugnis.Zeugnis.T1\n" ++ (if c0.isSome then "import Grammatik.Gen.Zeugen.Erreicht\n" else "") ++ s!"\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n\nnamespace Gabbro.Grammatik.Gen.Zeugen.{stamm}\n\nopen Gabbro.Grammatik Gabbro.Grammatik.Gen\n\nabbrev z : Spez := mitglieder.getD {i} " ++ "{}" ++ s!"\n\n{r}\ndef h0 : Haut z.deklaration := ⟨r, fun f => [{String.intercalate ", " flags}].getD f.val false⟩\n\ndef ws : List z.deklaration.Fn := [{wsT}]\n\n"
  let allF := fun (was : String) => s!"(fun f => (by decide : ∀ f : Fin z.fns.length, {was}) f)"
  let gr := "@groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f)"
  -- hn hu hk hP hws hb: the bounds, the size, the contract variant (none), the starts, the floors
  let seite := s!"{allF (gr ++ " ≤ (grenzenVon " ++ toString i ++ ").1")} {allF (gr ++ " < unendlich")}\n    (by decide) List.mem_cons_self (ws := ws) (by decide) (by decide)"
  let mitglied := s!"⟨{i}, by rw [mitglieder_laenge]; decide,"
  let satz := match c0 with
    | none => s!"theorem zellen : ∀ x ∈ ([{zs}] : List Zelle), RaumGut {nc} x := by\n  intro x hx\n  refine {mitglied} raumGutIn_aus z (grenzenVon {i}).1 (grenzenVon {i}).2 {nc} h0\n    {seite} (by decide) ?_⟩\n  revert x; decide\n"
    | some c => s!"theorem zellen : ∀ x ∈ ([{zs}] : List Zelle), RaumSchlecht {nc} erreicht x := by\n  intro x hx\n  simp only [List.mem_singleton] at hx\n  subst hx\n  exact {mitglied} raumSchlechtIn_aus z (grenzenVon {i}).1 (grenzenVon {i}).2 {nc} h0\n    {seite} {c.val} (by decide) (by decide) (by decide)⟩\n"
  pure (kopf ++ satz ++ s!"\nend Gabbro.Grammatik.Gen.Zeugen.{stamm}\n")

end Gabbro.Grammatik.Gen
