/-
  File:      Grammatik/Gen/Fein/Druck.lean
  Subject:   A FINE WITNESS FILE: one valid program of a member as a Lean term, the proof that the Lean model accepts it
             (`e_gueltig`) and that it has the fine cells listed (`e_hatF`), both decided by the kernel. The text is
             untrusted; the kernel checks it.
-/
import Grammatik.Gen.Druck.LeanZeuge
import Grammatik.Gen.Fein.Zellen

namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen

/-- A fine cell as a Lean literal. -/
def FZelle.lean (c : FZelle) : String :=
  s!"⟨{c.art}, {c.fam}, {c.kon}, {c.l}, [{String.intercalate ", " (c.daten.map toString)}]⟩"

/-- **The fine witness file** of a program of member `i` under the starts `ws`, with the cells `zs`. -/
def leanFein (z : Spez) (quelle : String) (i : Nat) (stamm : String) (P : Programm z.deklaration) (ws : List z.deklaration.Fn)
    (zs : List FZelle) : Except String String := do
  let r ← z.leanRuempfe P
  let (vdefs, _) ← z.leanVertrag P
  let vdefs := String.intercalate "\n\n" ((vdefs.splitOn "\n\n").filter fun b => !b.startsWith "theorem")
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let flags := z.fnListe.map fun f => toString (P.unterbricht f)
  let wsT := String.intercalate ", " (ws.map fun w => s!"(⟨{fn w}, by decide⟩ : Fin z.fns.length)")
  let zsT := String.intercalate ",\n  " (zs.map FZelle.lean)
  pure (s!"/-\n  File:      Grammatik/Gen/Zeugen/F/{stamm}.lean\n  Subject:   GENERATED fine witness (`Gen/Fein/Druck.lean`): member {i}, a valid program with the fine cells\n             below. Checked by the kernel; do not edit.\n-/\nimport Grammatik.Gen.Abdeckung.Satz.ErzeugtMN\nimport Grammatik.Gen.Erzeuger.Entscheidung\nimport Grammatik.Korpus.Zeugnis.Zeugnis.T1\nimport Grammatik.Gen.Fein.Mitglieder\n\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n\nnamespace Gabbro.Grammatik.Gen.Zeugen.F.{stamm}\n\nopen Gabbro.Grammatik Gabbro.Grammatik.Gen\n\nabbrev z : Spez := {quelle}.getD {i} " ++ "{}" ++
    s!"\n\n{r}\ndef h0 : Haut z.deklaration := ⟨r, fun f => [{String.intercalate ", " flags}].getD f.val false⟩\n\ndef ws : List z.deklaration.Fn := [{wsT}]\n\n" ++ vdefs ++
    (if vdefs.endsWith "\n" then "" else "\n\n") ++
    "/-- The witness as a program of the source. -/\ndef e : Einsatz := z.einsatz P ws (by decide) (by decide)\n\n" ++
    "theorem e_gueltig : e.gueltig = true := by decide +kernel\n\n" ++
    s!"/-- Its fine cells. -/\ndef zs : List Fein.FZelle := [\n  {zsT}]\n\n" ++
    "theorem e_hatF : ∀ c ∈ zs, e.HatF c := by decide +kernel\n\n" ++
    s!"end Gabbro.Grammatik.Gen.Zeugen.F.{stamm}\n")

end Gabbro.Grammatik.Gen.Fein
