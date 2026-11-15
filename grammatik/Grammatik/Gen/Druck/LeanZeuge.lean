/-
  Emit concrete checker verdicts and cell occurrences for generated witnesses. No full-verdict preservation by structural body summaries is assumed.
-/
module
public import Grammatik.Gen.Druck.LeanTerm
public import Grammatik.Gen.Abdeckung.Waehlen
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

/-- A cell as a Lean literal. -/
def Zelle.lean (x : Zelle) : String :=
  s!"⟨{x.komp}, {x.art}, {x.urteil}, [{String.intercalate ", " (x.atome.map toString)}]⟩"

/-- The numbers of the elements of a member's finite types. -/
def Spez.nummern (z : Spez) : LeanTerm.Namen z.deklaration where
  tab t := (show Fin z.tabs.length from t).val
  glob g := (show Fin z.globs.length from g).val
  fn f := (show Fin z.fns.length from f).val
  lock L := (show Fin z.locks.length from L).val
  ax a := (show Fin z.axs.length from a).val
  feld _ f := (show Fin _ from f).val
  reg r := (show Fin z.regs.length from r).val
  marke m := (show Fin z.marken.length from m).val
  inv i := (show Fin z.invs.length from i).val
  annahme a := (show Fin (z.annahmen + 1) from a).val

/-- The contract `true` everywhere: only such programs are printed (a contract variant has no clause yet). -/
def Spez.ohneVertrag (z : Spez) (P : Programm z.deklaration) : Bool :=
  z.fnListe.all fun f => istWahrL (P.requires f) && istWahrL (P.ensures f)
where
  istWahrL {Γ : Ctx} {Λ : List (Res z.deklaration)} {τ : Ty} : Expr z.deklaration Γ Λ τ → Bool
    | .tru => true
    | _ => false

/-- The contract variant of a program as Lean source: the definitions and the proof that the program is one of the
    variants of its skeleton (`vertragsL_req`/`vertragsL_ens`; the head of the list without a contract). -/
def Spez.leanVertrag (z : Spez) (P : Programm z.deklaration) : Except String (String × String) := do
  let tab := fun (t : z.deklaration.Tab) => (show Fin z.tabs.length from t).val
  let glob := fun (g : z.deklaration.Glob) => (show Fin z.globs.length from g).val
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let feld := fun (t : z.deklaration.Tab) (f : z.deklaration.Feld t) => (show Fin _ from f).val
  let wahr := @Spez.ohneVertrag.istWahrL z
  match z.fnListe.find? (fun f => !wahr (P.requires f)), z.fnListe.find? (fun f => !wahr (P.ensures f)) with
  | none, none => pure ("def P : Programm z.deklaration := h0.programm\n\n", "List.mem_cons_self")
  | some f, none => do
    let e ← LeanTerm.expr z.nummern (P.requires f)
    let j := fn f
    pure (s!"def fv : z.deklaration.Fn := (⟨{j}, by decide⟩ : Fin z.fns.length)\n\n" ++ s!"def vr : Expr z.deklaration (z.deklaration.params fv)\n    (Signatur.anfang z.deklaration (z.deklaration.signatur fv)) .bool :=\n  {e}\n\n" ++
      s!"def P : Programm z.deklaration :=\n  \{ h0.programm with requires := fun g => if hg : g = fv then hg ▸ vr else Expr.tru }\n\n" ++
      "theorem vr_klein : @groesseExpr z.deklaration z.zahlen _ _ _ vr ≤ ncZiel := by decide\n\n" ++
      "theorem vr_endlich : @groesseExpr z.deklaration z.zahlen _ _ _ vr < unendlich := by decide\n\n",
      s!"(vertragsL_req z ncZiel h0 fv vr vr_klein vr_endlich)")
  | none, some f => do
    let e ← LeanTerm.expr z.nummern (P.ensures f)
    let j := fn f
    pure (s!"def fv : z.deklaration.Fn := (⟨{j}, by decide⟩ : Fin z.fns.length)\n\n" ++ s!"def ve : Expr z.deklaration (ErgCtx (z.deklaration.params fv) (z.deklaration.erg fv))\n    (vertragVon z.deklaration fv).ende .bool :=\n  {e}\n\n" ++
      s!"def P : Programm z.deklaration :=\n  \{ h0.programm with ensures := fun g => if hg : g = fv then hg ▸ ve else Expr.tru }\n\n" ++
      "theorem ve_klein : @groesseExpr z.deklaration z.zahlen _ _ _ ve ≤ ncZiel := by decide\n\n" ++
      "theorem ve_endlich : @groesseExpr z.deklaration z.zahlen _ _ _ ve < unendlich := by decide\n\n",
      s!"(vertragsL_ens z ncZiel h0 fv ve ve_klein ve_endlich)")
  | some _, some _ => throw "Lean print: two contracts (the generator varies one)"

/-- The bodies of a program as Lean source: one clause per function. -/
def Spez.leanRuempfe (z : Spez) (P : Programm z.deklaration) : Except String String := do
  let n := z.fns.length
  let tab := fun (t : z.deklaration.Tab) => (show Fin z.tabs.length from t).val
  let glob := fun (g : z.deklaration.Glob) => (show Fin z.globs.length from g).val
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let lock := fun (L : z.deklaration.Lock) => (show Fin z.locks.length from L).val
  let ax := fun (a : z.deklaration.Ax) => (show Fin z.axs.length from a).val
  let feld := fun (t : z.deklaration.Tab) (f : z.deklaration.Feld t) => (show Fin _ from f).val
  let reg := fun (r : z.deklaration.Reg) => (show Fin z.regs.length from r).val
  let defs ← z.fnListe.mapM fun f => do
    let b ← LeanTerm.endblock z.nummern (P.rumpf f)
    pure s!"def b{fn f} : Rumpf z.deklaration ⟨{fn f}, by decide⟩ :=\n  {b}\n\n"
  let klauseln := z.fnListe.map fun f => s!"  | ⟨{fn f}, _⟩ => b{fn f}\n"
  pure (String.join defs ++ "def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f\n" ++ String.join klauseln ++
    s!"  | ⟨n + {n}, h⟩ => absurd h (by have : z.fns.length = {n} := (by decide); omega)\n")

/-- Emit the concrete verdict and cell occurrences of a witness. Refused
    witnesses also expose their needed cells for the explicit witness table. -/
def Spez.leanZeuge (z : Spez) (i _nc : Nat) (stamm : String) (P : Programm z.deklaration)
    (ws : List z.deklaration.Fn) (zellen : List Zelle) (abgelehnt : Bool) : Except String String := do
  let r ← z.leanRuempfe P
  let (vdefs, _) ← z.leanVertrag P
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let flags := z.fnListe.map fun f => toString (P.unterbricht f)
  let wsT := String.intercalate ", " (ws.map fun w => s!"(⟨{fn w}, by decide⟩ : Fin z.fns.length)")
  let zs := String.intercalate ", " (zellen.map Zelle.lean)
  let namensraum := stamm.replace "/" "."
  let kopf := s!"/-\n  File:      Grammatik/Gen/Zeugen/{stamm}.lean\n  Subject:   GENERATED witness (`gen-zelle`, `LeanZeuge.lean`): member {i}, concrete checker verdict and cell occurrences. Do not edit.\n-/\nmodule\npublic import Grammatik.Gen.Abdeckung.Satz.Raum\npublic import Grammatik.Gen.Erzeuger.Entscheidung\npublic import Grammatik.Korpus.Zeugnis.Zeugnis.T1\n" ++ (if abgelehnt then "public import Grammatik.Gen.Zeugen.Erreicht\n" else "") ++ s!"\n@[expose] public section\n\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n\nnamespace Gabbro.Grammatik.Gen.Zeugen.{namensraum}\n\nopen Gabbro.Grammatik Gabbro.Grammatik.Gen\n\nabbrev z : Spez := mitglieder.getD {i} " ++ "{}" ++ s!"\n\n{r}\ndef h0 : Haut z.deklaration := ⟨r, fun f => [{String.intercalate ", " flags}].getD f.val false⟩\n\ndef ws : List z.deklaration.Fn := [{wsT}]\n\n" ++ vdefs
  let einsatz := "/-- The test as a program of the source. -/\ndef e : Einsatz := z.einsatz P ws (by decide) (by decide)\n\n" ++
    s!"theorem e_gueltig : e.gueltig = {!abgelehnt} := by decide\n\n"
  let satz := if !abgelehnt then
      einsatz ++ s!"theorem e_hat : ∀ x ∈ ([{zs}] : List Zelle), e.Hat x := by decide\n"
    else
      s!"def alle : List Zelle := [{zs}]\n\ndef bnoetig : List Zelle := alle.filter fun w => w.schlecht || !erreicht.contains w\n\n" ++
      einsatz ++ "theorem e_gedeckt : gedeckt erreicht bnoetig e.zellen = true := by decide\n"
  pure (kopf ++ satz ++ s!"\nend Gabbro.Grammatik.Gen.Zeugen.{namensraum}\n")

end Gabbro.Grammatik.Gen
