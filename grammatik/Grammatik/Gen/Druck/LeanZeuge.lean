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
    let e ← LeanTerm.expr tab glob fn feld (P.requires f)
    let j := fn f
    pure (s!"def fv : z.deklaration.Fn := (⟨{j}, by decide⟩ : Fin z.fns.length)\n\n" ++ s!"def vr : Expr z.deklaration (z.deklaration.params fv)\n    (Signatur.anfang z.deklaration (z.deklaration.signatur fv)) .bool :=\n  {e}\n\n" ++
      s!"def P : Programm z.deklaration :=\n  \{ h0.programm with requires := fun g => if hg : g = fv then hg ▸ vr else Expr.tru }\n\n" ++
      "theorem vr_klein : @groesseExpr z.deklaration z.zahlen _ _ _ vr ≤ ncZiel := by decide\n\n" ++
      "theorem vr_endlich : @groesseExpr z.deklaration z.zahlen _ _ _ vr < unendlich := by decide\n\n",
      s!"(vertragsL_req z ncZiel h0 fv vr vr_klein vr_endlich)")
  | none, some f => do
    let e ← LeanTerm.expr tab glob fn feld (P.ensures f)
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
    let b ← LeanTerm.endblock tab glob fn lock ax feld reg (P.rumpf f)
    pure s!"def b{fn f} : Rumpf z.deklaration ⟨{fn f}, by decide⟩ :=\n  {b}\n\n"
  let klauseln := z.fnListe.map fun f => s!"  | ⟨{fn f}, _⟩ => b{fn f}\n"
  pure (String.join defs ++ "def r : (f : z.deklaration.Fn) → Rumpf z.deklaration f\n" ++ String.join klauseln ++
    s!"  | ⟨n + {n}, h⟩ => absurd h (by have : z.fns.length = {n} := (by decide); omega)\n")

/-- **The witness file** of a program: member `i`, starts `ws`. For a valid program the theorem is `RaumGut` of the
    good cells `zellen`; for a refused one (`abgelehnt`, `zellen` all its cells) it is `RaumSchlecht` of `bnoetig`, the
    cells of the program that are not good cells M witnesses (`erreicht`): a program that has these has the test. -/
def Spez.leanZeuge (z : Spez) (i _nc : Nat) (stamm : String) (P : Programm z.deklaration)
    (ws : List z.deklaration.Fn) (zellen : List Zelle) (abgelehnt : Bool) : Except String String := do
  let r ← z.leanRuempfe P
  let (vdefs, hP) ← z.leanVertrag P
  let fn := fun (f : z.deklaration.Fn) => (show Fin z.fns.length from f).val
  let flags := z.fnListe.map fun f => toString (P.unterbricht f)
  let wsT := String.intercalate ", " (ws.map fun w => s!"(⟨{fn w}, by decide⟩ : Fin z.fns.length)")
  let zs := String.intercalate ", " (zellen.map Zelle.lean)
  let kopf := s!"/-\n  File:      Grammatik/Gen/Zeugen/{stamm}.lean\n  Subject:   GENERATED witness (`gen-zelle`, `LeanZeuge.lean`): member {i}, the cells below lie in the generator's\n             space. Checked by the kernel; do not edit.\n-/\nimport Grammatik.Gen.Abdeckung.Satz.Raum\nimport Grammatik.Gen.Erzeuger.Entscheidung\nimport Grammatik.Korpus.Zeugnis.Zeugnis.T1\n" ++ (if abgelehnt then "import Grammatik.Gen.Zeugen.Erreicht\n" else "") ++ s!"\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\n\nnamespace Gabbro.Grammatik.Gen.Zeugen.{stamm}\n\nopen Gabbro.Grammatik Gabbro.Grammatik.Gen\n\nabbrev z : Spez := mitglieder.getD {i} " ++ "{}" ++ s!"\n\n{r}\ndef h0 : Haut z.deklaration := ⟨r, fun f => [{String.intercalate ", " flags}].getD f.val false⟩\n\ndef ws : List z.deklaration.Fn := [{wsT}]\n\n" ++ vdefs
  let allF := fun (was : String) => s!"(fun f => (by decide : ∀ f : Fin z.fns.length, {was}) f)"
  let gr := "@groesseEnd z.deklaration z.zahlen _ _ _ _ (h0.rumpf f)"
  -- hn hnb hk hP hws hax hb: the bounds, the table bound, the size, the contract variant, the starts, no foreign body, the floors
  let seite := s!"{allF (gr ++ " ≤ (grenzenVon " ++ toString i ++ ").1")} (by decide)\n    (by decide) {hP} (ws := ws) (by decide) (by decide) (by decide)"
  let mitglied := s!"⟨{i}, by rw [mitglieder_laenge]; decide,"
  let satz := if !abgelehnt then
      s!"theorem zellen : ∀ x ∈ ([{zs}] : List Zelle), RaumGut ncZiel x := by\n  intro x hx\n  refine {mitglied} raumGutIn_aus z (grenzenVon {i}).1 (grenzenVon {i}).2 ncZiel h0\n    {seite} (by decide) ?_⟩\n  revert x; decide\n"
    else
      s!"def alle : List Zelle := [{zs}]\n\ndef bnoetig : List Zelle := alle.filter fun w => w.schlecht || !erreicht.contains w\n\n" ++
      s!"theorem zellen : RaumSchlecht ncZiel erreicht bnoetig :=\n  {mitglied} raumSchlechtIn_aus z (grenzenVon {i}).1 (grenzenVon {i}).2 ncZiel h0\n    {seite} (by decide) (by decide)⟩\n"
  pure (kopf ++ satz ++ s!"\nend Gabbro.Grammatik.Gen.Zeugen.{stamm}\n")

end Gabbro.Grammatik.Gen
