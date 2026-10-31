/- Gate decoding witnesses, with inhabited boolean and never call sites. -/
import Stage0.Senke.Welt.Anordnung
import Stage0.Senke.Anweisung.TorLauf
import Grammatik.Parser.Elab.UebersetzeAllg3

namespace Gabbro.Stage0.Senke.GateProbe

open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR

set_option maxRecDepth 100000

def u : UProg := {
  tabs := [], locks := []
  axs := [{ name := "truth", params := [], kinds := [], res := some .bool },
    { name := "finish", params := [], kinds := [], res := some .never }]
  fns := [{ name := "main", params := [], kinds := [], res := some (0, 100), held := [], puts := [], gives := [], body := [], ret := .val (.lit 0) }]
}
abbrev D := declOf u
abbrev main : D.Fn := ⟨0, by decide⟩
abbrev truth : D.Ax := ⟨0, by decide⟩
abbrev finish : D.Ax := ⟨1, by decide⟩

def retN {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Endblock D (vertragVon D main) false Γ [] :=
  .ret (.val (.widen hl hh (.lit n))) (.refl [])

def boolBody : Endblock D (vertragVon D main) false [] [] :=
  .bindAxiom truth .nil rfl (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (.ite (.var .here) (retN 17 (by decide) (by decide)) (retN 19 (by decide) (by decide)))

def boolBlock : Block D (vertragVon D main) false [] [] [] :=
  .bindAxiom truth .nil rfl (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (.cons (.ite (.var .here) .nil .nil) .nil)

def neverBody : Endblock D (vertragVon D main) false [] [] :=
  .bindAxiom finish .nil rfl (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) (retN 99 (by decide) (by decide))

def neverBlock : Block D (vertragVon D main) false [] [] [] :=
  .bindAxiom finish .nil rfl (fun t => Fin.elim0 t) (fun g => Fin.elim0 g)
    (fun t => Fin.elim0 t) (fun g => Fin.elim0 g) .nil

def programOf (body : Endblock D (vertragVon D main) false [] []) : Programm D where
  invariante _ := .tru
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    obtain ⟨f, hf⟩ := f
    have hz : f = 0 := by change f < 1 at hf; omega
    subst f
    exact body

def binding (a : D.Ax) : Option TorB :=
  some ⟨if a.val = 0 then 39 else 231, regsIn 0, []⟩

def imageOf (body : Endblock D (vertragVon D main) false [] []) : Except String (List Runner.B) := do
  let b ← bild 1 (programOf body) (layU u binding) [main] Fin.val (fun _ => "main") main [] 1024
  pure b.bytes

theorem boolean_images_zeuge : (imageOf boolBody).isOk = true ∧
    (imageOf (.cons (.ite .tru boolBlock .nil) (retN 99 (by decide) (by decide)))).isOk = true := by
  decide +kernel

theorem never_images_zeuge : (imageOf neverBody).isOk = true ∧
    (imageOf (.cons (.ite .tru neverBlock .nil) (retN 99 (by decide) (by decide)))).isOk = true := by
  decide +kernel

/-- The never continuation is discarded by G for every oracle. -/
theorem never_outcome_zeuge (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) :
    execBlock O passes R neverBlock σ .nil = .hardware (.annahme finish) := by
  rfl

/-- The raw word and its signed interpretation agree on whether the boolean is false. -/
theorem boolean_decode_zeuge :
    einpassenErg (D := D) (fun _ => none) (some .bool) 0 = some false ∧
    einpassenErg (D := D) (fun _ => none) (some .bool) 7 = some true ∧
    einpassenErg (D := D) (fun _ => none) (some .bool) (-38) = some true := by exact ⟨rfl, rfl, rfl⟩

/-- The front end admits start, exports its worker, and the complete IR image lowers. -/
def startSource : String :=
  "module ir_probe { impl fn worker() effects { pure } { } impl fn main() -> u64 in 0 .. 100 effects { pure } { start { worker }; return 23; } }"

def startUnit : Except String UProg := do
  let ts ← (lex startSource).mapError fun _ => "lex"
  let items ← parseTopTief ts
  elabU (pre108 items)

def startNames : Except String (List String) := do
  pure (← startUnit).gestartet

theorem start_frontend_zeuge : startNames.toOption = some ["worker"] := by decide +kernel

def startRoots : Except String (List Nat) := do
  let p ← startUnit
  let entry ← fnIdx p.fns "main"
  let (P, _) ← lowerAllg p
  let rs ← (uOhneDoppelte (p.roots ++ p.gestartet)).mapM (fnIdx p.fns)
  let b ← bild 1 P (layU p (fun _ => none)) (List.finRange p.fns.length) Fin.val
    (fun _ => "probe") entry (rs.filter (fun f => f.val != entry.val)) 1024
  pure (b.roots.map Fin.val)

theorem start_image_zeuge : startRoots.toOption = some [0] := by decide +kernel

/-- Other result types still require their own checked representation and decoder. -/
theorem unsupported_answers_zeuge :
    chkC (some (.ref 0)) 3 = none ∧ chkC (some (.opt 4)) 3 = none ∧
    chkC (some (.fnptr 0)) 3 = none := by decide +kernel

end Gabbro.Stage0.Senke.GateProbe
