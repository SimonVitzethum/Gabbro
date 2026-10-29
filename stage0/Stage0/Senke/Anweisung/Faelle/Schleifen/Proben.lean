/- Runtime images for overflow blocks the source reader cannot construct, and forever fuel witnesses. -/
import Stage0.Senke.Anweisung.Faelle.Kontrolle.ControlProbes
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter
import Stage0.Senke.Anweisung.Faelle.Schleifen.Retry

namespace Gabbro.Stage0.Senke.LoopProbe
open Gabbro.Grammatik Runner.IR
open ControlProbe
set_option maxRecDepth 100000

/-- A return statement usable inside a loop body or overflow block. -/
def returned {l : Bool} {Γ : Ctx} (n : Int) (hl : 0 ≤ n) (hh : n ≤ 100) :
    Block D (vertragVon D entry) l Γ [] [] :=
  .cons (.ret (.val (.widen hl hh (.lit n))) (.refl [])) .nil

/-- The inner overflow's exit belongs to the outer loop. Reaching 41 would expose a wrong target. -/
def overflowExit (next : Bool) : Block D (vertragVon D entry) false [] [] [] :=
  .cons (.retry 1 .fls
    (.cons (.retry 0 .fls .nil (.cons (if next then .next rfl else .leave rfl) .nil))
      (returned 41 (by decide) (by decide))) .nil)
    (returned 7 (by decide) (by decide))

def overflowReturn : Block D (vertragVon D entry) false [] [] [] :=
  .cons (.retry 0 .fls .nil (returned 43 (by decide) (by decide))) .nil

def zeroTrue : Block D (vertragVon D entry) false [] [] [] :=
  .cons (.retry 0 .tru (returned 41 (by decide) (by decide))
    (returned 43 (by decide) (by decide))) .nil

def images : List (String × Except String (List Runner.B) × Nat) :=
  [("retry-overflow-leave", blockImageOf (overflowExit false), 7),
   ("retry-overflow-next", blockImageOf (overflowExit true), 7),
   ("retry-overflow-return", blockImageOf overflowReturn, 43),
   ("retry-zero-true", blockImageOf zeroTrue, 99)]

/-- All overflow-exit fixtures lower as complete images with nonempty loop control. -/
theorem retry_overflow_zeuge : images.all (fun x => x.2.1.isOk) = true := by
  decide +kernel

/-- A named progress assumption, one function and a concrete world. -/
def uf : Parser.Uebersetze.UProg := { ControlProbe.u with annahmen := ["tick"] }
abbrev DF := Parser.UebersetzeAllg.declOf uf
abbrev progress : DF.Annahme := some ⟨0, by decide⟩
abbrev main : DF.Fn := ⟨0, by decide⟩

def initialF : World DF where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g
  spur := []

def oracleF : Orakel DF where
  wirkt _ σ _ := (σ, 0)
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar _ _ := true

def callsF (f : DF.Fn) (_ : World DF) (_ : Env DF (DF.params f)) : RufAusgang f := .logik .schleife

/-- The same false-invariant loop has different observable exits at zero and positive fuel. -/
theorem forever_fuel_zeuge :
    execStmt oracleF 0 callsF (Stmt.forever (V := vertragVon DF main) (l := false) (Λ := []) progress .fls .nil)
      initialF (Env.nil : Env DF []) = .hardware (.fortschritt progress) ∧
    execStmt oracleF 1 callsF (Stmt.forever (V := vertragVon DF main) (l := false) (Λ := []) progress .fls .nil)
      initialF (Env.nil : Env DF []) = .logik .schleife ∧
    hwCode (D := DF) (.fortschritt progress) = 111 ∧ logikCode (D := DF) .schleife = 104 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Fallthrough and next exhaust the fuel; leave succeeds without a further invariant check. -/
theorem forever_body_zeuge :
    execStmt oracleF 2 callsF (Stmt.forever (V := vertragVon DF main) (l := false) (Λ := []) progress .tru .nil)
      initialF (Env.nil : Env DF []) = .hardware (.fortschritt progress) ∧
    execStmt oracleF 2 callsF (Stmt.forever (V := vertragVon DF main) (l := false) (Λ := []) progress .tru (.cons (.next rfl) .nil))
      initialF (Env.nil : Env DF []) = .hardware (.fortschritt progress) ∧
    (match execStmt oracleF 1 callsF (Stmt.forever (V := vertragVon DF main) (l := false) (Λ := []) progress .tru (.cons (.leave rfl) .nil))
      initialF (Env.nil : Env DF []) with | .ok _ _ => true | _ => false) = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Even an immediately leaving forever must be refused: fuel zero never enters its body. -/
theorem forever_refused_zeuge :
    lowS 1 (fun _ => 0) (layU uf (fun _ => none) 0) 3 ([], 0) [] (0, 0)
      (Stmt.forever (V := vertragVon DF main) (l := false) (Λ := []) progress .tru (.cons (.leave rfl) .nil) :
        Stmt DF (vertragVon DF main) false [] [] []) = none := rfl

end Gabbro.Stage0.Senke.LoopProbe
