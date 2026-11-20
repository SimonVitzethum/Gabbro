module
public import Grammatik.Berechenbarkeit.BrainfuckG.Programm
public import Grammatik.Berechenbarkeit.BrainfuckG.Schritt
public import Grammatik.Berechenbarkeit.Storage.GStack.Multi
public import Grammatik.Bausteine.Arena.Struktur.ArenaBaumWelt
public import Grammatik.Zielsatz.Kern.Akzeptiert
import all Batteries.Data.Except
@[expose] public section


/-! The G program of the Brainfuck program `.` as a whole G function -- bind the counter and the head, run the loop,
return -- and the core checker's verdict on it: accepted, in the conditional class. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert

open Brainfuck ArenaKette InvDynZeuge Storage.GStack SchrittWitnesses ProgrammWitnesses Terminierung

/-- `let pc = 0; let h = 0; programm; return`. -/
def body : Endblock BD BV false [] [] :=
  .bind (Expr.widen (by decide) (by decide) (.lit 0) : Expr BD [] [] (Ty.int 0 1))
    (.bind (nullByte : Expr BD [Ty.int 0 1] [] ByteTy)
      (.cons (programm BL BG hp rechte failure punkt ()) (.ret .empty (List.Perm.refl []))))

def prog : Programm BD where
  invariante := fun i => i.elim
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => body

/-- The same storage body with a false postcondition must enter the strict
    VC path; the Basic totality certificate cannot accept this contract. -/
def falseContract : Programm BD := { prog with ensures := fun _ => .fls }

theorem false_contract_refused_zeuge :
    Invarianten.Pruefer.invariantVCB falseContract (SperrInv.leer BD) [()] = false := by
  decide +kernel


end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert
