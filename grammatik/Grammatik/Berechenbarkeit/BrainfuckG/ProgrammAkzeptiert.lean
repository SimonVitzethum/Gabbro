import Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses
import Grammatik.Zielsatz.Kern.Akzeptiert

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

/-- The structural classifier: a conditional loop (`bedingt`); `programm_korrekt` and `programm_vollstaendig`
say when it completes. -/
theorem prog_klasse_zeuge : klasse prog [()] (fun _ => false) () = .bedingt := by decide

/-- **The core checker accepts the program.** -/
theorem prog_accepted_zeuge :
    Akzeptiert prog ⟨fun L => L.elim, fun L => L.elim⟩ [()] []
      [.inl (), .inr 0, .inr 1, .inr 2, .inr 3, .inr 4, .inr 5, .inr 6] [()] = true := by decide +kernel


/-- **The accepted function runs**: with budget 2 it returns normally, and its run is the halting Brainfuck run of `.`
with the output on the output stack. -/
theorem prog_exec_zeuge (O : Orakel BD) (R : ∀ f : BD.Fn, World BD → Env BD (BD.params f) → RufAusgang f) :
    ∃ σ', execEnd O 2 R body w0 .nil = .zurueck σ' () ∧
      ∃ out, HaltsWith punkt [] out ∧ ∃ vals, MultiRep BL BG σ' vals ∧ vals 3 = out.reverse.map (ablage hp) := by
  obtain ⟨σ', ρ', h⟩ := programm_ok_zeuge O R
  obtain ⟨out, hh, vals, hm, hv⟩ := programm_haelt O 2 R BL BG BG_inj hp rechte failure bricht punkt .nil () []
    w0 σ' ρi ρ' start h
  refine ⟨σ', ?_, out, hh, vals, hm, hv⟩
  have h' : execStmt O 2 R (programm BL BG hp rechte failure punkt ()) w0
      (.cons (Zahl.weiter (by decide) (by decide) ⟨0, le_refl _, le_refl _⟩)
        (.cons (Zahl.weiter (by decide) (by decide) ⟨0, le_refl _, le_refl _⟩) .nil)) = .ok σ' ρ' := h
  simp only [body, execEnd, eval, Expr.orte, World.lese, World.merke, List.map_nil, List.nil_append, nullByte]
  erw [h']
  rfl
end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammAkzeptiert
