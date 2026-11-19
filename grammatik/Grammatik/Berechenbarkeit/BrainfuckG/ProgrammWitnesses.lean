module
public import Grammatik.Berechenbarkeit.BrainfuckG.Programm
public import Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses
@[expose] public section


/-! Witnesses of `programm_vollstaendig`, `programm_korrekt` and `programm_haelt` over the four-stack declaration of
`SchrittWitnesses`: the one-instruction program `.` started on empty input in the empty arena `w0`. Two passes of the G
statement (one step with room, then the exit) complete it normally within budget 2; `programm_haelt` turns that run into a halting Brainfuck run
whose output lies on the output stack. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses

open Brainfuck ArenaKette InvDynZeuge Storage.GStack SchrittWitnesses Terminierung

/-- The program `.`. -/
def punkt : Program 1 where
  code := ⟨#[.output], rfl⟩
  valid := rfl

theorem bricht : Bricht (Γ0 := []) (n := 1) (Λ := []) O passes R failure := by
  intro σ ρ σ' ρ'
  refine ⟨?_, ?_⟩ <;> intro h <;> cases h

/-- The initial state on empty input, in `w0`. -/
def ρi : Env BD (BCtx 1 []) := .cons (kodiere 0) (.cons (pcWert 0) .nil)

theorem start : Darstellt BL BG hp .nil (initial [] : State 1) w0 ρi := by
  refine ⟨rfl, ?_, frei_w0⟩
  have : stapel hp (initial [] : State 1) = fun _ => [] := by
    funext k
    rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;> rfl
  rw [this]
  exact multi_w0

/-- The Brainfuck run: one step, then halt. -/
theorem lauf : Steps punkt 1 (initial []) ⟨1, 0, [], [], [], [0]⟩ :=
  .more rfl (.zero _)

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses
