import Grammatik.Berechenbarkeit.BrainfuckG.Programm
import Grammatik.Berechenbarkeit.BrainfuckG.SchrittWitnesses

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

/-- **Completeness witness**: the halting run of `.` is completed by budget 2 (normally or by the failure block). -/
theorem programm_vollstaendig_zeuge (O : Orakel BD)
    (R : ∀ f : BD.Fn, World BD → Env BD (BD.params f) → RufAusgang f) :
    (∃ σ' ρ', execStmt O 2 R (programm BL BG hp rechte failure punkt ()) w0 ρi = .ok σ' ρ' ∧
      Darstellt BL BG hp .nil (⟨1, 0, [], [], [], [0]⟩ : State 1) σ' ρ') ∨
    ∃ σf ρf, execStmt O 2 R (programm BL BG hp rechte failure punkt ()) w0 ρi =
      abbruch ((execEnd O 2 R failure σf ρf).zuAusgang) :=
  programm_vollstaendig O 2 R BL BG BG_inj hp rechte failure bricht punkt .nil () lauf rfl (by decide) w0 ρi start

/-- **The run itself**: the G statement of `.` completes normally -- two real passes, the second one leaving. -/
theorem programm_ok_zeuge (O : Orakel BD)
    (R : ∀ f : BD.Fn, World BD → Env BD (BD.params f) → RufAusgang f) :
    ∃ σ' ρ', execStmt O 2 R (programm BL BG hp rechte failure punkt ()) w0 ρi = .ok σ' ρ' := by
  have hdi := darstellt_lese (Λ := []) start (Expr.tru : Expr BD (BCtx 1 []) [] .bool).orte
  obtain ⟨σ1, ρ1, hpass1, hd1⟩ := durchgang_platz O 2 R BL BG BG_inj hp rechte failure punkt .nil _ _ ρi hdi
    (by decide) (.inr (by decide))
  have hdi1 := darstellt_lese (Λ := []) hd1 (Expr.tru : Expr BD (BCtx 1 []) [] .bool).orte
  obtain ⟨σ2, hpass2, _⟩ := durchgang_ende O 2 R BL BG hp rechte failure punkt .nil _ _ ρ1 hdi1 rfl
  exact ⟨σ2, ρ1, (runsUntil_iff O 2 R () .tru (pcIst 1) _ w0 ρi σ2 ρ1).mpr
    ⟨1, by decide, .more rfl (.inl hpass1) (.leave rfl hpass2)⟩⟩

/-- **Output witness**: that completion is a halting Brainfuck run of `.` on empty input, with its output on the
output stack. -/
theorem programm_haelt_zeuge (O : Orakel BD)
    (R : ∀ f : BD.Fn, World BD → Env BD (BD.params f) → RufAusgang f) :
    ∃ out, HaltsWith punkt [] out ∧ ∃ σ' vals, MultiRep BL BG σ' vals ∧ vals 3 = out.reverse.map (ablage hp) := by
  obtain ⟨σ', ρ', h⟩ := programm_ok_zeuge O R
  obtain ⟨out, hh, vals, hm, hv⟩ := programm_haelt O 2 R BL BG BG_inj hp rechte failure bricht punkt .nil () []
    w0 σ' ρi ρ' start h
  exact ⟨out, hh, σ', vals, hm, hv⟩

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.ProgrammWitnesses
