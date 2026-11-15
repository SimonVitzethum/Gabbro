module

public import Grammatik.Speichermodell.Atomar.AtomarSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Basic

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}

def StatementResult : Ausgang V l Γ → Prop
  | .logik _ => False
  | _ => True

def EndResult : EndAusgang V l Γ → Prop
  | .logik _ => False
  | _ => True

theorem statement_shrink {τ : Ty} (result : Ausgang V l (τ :: Γ))
    (valid : StatementResult result) : StatementResult result.schrumpf := by
  cases result <;> exact valid

theorem end_shrink {τ : Ty} (result : EndAusgang V l (τ :: Γ))
    (valid : EndResult result) : EndResult result.schrumpf := by
  cases result <;> exact valid

abbrev StatementSafe {Λ Λ' : List (Res D)} (code : Stmt D V l Γ Λ Λ') :=
  ∀ S O U A passes R world locals,
    StatementResult (execStmtHA S O U A passes R code world locals)

abbrev BlockSafe {Λ Λ' : List (Res D)} (code : Block D V l Γ Λ Λ') :=
  ∀ S O U A passes R world locals,
    StatementResult (execBlockHA S O U A passes R code world locals)

abbrev EndSafe {Λ : List (Res D)} (code : Endblock D V l Γ Λ) :=
  ∀ S O U A passes R world locals,
    EndResult (execEndHA S O U A passes R code world locals)

mutual

/-- A syntax certificate for total typed primitives. It reasons about the actual
    atomic semantics for every read environment, without replaying SC reads.
    Locks, program calls, annotations and potentially failing forms are excluded.
    A typed oracle answer is checked through its entire continuation. -/
def statement {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (fuel : Nat) → (code : Stmt D V l Γ Λ Λ') → Option (PLift (StatementSafe code))
  | 0, _ => none
  | fuel + 1, code => match code with
    | .assignSlot .. | .assignThru .. | .assignSlotRef .. | .assignGlob .. | .assignVar ..
      | .ret .. | .retWhy .. | .leave .. | .next .. =>
        some ⟨fun _ _ _ _ _ _ _ _ => trivial⟩
    | .breaking _ body => do
        let checked ← block fuel body
        return ⟨fun S O U A passes R world locals =>
          checked.down S O U A passes R world locals⟩
    | .ite condition yes no => do
        let yesChecked ← block fuel yes
        let noChecked ← block fuel no
        return ⟨fun S O U A passes R world locals => by
          dsimp only [execStmtHA]
          split
          · exact yesChecked.down S O U A passes R _ locals
          · exact noChecked.down S O U A passes R _ locals⟩
    | _ => none

def block {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (fuel : Nat) → (code : Block D V l Γ Λ Λ') → Option (PLift (BlockSafe code))
  | 0, _ => none
  | fuel + 1, code => match code with
    | .nil => some ⟨fun _ _ _ _ _ _ _ _ => trivial⟩
    | .cons head tail => do
        let headChecked ← statement fuel head
        let tailChecked ← block fuel tail
        return ⟨fun S O U A passes R world locals => by
          have valid := headChecked.down S O U A passes R world locals
          dsimp only [execBlockHA]
          cases result : execStmtHA S O U A passes R head world locals with
          | ok next env => exact tailChecked.down S O U A passes R next env
          | logik error => exact (by simpa only [result, StatementResult] using valid)
          | _ => trivial⟩
    | .bind expression tail => do
        let checked ← block fuel tail
        return ⟨fun S O U A passes R world locals =>
          statement_shrink _ (checked.down S O U A passes R _ _)⟩
    | .bindAxiom item arguments same _ _ _ _ tail => do
        let checked ← block fuel tail
        return ⟨fun S O U A passes R world locals => by
          dsimp only [execBlockHA]
          cases answer : axiomAntwort O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value => exact statement_shrink _ (checked.down S O U A passes R _ _)⟩
    | _ => none

end

def ending {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (fuel : Nat) → (code : Endblock D V l Γ Λ) → Option (PLift (EndSafe code))
  | 0, _ => none
  | fuel + 1, code => match code with
    | .ret .. | .retWhy .. | .leave .. | .next .. =>
        some ⟨fun _ _ _ _ _ _ _ _ => trivial⟩
    | .cons head tail => do
        let headChecked ← statement fuel head
        let tailChecked ← ending fuel tail
        return ⟨fun S O U A passes R world locals => by
          have valid := headChecked.down S O U A passes R world locals
          dsimp only [execEndHA]
          cases result : execStmtHA S O U A passes R head world locals with
          | ok next env => exact tailChecked.down S O U A passes R next env
          | logik error => exact (by simpa only [result, StatementResult] using valid)
          | _ => trivial⟩
    | .bind expression tail => do
        let checked ← ending fuel tail
        return ⟨fun S O U A passes R world locals =>
          end_shrink _ (checked.down S O U A passes R _ _)⟩
    | .bindAxiom item arguments same _ _ _ _ tail => do
        let checked ← ending fuel tail
        return ⟨fun S O U A passes R world locals => by
          dsimp only [execEndHA]
          cases answer : axiomAntwort O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value => exact end_shrink _ (checked.down S O U A passes R _ _)⟩
    | .ite condition yes no => do
        let yesChecked ← ending fuel yes
        let noChecked ← ending fuel no
        return ⟨fun S O U A passes R world locals => by
          dsimp only [execEndHA]
          split
          · exact yesChecked.down S O U A passes R _ locals
          · exact noChecked.down S O U A passes R _ locals⟩
    | _ => none

theorem noLogic {Λ : List (Res D)} {code : Endblock D V l Γ Λ}
    (checked : EndSafe code) (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    (A : AUmwelt D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (world : World D) (locals : Env D Γ) (error : Logik D) :
    execEndHA S O U A passes R code world locals ≠ .logik error := by
  intro returned
  have valid := checked S O U A passes R world locals
  rw [returned] at valid
  exact valid

end Gabbro.Grammatik.Vertraege.Pruefer.Basic
