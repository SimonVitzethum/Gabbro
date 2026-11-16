module

public import Grammatik.Speichermodell.Atomar.AtomarSem.Teil1
public import Grammatik.Nebenlaeufigkeit.Sperren.Sources

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Basic

open Invarianten.Pruefer

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

theorem statement_optional (kind : Option Ty) (result : Ausgang V l (ErgCtx Γ kind))
    (valid : StatementResult result) : StatementResult (Ausgang.weiterOpt kind result) := by
  cases kind with
  | none => exact valid
  | some _ => exact statement_shrink result valid

theorem end_optional (kind : Option Ty) (result : EndAusgang V l (ErgCtx Γ kind))
    (valid : EndResult result) : EndResult (EndAusgang.weiterOpt kind result) := by
  cases kind with
  | none => exact valid
  | some _ => exact end_shrink result valid

theorem end_statement (result : EndAusgang V l Γ) (valid : EndResult result) :
    StatementResult result.zuAusgang := by
  cases result <;> exact valid

/-- A loop annotation must be true at every iteration. The body certificate
    excludes logic stops in every state, independently of the iteration bound. -/
theorem forever_safe (annotation : D.Annahme)
    (step : World D → Env D Γ → Ausgang V true Γ)
    (invariant : World D → Env D Γ → World D × Bool)
    (safe : ∀ world locals, StatementResult (step world locals))
    (truth : ∀ world locals, (invariant world locals).2 = true) :
    ∀ passes world locals,
      StatementResult (foreverLauf (l := l) annotation step invariant passes world locals) := by
  intro passes
  induction passes with
  | zero => intro world locals; trivial
  | succ passes ih =>
      intro world locals
      simp only [foreverLauf, truth, Bool.true_eq_false, ↓reduceIte]
      have valid := safe (invariant world locals).1 locals
      cases reply : step (invariant world locals).1 locals with
      | ok next env => exact ih next env
      | next _ next env => exact ih next env
      | logik error => simpa only [reply, StatementResult] using valid
      | _ => trivial

/-- Every finite traversal is total when its annotation is always true and
    each typed iteration is total, including the final and leave checks. -/
theorem traverse_safe {τ : Ty}
    (step : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (invariant : World D → Env D Γ → World D × Bool)
    (safe : ∀ world locals, StatementResult (step world locals))
    (truth : ∀ world locals, (invariant world locals).2 = true) :
    ∀ indices world locals,
      StatementResult (traverseLauf (l := l) step invariant indices world locals) := by
  intro indices
  induction indices with
  | nil =>
      intro world locals
      simp only [traverseLauf, truth, ↓reduceIte, StatementResult]
  | cons value indices ih =>
      intro world locals
      simp only [traverseLauf, truth, Bool.true_eq_false, ↓reduceIte]
      have valid := safe (invariant world locals).1 (.cons value locals)
      cases result : step (invariant world locals).1 (.cons value locals) with
      | ok next env => exact ih next env.tail
      | next _ next env => exact ih next env.tail
      | leave _ next env => simp only [truth, ↓reduceIte, StatementResult]
      | logik error => simpa only [result, StatementResult] using valid
      | _ => trivial

/-- Retry has no annotation failure: total body and overflow certificates
    establish totality for every bound without expanding the loop. -/
theorem retry_safe
    (step : World D → Env D Γ → Ausgang V true Γ)
    (test : World D → Env D Γ → World D × Bool)
    (overflow : World D → Env D Γ → Ausgang V l Γ)
    (safe : ∀ world locals, StatementResult (step world locals))
    (safeOverflow : ∀ world locals, StatementResult (overflow world locals)) :
    ∀ count world locals,
      StatementResult (retryLauf step test overflow count world locals) := by
  intro count
  induction count with
  | zero =>
      intro world locals
      simp only [retryLauf]
      split
      · trivial
      · exact safeOverflow _ _
  | succ count ih =>
      intro world locals
      simp only [retryLauf]
      split
      · trivial
      · have valid := safe (test world locals).1 locals
        cases result : step (test world locals).1 locals with
        | ok next env => exact ih next env
        | next _ next env => exact ih next env
        | logik error => simpa only [result, StatementResult] using valid
        | _ => trivial

abbrev StatementSafe (S : SperrInv D) {Λ Λ' : List (Res D)} (code : Stmt D V l Γ Λ Λ') :=
  ∀ O U A passes R world locals,
    StatementResult (execStmtHA S O U A passes R code world locals)

abbrev BlockSafe (S : SperrInv D) {Λ Λ' : List (Res D)} (code : Block D V l Γ Λ Λ') :=
  ∀ O U A passes R world locals,
    StatementResult (execBlockHA S O U A passes R code world locals)

abbrev EndSafe (S : SperrInv D) {Λ : List (Res D)} (code : Endblock D V l Γ Λ) :=
  ∀ O U A passes R world locals,
    EndResult (execEndHA S O U A passes R code world locals)

/-- Only literal source truth removes a release duty from this certificate.
    Other predicates remain obligations of the strict VC compiler. -/
def trivialLock {S : SperrInv D} (sources : LockSources S) (lock : D.Lock) :
    Option (PLift (∀ memory, S.inv lock memory = true)) := do
  let source ← sources lock
  match encoded : source.expression with
  | .tru =>
      return ⟨fun memory => by
        have meaning := source.correct (memory.welt [])
        rw [encoded] at meaning
        change true = S.inv lock memory at meaning
        exact meaning.symm⟩
  | _ => none

/-- Every scope in a lexical cleanup is checked, including empty payload locks. -/
def trivialScopes {S : SperrInv D} (sources : LockSources S) :
    (locks : List D.Lock) → Option (PLift (∀ world, scopesInvH S locks world = true))
  | [] => some ⟨fun _ => rfl⟩
  | lock :: locks => do
      let head ← trivialLock sources lock
      let tail ← trivialScopes sources locks
      return ⟨fun world => by
        simp only [scopesInvH, List.all_cons, head.down, Bool.true_and]
        exact tail.down world⟩

mutual

/-- A syntax certificate for total typed primitives. It reasons about the actual
    atomic semantics for every read environment, without replaying SC reads.
    Only source-reified literal-true locks are admitted; program calls and potentially failing forms remain excluded.
    A typed oracle answer is checked through its entire continuation. -/
def statement (S : SperrInv D) (sources : LockSources S) :
    (fuel : Nat) → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (code : Stmt D V l Γ Λ Λ') → Option (PLift (StatementSafe S code))
  | 0, _, _, _, _, _ => none
  | fuel + 1, _, _, _, _, code => match code with
    | .assignSlot .. | .assignThru .. | .assignThruOwn .. | .assignSlotRef ..
      | .assignGlob .. | .assignVar .. | .putBytes .. | .publish ..
      | .regWrite .. | .transition .. | .advances .. | .retires ..
      | .ret .. | .retWhy .. | .leave .. | .next .. =>
        some ⟨fun _ _ _ _ _ _ _ => trivial⟩
    | .retScoped expression cleanup => do
        let truth ← trivialScopes sources cleanup.scopes
        return ⟨fun _ _ _ _ _ _ _ => by
          simp only [execStmtHA, truth.down, ↓reduceIte, StatementResult]⟩
    | .retWhyScoped reason cleanup => do
        let truth ← trivialScopes sources cleanup.scopes
        return ⟨fun _ _ _ _ _ _ _ => by
          simp only [execStmtHA, truth.down, ↓reduceIte, StatementResult]⟩
    | .axiomCall .. => some ⟨fun O U A passes R world locals => by
        dsimp only [execStmtHA]
        split <;> trivial⟩
    | .axiomCallElse _ _ _ _ _ _ _ _ failure => do
        let checked ← ending S sources fuel failure
        return ⟨fun O U A passes R world locals => by
          dsimp only [execStmtHA]
          split
          · trivial
          · exact end_statement _ (end_shrink _ (checked.down O U A passes R _ _))
          · trivial⟩
    | .breaking _ body => do
        let checked ← block S sources fuel body
        return ⟨fun O U A passes R world locals =>
          checked.down O U A passes R world locals⟩
    | .ite condition yes no => do
        let yesChecked ← block S sources fuel yes
        let noChecked ← block S sources fuel no
        return ⟨fun O U A passes R world locals => by
          dsimp only [execStmtHA]
          split
          · exact yesChecked.down O U A passes R _ locals
          · exact noChecked.down O U A passes R _ locals⟩
    | .forever annotation .tru body => do
        let checked ← block S sources fuel body
        return ⟨fun O U A passes R world locals =>
          forever_safe annotation _ _ (checked.down O U A passes R)
            (fun _ _ => rfl) passes world locals⟩
    | .traverse table .tru body => do
        let checked ← block S sources fuel body
        return ⟨fun O U A passes R world locals =>
          traverse_safe _ _ (checked.down O U A passes R)
            (fun _ _ => rfl) (alleIndizes (D.count table)) world locals⟩
    | .retry 0 test _ overflow => do
        let exceeded ← block S sources fuel overflow
        return ⟨fun O U A passes R world locals => by
          dsimp only [execStmtHA, retryLauf]
          split
          · trivial
          · exact exceeded.down O U A passes R _ _⟩
    | .retry count test body overflow => do
        let checked ← block S sources fuel body
        let exceeded ← block S sources fuel overflow
        return ⟨fun O U A passes R world locals =>
          retry_safe _ _ _ (checked.down O U A passes R)
            (exceeded.down O U A passes R) count world locals⟩
    | .locks lock _ body => do
        let truth ← trivialLock sources lock
        let checked ← block S sources fuel body
        return ⟨fun O U A passes R world locals => by
          have valid := checked.down O U A passes R ((U lock world).nimmt lock) locals
          dsimp only [execStmtHA]
          cases result : execBlockHA S O U A passes R body ((U lock world).nimmt lock) locals <;>
            simp only [freiH, truth.down, ↓reduceIte, StatementResult]
          simpa only [result, StatementResult] using valid⟩
    | _ => none

def block (S : SperrInv D) (sources : LockSources S) :
    (fuel : Nat) → {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → (code : Block D V l Γ Λ Λ') → Option (PLift (BlockSafe S code))
  | 0, _, _, _, _, _ => none
  | fuel + 1, _, _, _, _, code => match code with
    | .nil => some ⟨fun _ _ _ _ _ _ _ => trivial⟩
    | .cons head tail => do
        let headChecked ← statement S sources fuel head
        let tailChecked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          have valid := headChecked.down O U A passes R world locals
          dsimp only [execBlockHA]
          cases result : execStmtHA S O U A passes R head world locals with
          | ok next env => exact tailChecked.down O U A passes R next env
          | logik error => exact (by simpa only [result, StatementResult] using valid)
          | _ => trivial⟩
    | .bind expression tail => do
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals =>
          statement_shrink _ (checked.down O U A passes R _ _)⟩
    | .exchange _ _ _ _ tail => do
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R _ _ =>
          statement_shrink _ (checked.down O U A passes R _ _)⟩
    | .awaits _ _ _ _ _ tail => do
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          split
          · exact statement_shrink _ (checked.down O U A passes R _ _)
          · trivial⟩
    | .regRead _ _ tail => do
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          split
          · split
            · exact statement_shrink _ (checked.down O U A passes R _ _)
            · trivial
          · trivial⟩
    | .bindAxiom item arguments same _ _ _ _ tail => do
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          cases answer : axiomAntwort O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value => exact statement_shrink _ (checked.down O U A passes R _ _)⟩
    | .bindAxiomElse item arguments same _ _ _ _ _ failure tail => do
        let failed ← ending S sources fuel failure
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          cases answer : axiomAntwortSonst O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value =>
                  cases value with
                  | inl value => exact statement_shrink _ (checked.down O U A passes R _ _)
                  | inr reason => exact end_statement _ (end_shrink _ (failed.down O U A passes R _ _))⟩
    | .bindAxiomOptElse kind item arguments same _ _ _ _ failure tail => do
        let failed ← ending S sources fuel failure
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          cases answer : axiomAntwortSonst O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value =>
                  cases value with
                  | inl value => exact statement_optional kind _ (checked.down O U A passes R _ _)
                  | inr reason => exact end_statement _ (end_shrink _ (failed.down O U A passes R _ _))⟩
    | .narrow expression low high fallback tail => do
        let failed ← ending S sources fuel fallback
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          split
          · exact statement_shrink _ (checked.down O U A passes R _ _)
          · exact end_statement _ (failed.down O U A passes R _ locals)⟩
    | .check condition fallback tail => do
        let failed ← ending S sources fuel fallback
        let checked ← block S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execBlockHA]
          split
          · exact checked.down O U A passes R _ locals
          · exact end_statement _ (failed.down O U A passes R _ locals)⟩
    | _ => none

def ending (S : SperrInv D) (sources : LockSources S) :
    (fuel : Nat) → {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → (code : Endblock D V l Γ Λ) → Option (PLift (EndSafe S code))
  | 0, _, _, _, _ => none
  | fuel + 1, _, _, _, code => match code with
    | .ret .. | .retWhy .. | .leave .. | .next .. =>
        some ⟨fun _ _ _ _ _ _ _ => trivial⟩
    | .retScoped expression cleanup => do
        let truth ← trivialScopes sources cleanup.scopes
        return ⟨fun _ _ _ _ _ _ _ => by
          simp only [execEndHA, truth.down, ↓reduceIte, EndResult]⟩
    | .retWhyScoped reason cleanup => do
        let truth ← trivialScopes sources cleanup.scopes
        return ⟨fun _ _ _ _ _ _ _ => by
          simp only [execEndHA, truth.down, ↓reduceIte, EndResult]⟩
    | .cons head tail => do
        let headChecked ← statement S sources fuel head
        let tailChecked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          have valid := headChecked.down O U A passes R world locals
          dsimp only [execEndHA]
          cases result : execStmtHA S O U A passes R head world locals with
          | ok next env => exact tailChecked.down O U A passes R next env
          | logik error => exact (by simpa only [result, StatementResult] using valid)
          | _ => trivial⟩
    | .bind expression tail => do
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals =>
          end_shrink _ (checked.down O U A passes R _ _)⟩
    | .exchange _ _ _ _ tail => do
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R _ _ =>
          end_shrink _ (checked.down O U A passes R _ _)⟩
    | .awaits _ _ _ _ _ tail => do
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          split
          · exact end_shrink _ (checked.down O U A passes R _ _)
          · trivial⟩
    | .regRead _ _ tail => do
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          split
          · split
            · exact end_shrink _ (checked.down O U A passes R _ _)
            · trivial
          · trivial⟩
    | .bindAxiom item arguments same _ _ _ _ tail => do
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          cases answer : axiomAntwort O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value => exact end_shrink _ (checked.down O U A passes R _ _)⟩
    | .bindAxiomElse item arguments same _ _ _ _ _ failure tail => do
        let failed ← ending S sources fuel failure
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          cases answer : axiomAntwortSonst O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value =>
                  cases value with
                  | inl value => exact end_shrink _ (checked.down O U A passes R _ _)
                  | inr reason => exact end_shrink _ (failed.down O U A passes R _ _)⟩
    | .bindAxiomOptElse kind item arguments same _ _ _ _ failure tail => do
        let failed ← ending S sources fuel failure
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          cases answer : axiomAntwortSonst O item _ _ with
          | mk next value =>
              cases value with
              | none => trivial
              | some value =>
                  cases value with
                  | inl value => exact end_optional kind _ (checked.down O U A passes R _ _)
                  | inr reason => exact end_shrink _ (failed.down O U A passes R _ _)⟩
    | .narrow expression low high fallback tail => do
        let failed ← ending S sources fuel fallback
        let checked ← ending S sources fuel tail
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          split
          · exact end_shrink _ (checked.down O U A passes R _ _)
          · exact failed.down O U A passes R _ locals⟩
    | .ite condition yes no => do
        let yesChecked ← ending S sources fuel yes
        let noChecked ← ending S sources fuel no
        return ⟨fun O U A passes R world locals => by
          dsimp only [execEndHA]
          split
          · exact yesChecked.down O U A passes R _ locals
          · exact noChecked.down O U A passes R _ locals⟩
    | _ => none

end

theorem noLogic {S : SperrInv D} {Λ : List (Res D)} {code : Endblock D V l Γ Λ}
    (checked : EndSafe S code) (O : Orakel D) (U : Umwelt D)
    (A : AUmwelt D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (world : World D) (locals : Env D Γ) (error : Logik D) :
    execEndHA S O U A passes R code world locals ≠ .logik error := by
  intro returned
  have valid := checked O U A passes R world locals
  rw [returned] at valid
  exact valid

end Gabbro.Grammatik.Vertraege.Pruefer.Basic
