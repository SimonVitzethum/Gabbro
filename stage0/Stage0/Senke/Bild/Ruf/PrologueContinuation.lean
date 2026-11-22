module

public import Stage0.Senke.Bild.Mehr.Ort.IRStartup

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Stage0.Senke.BildMehr Runner Runner.IR Runner.Beweis

/-- The remaining instructions of an established IR region. Its current
    instruction may be between requests, and the last full instruction
    ends at the same fixed boundary in every case. -/
def IRContinuation [kernel : Kern] (target : T) (finish : Mem) (control : Res T) (memory : Mem) : Prop :=
  match control with
  | .next pointer => ∃ count, @IRReference kernel.withoutSyscalls count pointer memory target finish
  | .ask .. => ∃ next middle count,
      @Run kernel.withoutSyscalls control memory next middle ∧
      @IRReference kernel.withoutSyscalls count next middle target finish
  | .fault | .unk => False

private theorem IRContinuation.ofRun [kernel : Kern] {target next : T} {memory middle finish : Mem}
    {control : Res T} {count : Nat} (step : @Run kernel.withoutSyscalls control memory next middle)
    (remaining : @IRReference kernel.withoutSyscalls count next middle target finish) :
    IRContinuation target finish control memory := by
  cases control with
  | next pointer =>
    cases step
    exact ⟨count, remaining⟩
  | ask request resume => exact ⟨next, middle, count, step, remaining⟩
  | fault | unk => cases step

theorem IRContinuation.noHost [Kern] {target : T} {memory finish : Mem} {request : Req} {resume : Ans → Res T}
    (pending : IRContinuation target finish (.ask (.sys request) resume) memory) : False := by
  obtain ⟨_, _, _, instruction, _⟩ := pending
  cases instruction with
  | ask impossible _ => cases impossible
  | sys impossible _ => exact impossible

theorem IRContinuation.not_fault [Kern] {target : T} {memory finish : Mem} {control : Res T}
    (continuation : IRContinuation target finish control memory) : control ≠ .fault := by
  rintro rfl
  exact continuation

/-- A restricted continuation certifies its next request from the Lean IR
    semantics and the permissions of its reference memory. -/
theorem IRContinuation.request_scope [Kern] {target : T} {memory finish : Mem}
    {request : Op} {resume : Ans → Res T} {reads writes : W → Prop}
    (continuation : IRContinuation target finish (.ask request resume) memory)
    (blind : Blind (.ask request resume))
    (readable : ∀ byte, memory.rd byte = true → reads byte)
    (writable : ∀ byte, memory.wr byte = true → reads byte ∧ writes byte) :
    HostFreeControl reads writes (.ask request resume) := by
  have noHost (call : Req) (same : request = .sys call) : False := by
    subst request
    exact IRContinuation.noHost continuation
  obtain ⟨_, _, _, instruction, _⟩ := continuation
  cases instruction with
  | ask answered rest =>
    rename_i answer
    cases answer with
    | none =>
      rw [blind.missing] at rest
      cases rest
    | some words =>
      obtain ⟨readScope, writeScope⟩ := memAns_confined readable writable answered
      exact ⟨noHost, readScope, writeScope⟩
  | sys impossible _ => exact False.elim impossible
  | fp =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ impossible
      cases impossible
    · intro _ touched
      cases touched
    · intro writesMemory
      cases writesMemory

/-- Decoding the next instruction either opens the remaining reference
    or identifies the exact boundary where the region has finished. -/
theorem IRContinuation.decode [Kern] {target pointer : T} {memory finish : Mem}
    (continuation : IRContinuation target finish (.next pointer) memory) :
    (pointer = target ∧ memory = finish) ∨ IRContinuation target finish (IR.step pointer) memory := by
  obtain ⟨_, code⟩ := continuation
  cases code with
  | start => exact .inl ⟨rfl, rfl⟩
  | extend current remaining => exact .inr (.ofRun current remaining)

/-- Consuming an actual response preserves the restricted continuation
    and its reusable read and write permissions. -/
theorem IRContinuation.answer [kernel : Kern] {before after : imageTSO.St} {thread : Nat}
    {reads writes : W → Prop} {reference finish : Mem} {target : T}
    {request : Op} {resume : Ans → Res T} {answer : Ans}
    (continuation : IRContinuation target finish (.ask request resume) reference)
    (blind : Blind (.ask request resume))
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    (agreement : MaskedAgreement reads writes reference (before.1.view thread))
    (nativeUnique : ∀ kind a b first second, request = .fp kind a b →
      NativeFPEval kind a b first → NativeFPEval kind a b second → first = second)
    (replied : imageTSO.ans before thread request answer after) :
    ∃ updated, IRContinuation target finish (resume answer) updated ∧
      MaskedAgreement reads writes updated (after.1.view thread) ∧
      updated.rd = reference.rd ∧ updated.wr = reference.wr := by
  obtain ⟨_, _, _, instruction, suffix⟩ := continuation
  cases instruction with
  | ask expected rest =>
    have memory : istSpeicherOp request = true := by
      cases request <;> first | rfl | cases expected
    rename_i normalized
    cases normalized with
    | none =>
      rw [blind.missing] at rest
      cases rest
    | some words =>
      obtain ⟨sameControl, sameView⟩ :=
        tso_scoped_memory_response blind readable writable agreement memory expected replied.1
      have permissions := memAns_nurIn expected
      exact ⟨_, .ofRun (sameControl.symm ▸ rest) suffix, sameView, permissions.rd, permissions.wr⟩
  | sys impossible _ => exact False.elim impossible
  | fp expected rest =>
    obtain ⟨rfl, word, rfl, observed⟩ := replied.1
    have same := nativeUnique _ _ _ _ _ rfl expected observed
    cases same
    exact ⟨reference, .ofRun rest suffix, agreement, rfl, rfl⟩

/-- Adjacent regions preserve the unfinished part of the current
    instruction while extending its eventual destination. -/
theorem IRContinuation.append [kernel : Kern] {control : Res T} {memory middle finish : Mem}
    {target next : T} {count : Nat}
    (first : IRContinuation target middle control memory)
    (suffix : @IRReference kernel.withoutSyscalls count target middle next finish) :
    IRContinuation next finish control memory := by
  letI : Kern := kernel.withoutSyscalls
  cases control with
  | next pointer =>
    obtain ⟨_, initial⟩ := first
    exact ⟨_, initial.append suffix⟩
  | ask request resume =>
    obtain ⟨pointer, after, _, instruction, initial⟩ := first
    exact ⟨pointer, after, _, instruction, initial.append suffix⟩
  | fault | unk => exact False.elim first

end Gabbro.Stage0
