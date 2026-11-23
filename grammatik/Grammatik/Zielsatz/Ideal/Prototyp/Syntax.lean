/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Syntax.lean
  Subject:   PROTOTYPE of step S7 (`dokumente/PERFECT-MODEL.md` §8): the syntax of the fragment, its plain
             operations and their execution against a list of outside answers.

  The fragment is a FAITHFUL MINIATURE, not the real G/GX: the real machine is indexed by a whole `Deklaration`
  and its per-thread replay (`ZielInvSA`) speaks about call frames, contracts and havoc environments that the
  question of S7 does not need. The miniature keeps exactly the parts the question is about:
  * two threads (`Fin 2`), each a list of UNITS (`Seg`): a lock section `lock k body`, a section under the
    interrupt mask `masked body` (thread 0 only, the handler runs on its core), one atomic operation, `lend` and
    `takeBack` of a DMA buffer, and a local assignment;
  * a unit body is a list of plain operations (`Op`): register assignment, plain load and store, and a device
    register read `dev`, an OUTSIDE question whose answer is an owned value (`dokumente/PERFECT-MODEL.md` §4);
  * one interrupt handler (a body of plain operations) on the core of thread 0;
  * every location carries its protection (`Prot`): a lock, the interrupt mask, or ownership by one thread (the
    DMA buffers). The protection is the static carrier discipline that the race and lock legs of the real model
    establish; here it is a premise checked by `Discipline.lean`.
-/
module

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- Point update of a function. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : upd f a b a = b := by
  simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) : upd f a b x = f x := by
  simp [upd, h]

theorem upd_apply {α β : Type} [DecidableEq α] (f : α → β) (a x : α) (b : β) :
    upd f a b x = if x = a then b else f x := rfl

/-- Registers of a thread (or of the handler). -/
abbrev Regs := Nat → Int
/-- The plain shared memory, locations are numbers. -/
abbrev Mem := Nat → Int

/-- Expressions over registers. -/
inductive Ex where
  | lit (v : Int)
  | reg (r : Nat)
  | add (a b : Ex)

/-- The value of an expression. -/
def Ex.eval (ρ : Regs) : Ex → Int
  | .lit v => v
  | .reg r => ρ r
  | .add a b => a.eval ρ + b.eval ρ

/-- A plain operation inside a unit body. -/
inductive Op where
  /-- register assignment -/
  | set (r : Nat) (e : Ex)
  /-- plain load of a shared location -/
  | load (r x : Nat)
  /-- plain store to a shared location -/
  | store (x : Nat) (e : Ex)
  /-- read of device register `d`: an outside question, the answer is an owned value in `r` -/
  | dev (r d : Nat)

/-- Memory order of an atomic operation. -/
inductive Ord where
  | rlx
  | sc

/-- An atomic operation on an atomic location. -/
inductive AOp where
  | ld (r a : Nat)
  | st (a : Nat) (e : Ex)
  | faa (r a : Nat) (e : Ex)

/-- A unit of a thread: the indivisible steps of the ideal meaning (§3.4). -/
inductive Seg where
  /-- `lock k { body }`: acquire, body, release -/
  | lock (k : Nat) (body : List Op)
  /-- `masked { body }`: the interrupt of the core is masked during `body` -/
  | masked (body : List Op)
  /-- one atomic operation -/
  | atom (o : Ord) (op : AOp)
  /-- lend the owned buffer `x` to the device -/
  | lend (x : Nat)
  /-- take the buffer `x` back; its content is an outside answer -/
  | takeBack (x : Nat)
  /-- a local assignment -/
  | set (r : Nat) (e : Ex)

/-- The protection of a location. -/
inductive Prot where
  | lock (k : Nat)
  | irq
  | own (t : Fin 2)
  deriving DecidableEq

/-- A fragment program: protections, two threads and the handler on the core of thread 0. -/
structure Prog where
  prot : Nat → Prot
  thread : Fin 2 → List Seg
  handler : List Op

/-- One plain operation with its answer (`some v` exactly for `dev`). -/
def opStep : Op → Option Int → Regs × Mem → Option (Regs × Mem)
  | .set r e, none, (ρ, m) => some (upd ρ r (e.eval ρ), m)
  | .set _ _, some _, _ => none
  | .load r x, none, (ρ, m) => some (upd ρ r (m x), m)
  | .load _ _, some _, _ => none
  | .store x e, none, (ρ, m) => some (ρ, upd m x (e.eval ρ))
  | .store _ _, some _, _ => none
  | .dev r _, some v, (ρ, m) => some (upd ρ r v, m)
  | .dev _ _, none, _ => none

/-- A list of plain operations against the list of answers to its questions, consumed exactly. -/
def execOps : List Op → List Int → Regs × Mem → Option (Regs × Mem)
  | [], [], st => some st
  | [], _ :: _, _ => none
  | .dev r _ :: ops, v :: as, (ρ, m) => execOps ops as (upd ρ r v, m)
  | .dev _ _ :: _, [], _ => none
  | .set r e :: ops, as, (ρ, m) => execOps ops as (upd ρ r (e.eval ρ), m)
  | .load r x :: ops, as, (ρ, m) => execOps ops as (upd ρ r (m x), m)
  | .store x e :: ops, as, (ρ, m) => execOps ops as (ρ, upd m x (e.eval ρ))

/-- Running a prefix and then one operation is running the extended list. -/
theorem execOps_snoc : ∀ (done : List Op) (as : List Int) (st st₁ st₂ : Regs × Mem) (op : Op) (a : Option Int),
    execOps done as st = some st₁ → opStep op a st₁ = some st₂ →
    execOps (done ++ [op]) (as ++ a.toList) st = some st₂
  | [], [], st, st₁, st₂, op, a, h₁, h₂ => by
      simp only [execOps, Option.some.injEq] at h₁
      subst h₁
      obtain ⟨ρ, m⟩ := st
      cases op <;> cases a <;> simp_all [opStep, execOps]
  | [], _ :: _, _, _, _, _, _, h₁, _ => by simp [execOps] at h₁
  | .dev r _ :: ops, v :: as, (ρ, m), st₁, st₂, op, a, h₁, h₂ => by
      simp only [execOps] at h₁
      simpa [execOps] using execOps_snoc ops as _ st₁ st₂ op a h₁ h₂
  | .dev _ _ :: _, [], _, _, _, _, _, h₁, _ => by simp [execOps] at h₁
  | .set r e :: ops, as, (ρ, m), st₁, st₂, op, a, h₁, h₂ => by
      simp only [execOps] at h₁
      simpa [execOps] using execOps_snoc ops as _ st₁ st₂ op a h₁ h₂
  | .load r x :: ops, as, (ρ, m), st₁, st₂, op, a, h₁, h₂ => by
      simp only [execOps] at h₁
      simpa [execOps] using execOps_snoc ops as _ st₁ st₂ op a h₁ h₂
  | .store x e :: ops, as, (ρ, m), st₁, st₂, op, a, h₁, h₂ => by
      simp only [execOps] at h₁
      simpa [execOps] using execOps_snoc ops as _ st₁ st₂ op a h₁ h₂

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
