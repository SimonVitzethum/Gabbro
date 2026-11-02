module

public import Grammatik.Kern.Syntax.Marken.Owner.Conservation
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T3

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The serial of an activation is the position of its entry in the canonical
    call log, counted from the oldest event. Returns pop an activation but
    never rewind the log. Equal function/argument/world keys therefore still
    get different identities on repeated calls at the same stack depth.
    This reads ghost metadata from the existing log; it executes no program. -/
def ownerActivations : List (RufEreignisF D) → List Nat
  | [] => []
  | .eintritt .. :: log => log.length :: ownerActivations log
  | .rueck .. :: log => (ownerActivations log).tail
  | .why .. :: log => (ownerActivations log).tail

theorem ownerActivations_bounded (log : List (RufEreignisF D)) :
    ∀ n ∈ ownerActivations log, n < log.length := by
  induction log with
  | nil => intro n hn; cases hn
  | cons ev log ih =>
    cases ev with
    | eintritt f rho s0 =>
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (ih n hn)
    | rueck f rho v s0 s1 =>
      intro n hn
      exact Nat.lt_succ_of_lt (ih n (List.mem_of_mem_tail hn))
    | why f rho r s0 s1 =>
      intro n hn
      exact Nat.lt_succ_of_lt (ih n (List.mem_of_mem_tail hn))

/-- A new entry serial is fresh even after arbitrary completed nested calls. -/
theorem ownerActivations_fresh (log : List (RufEreignisF D)) :
    log.length ∉ ownerActivations log :=
  fun h => Nat.lt_irrefl _ (ownerActivations_bounded log _ h)

theorem ownerActivations_nodup (log : List (RufEreignisF D)) :
    (ownerActivations log).Nodup := by
  induction log with
  | nil => exact List.nodup_nil
  | cons ev log ih =>
    cases ev with
    | eintritt => exact List.nodup_cons.mpr ⟨ownerActivations_fresh log, ih⟩
    | rueck => exact ih.sublist (List.tail_sublist _)
    | why => exact ih.sublist (List.tail_sublist _)

/-- The serial stack annotates exactly the canonical key stack. This proof
    uses the actual G call-log invariant, including both return channels. -/
theorem ownerActivations_length {ks : List (Σ f : D.Fn, Env D (D.params f) × World D)}
    {log : List (RufEreignisF D)} (h : RufLogPasstG ks log) :
    (ownerActivations log).length = ks.length := by
  induction h with
  | leer => rfl
  | eintritt ks log f rho s0 h ih =>
    simpa only [ownerActivations, List.length_cons] using congrArg Nat.succ ih
  | rueck ks log f rho s0 v s1 h ih =>
    simpa only [ownerActivations, List.length_tail, List.length_cons, Nat.add_sub_cancel] using
      congrArg (fun n => n - 1) ih
  | why ks log f rho s0 r s1 h ih =>
    simpa only [ownerActivations, List.length_tail, List.length_cons, Nat.add_sub_cancel] using
      congrArg (fun n => n - 1) ih

/-- Exact identity of one invocation: resolved callee, arguments, old-entry
    world, immutable log prefix, caller serial and its suspended ancestors. -/
structure OwnerInvocation (D : Deklaration) where
  thread : Faden
  before : List (RufEreignisF D)
  callee : D.Fn
  arguments : Env D (D.params callee)
  entry : World D
  parent : Nat
  ancestors : List Nat
  active : ownerActivations before = parent :: ancestors

namespace OwnerInvocation

def caller (c : OwnerInvocation D) : ArenaOwnership.Frame := ⟨c.thread, c.parent⟩
def frame (c : OwnerInvocation D) : ArenaOwnership.Frame := ⟨c.thread, c.before.length⟩
def opened (c : OwnerInvocation D) : List (RufEreignisF D) :=
  .eintritt c.callee c.arguments c.entry :: c.before

theorem parent_before_entry (c : OwnerInvocation D) : c.parent < c.before.length :=
  ownerActivations_bounded c.before c.parent (by rw [c.active]; exact List.mem_cons_self)

theorem different_frames (c : OwnerInvocation D) : c.caller ≠ c.frame := by
  intro he
  have hn := congrArg ArenaOwnership.Frame.activation he
  exact Nat.ne_of_lt c.parent_before_entry hn

theorem opened_active (c : OwnerInvocation D) :
    ownerActivations c.opened = c.before.length :: c.parent :: c.ancestors := by
  simp only [opened, ownerActivations, c.active]

/-- A concrete G push has this exact entry, log and stack change. The actual
    step remains a premise; no mere adjacency of two numbers authorizes it. -/
structure Push (c : OwnerInvocation D) (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) : Prop where
  step : RufSchrittG P O passes M c.thread M'
  beforeLog : (M.faeden c.thread).log = c.before
  afterLog : (M'.faeden c.thread).log = c.opened
  key : RufSchluesselG (M'.faeden c.thread).kopf = ⟨c.callee, c.arguments, c.entry⟩
  stack : (M'.faeden c.thread).stapel.length = (M.faeden c.thread).stapel.length + 1

/-- A returning event must match this invocation's complete key. Both channels
    obey the one signature output inventory; neither rolls back consumed marks. -/
def Outcome (c : OwnerInvocation D) (ev : RufEreignisF D) : Prop :=
  (∃ v s1, ev = .rueck c.callee c.arguments v c.entry s1) ∨
  (∃ r s1, ev = .why c.callee c.arguments r c.entry s1)

/-- Bind an escrow return to an actual G pop. The active entry serial selects
    the original invocation even after nested calls or equal-key later calls.
    Keeping the immutable prefix also excludes a different historical entry. -/
structure Return (c : OwnerInvocation D) (P : Programm D) (O : Orakel D) (passes : Nat)
    (M M' : RufMaschineG D) : Prop where
  step : RufSchrittG P O passes M c.thread M'
  nested : List (RufEreignisF D)
  event : RufEreignisF D
  beforeLog : (M.faeden c.thread).log = nested ++ c.opened
  active : ownerActivations (M.faeden c.thread).log = c.before.length :: ownerActivations c.before
  outcome : c.Outcome event
  afterLog : (M'.faeden c.thread).log = event :: (M.faeden c.thread).log
  stack : (M.faeden c.thread).stapel.length = (M'.faeden c.thread).stapel.length + 1

theorem Return.restores_stack {c : OwnerInvocation D} {P : Programm D} {O : Orakel D}
    {passes : Nat} {M M' : RufMaschineG D} (h : c.Return P O passes M M') :
    ownerActivations (M'.faeden c.thread).log = ownerActivations c.before := by
  rw [h.afterLog]
  rcases h.outcome with ⟨v, s1, he⟩ | ⟨r, s1, he⟩ <;>
    simp only [he, ownerActivations, h.active, List.tail_cons]

end OwnerInvocation

end Gabbro.Grammatik
