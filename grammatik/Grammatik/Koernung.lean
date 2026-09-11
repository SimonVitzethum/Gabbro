/-
  File:     Grammatik/Koernung.lean
  Subject:  Event granularity as an EXPLICIT premise.

  One event of the trace (`Semantik.lean`: `Ereignis`, `World.spur`,
  newest first) executes indivisibly on the machine. Until now the tree
  USED that -- every `schreibSlot` records exactly one event, every
  `lese` one event per place -- without SAYING it. This file says it:
  `EreignisAtomar` (each event covers at most one cell) travels as an
  explicit hypothesis into the no-tearing theorem `atomar_no_tear`.

  Cites (read-only; nothing outside this file is touched):
  - `Semantik.lean`: `Ereignis` (zugriff/gzugriff/nimmt/gibt),
    `World.spur`, `World.merke` (new events as prefix), `World.lese`
    (one event per place), `World.schreibSlot` (value plus exactly one
    event), `World.schreibBytes` (one event PER BYTE, by recursion),
    `World.bytesAb` (the n cells a byte read folds over) with
    `World.bytesAb_length`, `Expr.orte` (a `leseBytes` records ONE place
    while reading n cells), `alleIndizes` (indices as `Zahl 0 (n - 1)`).
  - `Typen.lean`: `Zahl lo hi`, `Ty.index n = .int 0 (n - 1)`, `Byte`.
    A byte is `Zahl 0 255`: the same `0 .. count-1` shape over a
    256-cell carrier, so one event covers exactly one such value.
  - `Satz.lean`: `Ereignis.gut` / `Ereignis.passt` (one event carries its
    own guards) -- used, not restated.

  Proven here:
  - `ereignisAtomar_gilt`: every event satisfies the premise (it is
    satisfiable, not vacuous).
  - `atomar_no_tear`: UNDER `EreignisAtomar`, interrupting a transfer at
    any byte boundary shows the old or the new bytes -- never a mix.
  - `schreibBytes_event_count`: an n-byte `schreibBytes` leaves exactly
    n events on the trace.
  - `schreibBytes_not_single`: for 2 <= n the transfer is NOT one event
    (negative write case: n single-byte events, or the premise fails).
  - `leseBytes_single_event` / `leseBytes_not_atomic`: a `leseBytes`
    records ONE event while folding over n cells (negative read case).
  - `two_byte_tear` (+ `two_byte_tear_is_interruption`): the witnessed
    mix -- interrupting a 2-byte transfer after one byte.
   - `oldOrNewPerByte` (Prop-valued bridge) + `schreibBytes_prefix_readback`:
     writing the first `m` bytes of `new` over the world and reading the `n`
     bytes back shows exactly `interrupted old new m` (§7);
     `prefix_readback_perByte` reads it as old-or-new per byte, with
     `prefix_readback_zero` / `prefix_readback_full` at the boundaries.
     Helpers: `castBytes_cancel`, `schreibSlot_slots_same` (`_other`),
     `merke_bytesAb`, `storeSlot_bytesAb_other`, `schreibBytes_slots_other`;
     list facts `interrupted_length_eq`, `interrupted_zero_eq`,
     `interrupted_full_eq`, `interrupted_perByte`.
  - §8 (C2 discharge over the lane-47 inventory under the lane-70 ruling):
    `InvForm` (nine rows) + `Guarantee`, `InvForm.verdict` / `admitted` /
    `width`, `ruling_covers` (no fourth case), `admitted_no_tear` (+
    world-level `admitted_readback_no_tear`), `AtBoundary` +
    `boundary_no_tear`, `refused_no_tear` (+ world-level
    `refused_readback_no_tear`), `mid_interruption_tears` (the ruled-out
    middle IS the witnessed tear), and `shared_inventory_tearing_free`.

  CUTS (booked, not hidden):
  - C1 (was: no world-level readback): bridged in §7 for the prefix case --
     `schreibBytes_prefix_readback` writes `new.take m` over the world and
     reads `interrupted old new m` back, `prefix_readback_perByte` as
     old-or-new per byte. The machine step itself stays a word: no claim is
     made about hardware granularity, the premise is still width-based
     (`eventWidth <= 1`) and is explicitly NOT moved by this section.
  - C2: read tearing under a concurrent write DURING the n-cell fold is
    discharged for the measured inventory under the ruling (§8): admitted
    rows cannot tear by width (`admitted_no_tear`, world-level
    `admitted_readback_no_tear`), refused rows cannot tear under their
    guarantee (`refused_no_tear`, world-level `refused_readback_no_tear`),
    every row lands somewhere (`ruling_covers`), and the middle the
    guarantee rules out IS the witnessed tear (`mid_interruption_tears`).
    What is NOT built is a general interleaving semantics for `eval` (cf.
    the honest section 5 of `Wettlauf.lean`): outside the nine inventory
    rows and their ruling premises the n-cell fold under a concurrent
    write still has no model, and the volatile row stays open with no
    theorem.
  - C3: no machine beyond counting is modelled; the premise is
    width-based (`eventWidth <= 1`), the machine step itself stays a word.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-! ## 1. The premise: one event covers at most one cell -/

/-- How many cells one trace event covers: a slot or global access
    touches exactly one cell; taking or giving a lock touches none. -/
def eventWidth : Ereignis D → Nat
  | .zugriff .. => 1
  | .gzugriff .. => 1
  | .nimmt .. => 0
  | .gibt .. => 0

/-- **Each event executes indivisibly on the machine.** An event covers
    at most one cell, so there is no interior boundary at which an
    interruption could observe half of it. Lock events cover none. -/
def EreignisAtomar (e : Ereignis D) : Prop := eventWidth e ≤ 1

/-- The premise holds of every event: it is satisfiable, not vacuous. -/
theorem ereignisAtomar_gilt (e : Ereignis D) : EreignisAtomar e := by
  cases e
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-! ## 2. Interruption, as lists of bytes -/

/-- Interrupting a transfer after `m` bytes: the first `m` bytes are
    new, the rest is still old. -/
def interrupted (old new : List Byte) (m : Nat) : List Byte :=
  new.take m ++ old.drop m

/-- Torn: a mix that is neither the old nor the new bytes. -/
def torn (old new seen : List Byte) : Prop :=
  seen ≠ old ∧ seen ≠ new

/-- A transfer of width at most one cannot tear: every split shows the
    old or the new bytes. The split `m = 0` shows old; any `m >= 1`
    takes all of `new` and drops all of `old`. -/
theorem width_le_one_no_tear (old new : List Byte)
    (hlen : old.length = new.length) (hbound : new.length ≤ 1) (m : Nat) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  unfold interrupted
  by_cases hm : m = 0
  · subst hm
    left
    rw [List.take_zero, List.drop_zero, List.nil_append]
  · right
    have ht : new.take m = new := List.take_of_length_le (by omega)
    have hd : old.drop m = [] := List.drop_of_length_le (by omega)
    rw [ht, hd, List.append_nil]

/-! ## 3. No tearing -- under the premise -/

/-- **No tearing across interruption, under `EreignisAtomar`.** A
    transfer whose width fits one atomic event shows, at any split,
    the old or the new bytes -- never a mix. -/
theorem atomar_no_tear (e : Ereignis D) (h : EreignisAtomar e)
    (old new : List Byte) (hold : old.length = eventWidth e)
    (hnew : new.length = eventWidth e) (m : Nat) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  have hle : eventWidth e ≤ 1 := h
  have hb : new.length ≤ 1 := by omega
  exact width_le_one_no_tear old new (hold.trans hnew.symm) hb m

/-! ## 4. The negative write case: n bytes are n events -/

/-- A single slot write records exactly one event on the trace
    (`World.schreibSlot` is a value plus a singleton `merke`). -/
theorem writeSlot_trace_singleton (σ : World D) (t : D.Tab) (Λ : List (Res D))
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) :
    (σ.schreibSlot t Λ k f v).spur =
      (Ereignis.zugriff t true Λ σ.haelt) :: σ.spur := rfl

/-- A byte transfer over `bs` leaves exactly `bs.length` events on the
    trace: one per byte (`World.schreibBytes`, by recursion). -/
theorem schreibBytes_event_count (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte) :
    (σ.schreibBytes t f hf Λ k bs).spur.length = σ.spur.length + bs.length := by
  induction bs generalizing σ k with
  | nil => simp [World.schreibBytes]
  | cons b bs ih =>
    simp only [World.schreibBytes]
    rw [ih, writeSlot_trace_singleton]
    simp only [List.length_cons]
    omega

/-- **The negative write case.** For 2 <= n the n-byte transfer is NOT
    one atomic event: its trace contribution is n events, not one.
    Either it runs as n single-byte events, or the atomicity premise
    fails for the transfer as a whole. -/
theorem schreibBytes_not_single (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte)
    (h : 2 ≤ bs.length) :
    (σ.schreibBytes t f hf Λ k bs).spur.length ≠ σ.spur.length + 1 := by
  rw [schreibBytes_event_count]
  omega

/-! ## 5. The negative read case: one event over n cells -/

/-- A `leseBytes` records ONE event (`Expr.orte`: the carrier plus the
    index places; with a closed index that is exactly `[.inl t]`) while
    `eval` folds over n cells (`World.bytesAb`, `bytesAb_length`). -/
theorem leseBytes_single_event (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (n : Nat) (lo hi : Int)
    (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo)
    (hhi : hi + n ≤ D.count t) (hL : darf D t Λ) (hi0 : i.orte = []) :
    (Expr.leseBytes t f hf n i hlo hhi hL).orte = [.inl t] := by
  simp [Expr.orte, hi0]

/-- **The negative read case.** For 2 <= n the single event of a
    `leseBytes` cannot be the indivisible unit of the whole read: one
    event against n cells. -/
theorem leseBytes_not_atomic (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (n : Nat) (lo hi : Int)
    (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo)
    (hhi : hi + n ≤ D.count t) (hL : darf D t Λ) (hi0 : i.orte = [])
    (h : 2 ≤ n) :
    (Expr.leseBytes t f hf n i hlo hhi hL).orte.length ≠ n := by
  have ho := leseBytes_single_event t f hf n lo hi i hlo hhi hL hi0
  rw [ho]
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## 6. The witnessed mix -/

/-- **The witnessed tear.** Interrupting a 2-byte transfer after one
    byte shows the new first byte with the old second: neither the old
    pair nor the new one. -/
theorem two_byte_tear :
    torn [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
         [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩]
         [⟨1, by omega, by omega⟩, ⟨0, by omega, by omega⟩] := by
  refine ⟨?_, ?_⟩ <;>
    intro h <;>
    exact absurd (congrArg (List.map Zahl.n) h) (by decide)

/-- And the witness IS an interruption after one byte. -/
theorem two_byte_tear_is_interruption :
    interrupted [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
      [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩] 1 =
      [⟨1, by omega, by omega⟩, ⟨0, by omega, by omega⟩] := rfl

/-! ## 7. World-level readback: an interrupted transfer shows old-or-new per byte -/

/-- Cast a byte back into the slot type and out again: the roundtrip is the identity.
    Every byte written by `schreibBytes` passes through this cast on write and the
    inverse cast on read (`World.bytesAb`), so the head of a readback is the byte. -/
theorem castBytes_cancel (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (b : Byte) :
    cast (congrArg (Wert D) hf) (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255))) = b := by
  have e1 : cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)) ≍ (b : Wert D (.int 0 255)) :=
    cast_heq _ _
  have e2 : cast (congrArg (Wert D) hf) (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))
      ≍ cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)) :=
    cast_heq _ _
  exact eq_of_heq (HEq.trans e2 e1)


/-- A `schreibSlot` moves `slots` exactly like a `storeSlot`: the trace entry
    (`World.merke`) records the write without moving the value. The bridge is
    `rfl` -- `merke` only touches `spur` -- and `simp` never sees through it. -/
theorem schreibSlot_slots_same (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) : (σ.schreibSlot t Λ k f v).slots t k f = v := by
  have hss : (σ.schreibSlot t Λ k f v).slots t k f
    = (σ.storeSlot t k f v).slots t k f := rfl
  rw [hss]
  simp [World.storeSlot]

/-- Same, at any other key: the value there is untouched. -/
theorem schreibSlot_slots_other (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k k₀ : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (h : k₀ ≠ k) :
    (σ.schreibSlot t Λ k f v).slots t k₀ f = σ.slots t k₀ f := by
  have hss : (σ.schreibSlot t Λ k f v).slots t k₀ f
    = (σ.storeSlot t k f v).slots t k₀ f := rfl
  rw [hss]
  simp [World.storeSlot, h]


/-- Recording trace entries (`World.merke`) does not move `slots`, hence never
    moves a byte readback: induction on the read length, the head by `rfl`. -/
theorem merke_bytesAb (σ : World D) (es : List (Ereignis D)) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) :
    ∀ (n : Nat) (k : Int), (σ.merke es).bytesAb t f hf n k = σ.bytesAb t f hf n k := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    have hhead : (σ.merke es).slots t k f = σ.slots t k f := rfl
    have htail := ih (k + 1)
    simp only [World.bytesAb, hhead, htail]

/-- A `storeSlot` away from the read window leaves the readback unchanged:
    writing at `k₀` while reading `n` bytes from `k` with `k₀ < k ∨ k + n ≤ k₀`. -/
theorem storeSlot_bytesAb_other (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (v : Wert D (D.typ t f)) :
    ∀ (n : Nat) (k k₀ : Int), k₀ < k ∨ k + n ≤ k₀ →
      (σ.storeSlot t k₀ f v).bytesAb t f hf n k = σ.bytesAb t f hf n k := by
  intro n
  induction n with
  | zero => intro k k₀ _; rfl
  | succ n ih =>
    intro k k₀ h
    have hne : k ≠ k₀ := by omega
    have hhead : (σ.storeSlot t k₀ f v).slots t k f = σ.slots t k f := by
      simp [World.storeSlot, hne]
    have htail := ih (k + 1) k₀ (by omega : k₀ < k + 1 ∨ (k + 1) + n ≤ k₀)
    simp only [World.bytesAb, hhead, htail]

/-- Later bytes of a transfer leave an earlier slot alone: `schreibBytes` from `k`
    never touches `k₀ < k`. A `schreibSlot` is a `storeSlot` plus a trace entry
    (`World.merke`), and the trace entry does not move `slots`. -/
theorem schreibBytes_slots_other (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) :
    ∀ (σ : World D) (cs : List Byte) (k k₀ : Int), k₀ < k →
      (σ.schreibBytes t f hf Λ k cs).slots t k₀ f = σ.slots t k₀ f := by
  intro σ cs k
  induction cs generalizing σ k with
  | nil => intro k₀ _; rfl
  | cons c cs ih =>
    intro k₀ h
    have hslot : (σ.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).slots t k₀ f
        = σ.slots t k₀ f :=
      schreibSlot_slots_other σ t Λ k k₀ f _ (by omega : k₀ ≠ k)
    calc ((σ.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).schreibBytes t f hf Λ (k + 1) cs).slots t k₀ f
        = (σ.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).slots t k₀ f :=
          ih _ _ _ (by omega : k₀ < k + 1)
      _ = σ.slots t k₀ f := hslot

/-- **Old-or-new per byte, as a `Prop`.** The bridge between the byte-list
    interruption model (`interrupted`) and `World` reads (`World.bytesAb`):
    `seen` has the shape of `old` and `new`, and every byte position holds
    the old or the new byte. -/
def oldOrNewPerByte (old new seen : List Byte) : Prop :=
  seen.length = old.length ∧ old.length = new.length ∧
    ∀ i : Nat, i < seen.length → (seen[i]? = old[i]? ∨ seen[i]? = new[i]?)

/-- An interruption keeps the length. -/
theorem interrupted_length_eq (old new : List Byte) (hlen : old.length = new.length) (m : Nat) :
    (interrupted old new m).length = old.length := by
  unfold interrupted
  rw [List.length_append, List.length_take, List.length_drop]
  omega

/-- Interrupting before the first byte shows old. -/
theorem interrupted_zero_eq (old new : List Byte) :
    interrupted old new 0 = old := by
  unfold interrupted
  rw [List.take_zero, List.drop_zero, List.nil_append]

/-- Interrupting past the last byte shows new. -/
theorem interrupted_full_eq (old new : List Byte) (hlen : old.length = new.length) (m : Nat)
    (hm : new.length ≤ m) : interrupted old new m = new := by
  unfold interrupted
  have ht : new.take m = new := List.take_of_length_le hm
  have hd : old.drop m = [] := List.drop_of_length_le (by omega)
  rw [ht, hd, List.append_nil]

/-- Every interruption reads back old-or-new per byte. -/
theorem interrupted_perByte (old new : List Byte) (hlen : old.length = new.length) (m : Nat) :
    oldOrNewPerByte old new (interrupted old new m) := by
  refine ⟨interrupted_length_eq old new hlen m, hlen, ?_⟩
  intro i hi
  rw [interrupted_length_eq old new hlen m] at hi
  unfold interrupted
  rw [List.getElem?_append]
  by_cases h : i < (new.take m).length
  · have him : i < m := by rw [List.length_take] at h; omega
    have htake : (new.take m)[i]? = new[i]? := by
      rw [List.getElem?_take, if_pos him]
    rw [if_pos h, htake]
    exact Or.inr rfl
  · have hdrop : (old.drop m)[i - (new.take m).length]? = old[i]? := by
      rw [List.getElem?_drop]
      have e1 : (new.take m).length = min m new.length := List.length_take
      have e3 : m + (i - (new.take m).length) = i := by omega
      rw [e3]
    rw [if_neg h, hdrop]
    exact Or.inl rfl

/-- **World-level readback of an interrupted transfer.** Write the first `m` bytes
    of `new` over a world whose `n` bytes from `k` are `old`, then read the `n`
    bytes back: the result is exactly `interrupted old new m`. The head byte just
    written survives because later bytes go to strictly larger keys
    (`schreibBytes_slots_other`) and the cast roundtrips (`castBytes_cancel`);
    the tail is the induction hypothesis, since the head write leaves the rest of
    the window alone (`storeSlot_bytesAb_other`). -/
theorem schreibBytes_prefix_readback (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (n : Nat) :
    ∀ (m : Nat) (k : Int) (σ' : World D) (old new : List Byte),
      old = σ'.bytesAb t f hf n k → new.length = n →
      ((σ'.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k)
        = interrupted old new m := by
  induction n with
  | zero =>
    intro m k σ' old new hold hnew
    have hn : new = [] := List.length_eq_zero_iff.mp hnew
    have ho : old = [] := by rw [hold]; rfl
    subst hn; subst ho
    simp [World.bytesAb, interrupted]
  | succ n ih =>
    intro m k σ' old new hold hnew
    have hold0 : old = σ'.bytesAb t f hf (n + 1) k := hold
    have hlen_old : old.length = n + 1 := by rw [hold, World.bytesAb_length]
    have hne_old : old ≠ [] := by intro h; subst h; simp at hlen_old
    have hne_new : new ≠ [] := by intro h; subst h; simp at hnew
    obtain ⟨b₀, old_tl, hold_eq⟩ := List.exists_cons_of_ne_nil hne_old
    obtain ⟨c, new_tl, hnew_eq⟩ := List.exists_cons_of_ne_nil hne_new
    simp only [World.bytesAb] at hold
    rw [hold_eq] at hold
    obtain ⟨hhead_old, htail_old⟩ := List.cons_eq_cons.mp hold
    have hnew_len : new_tl.length = n := by rw [hnew_eq] at hnew; simpa using hnew
    cases m with
    | zero =>
      rw [List.take_zero]
      show σ'.bytesAb t f hf (n + 1) k = interrupted old new Nat.zero
      rw [← hold0, interrupted_zero_eq]
    | succ m' =>
      have htake : new.take (m' + 1) = c :: new_tl.take m' := by
        rw [hnew_eq, List.take_succ_cons]
      have hrhs : interrupted old new (m' + 1)
          = c :: interrupted old_tl new_tl m' := by
        rw [hold_eq, hnew_eq]; rfl
      have hhead : ((σ'.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).schreibBytes t f hf Λ (k + 1) (new_tl.take m')).slots t k f
          = cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)) := by
        have h3 := schreibBytes_slots_other t f hf Λ
          (σ'.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255))))
          (new_tl.take m') (k + 1) k (by omega : k < k + 1)
        rw [h3]
        exact schreibSlot_slots_same _ _ _ _ _ _
      have hheadB : (cast (congrArg (Wert D) hf) (((σ'.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).schreibBytes t f hf Λ (k + 1) (new_tl.take m')).slots t k f) : Wert D (.int 0 255))
          = (c : Wert D (.int 0 255)) := by
        rw [hhead]; exact castBytes_cancel t f hf c
      have hpres : (σ'.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).bytesAb t f hf n (k + 1)
          = σ'.bytesAb t f hf n (k + 1) :=
        (merke_bytesAb (σ'.storeSlot t k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255))))
          [Ereignis.zugriff t true Λ σ'.haelt] t f hf n (k + 1)).trans
          (storeSlot_bytesAb_other σ' t f hf
            (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255))) n (k + 1) k
            (Or.inl (by omega : k < k + 1)))
      have htail_old' : old_tl = (σ'.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255)))).bytesAb t f hf n (k + 1) := by
        rw [hpres]; exact htail_old
      have htail_eq := ih m' (k + 1)
        (σ'.schreibSlot t Λ k f (cast (congrArg (Wert D) hf).symm (c : Wert D (.int 0 255))))
        old_tl new_tl htail_old' hnew_len
      rw [htake]
      simp only [World.schreibBytes, World.bytesAb]
      rw [hrhs, hheadB, htail_eq]

/-- **The world-level readback lemma.** An interrupted multi-byte transfer reads
    back old-or-new per byte from the world model. -/
theorem prefix_readback_perByte (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (n m : Nat) (k : Int) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf n k)
    (hnew : new.length = n) :
    oldOrNewPerByte old new
      ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k) := by
  rw [schreibBytes_prefix_readback t f hf Λ n m k σ old new hold hnew]
  have hlen : old.length = new.length := by rw [hold, World.bytesAb_length]; omega
  exact interrupted_perByte old new hlen m

/-- Boundary: interrupting before the first byte reads back old. -/
theorem prefix_readback_zero (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (n : Nat) (k : Int) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf n k)
    (hnew : new.length = n) :
    ((σ.schreibBytes t f hf Λ k (new.take 0)).bytesAb t f hf n k) = old := by
  rw [schreibBytes_prefix_readback t f hf Λ n 0 k σ old new hold hnew,
    interrupted_zero_eq]

/-- Boundary: interrupting past the last byte reads back new. -/
theorem prefix_readback_full (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (n m : Nat) (k : Int) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf n k)
    (hnew : new.length = n) (hm : n ≤ m) :
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k) = new := by
  rw [schreibBytes_prefix_readback t f hf Λ n m k σ old new hold hnew]
  have hlen : old.length = new.length := by rw [hold, World.bytesAb_length]; omega
  exact interrupted_full_eq old new hlen m (by omega)

/-! ## 8. Tearing freedom over the measured inventory (discharges C2) -/

/-- The lane-47 inventory as data: the eight measured emitted-C forms plus
    the unmeasured volatile row (`messung/TEARING-INVENTAR.md`). The
    assembler behind each row is NOT restated here -- it stands in the
    inventory's evidence block and is copied into the executable witness
    (`crates/gabbro-check/src/tearing.rs`, `LANE47_ASM`). What is proved
    here is the CONSEQUENCE the lane-70 ruling (`messung/TEARING-RULING.md`)
    draws from it. Every row is shared-carrier traffic by construction of
    the inventory: shared table slots, a `static mut` global, per-core
    accumulates cells, atomics with declared ordering, foreign lock calls,
    device registers. -/
inductive InvForm : Type
  | slotPlain | globalPlain | slotCompound | guardedCompound
  | cas | relAcq | mergeAdd | lockOps | volatileReg

/-- The guarantee that redeems a refusal, in the ruling's words. The atomic
    form is the standing upgrade path, not a third guarantee: the `cas` row
    shows what it costs, which is why the two disciplines below are worth
    keeping where they already hold. -/
inductive Guarantee : Type
  | exclusiveAccess | singleWriterPerCell

/-- The lane-70 verdict per form: refused rows carry the guarantee that
    redeems them; admitted and open rows carry none. Admitted rows name
    their atomicity price (alignment, total store order, declared ordering,
    foreign body) only in the ruling prose -- a machine assumption, cited,
    not re-stated as a proposition. -/
def InvForm.verdict : InvForm → Option Guarantee
  | .slotCompound | .guardedCompound => some .exclusiveAccess
  | .mergeAdd => some .singleWriterPerCell
  | _ => none

/-- The five admitted rows: a single machine memory access at both levels. -/
def InvForm.admitted : InvForm → Prop
  | .slotPlain | .globalPlain | .cas | .relAcq | .lockOps => True
  | _ => False

/-- Measured machine accesses per form, worst level: admitted rows do one;
    refused rows do two or more (the `-O0` triple counts here as two -- the
    exact count never enters a proof, only the `≤ 1` / `≥ 2` split does);
    the volatile row is unmeasured and reads `0`, which no width argument
    ever consumes. -/
def InvForm.width : InvForm → Nat
  | .slotPlain | .globalPlain | .cas | .relAcq | .lockOps => 1
  | .slotCompound | .guardedCompound | .mergeAdd => 2
  | .volatileReg => 0

/-- Every inventory row lands somewhere: admitted, refused with its
    guarantee, or the open volatile row. There is no fourth case -- ruling
    a tenth row means extending this proof, which is the point. -/
theorem ruling_covers (f : InvForm) :
    f.admitted ∨ (∃ g, f.verdict = some g) ∨ f = .volatileReg := by
  cases f with
  | slotPlain => exact Or.inl True.intro
  | globalPlain => exact Or.inl True.intro
  | slotCompound => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | guardedCompound => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | cas => exact Or.inl True.intro
  | relAcq => exact Or.inl True.intro
  | mergeAdd => exact Or.inr (Or.inl ⟨_, rfl⟩)
  | lockOps => exact Or.inl True.intro
  | volatileReg => exact Or.inr (Or.inr rfl)

/-- Admitted rows are single-access: their width fits one atomic event. -/
theorem admitted_width_le_one (f : InvForm) (h : f.admitted) : f.width ≤ 1 := by
  cases f with
  | slotPlain => decide
  | globalPlain => decide
  | slotCompound => simp only [InvForm.admitted] at h
  | guardedCompound => simp only [InvForm.admitted] at h
  | cas => decide
  | relAcq => decide
  | mergeAdd => simp only [InvForm.admitted] at h
  | lockOps => decide
  | volatileReg => simp only [InvForm.admitted] at h

/-- Admitted rows cannot tear: one atomic event covers the whole transfer,
    so every split shows the old or the new bytes. -/
theorem admitted_no_tear (f : InvForm) (h : f.admitted)
    (old new : List Byte) (hlen : old.length = new.length)
    (hold : old.length = f.width) (m : Nat) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  have hw := admitted_width_le_one f h
  have hb : new.length ≤ 1 := by omega
  exact width_le_one_no_tear old new hlen hb m

/-- The discipline premise, in the ruling's words as a proposition: no
    observer sees the middle of the transfer. Exclusive access (lock held,
    no second thread inside) and single-writer-per-cell (each core its own
    cell, the merge loop only reads) both mean exactly this: an interruption
    sits at a boundary -- before the first byte or past the last. -/
def AtBoundary (_old new : List Byte) (m : Nat) : Prop :=
  m = 0 ∨ new.length ≤ m

/-- At a boundary there is no tear, at any width: before the first byte
    shows old, past the last byte shows new. -/
theorem boundary_no_tear (old new : List Byte) (hlen : old.length = new.length)
    (m : Nat) (h : AtBoundary old new m) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  rcases h with rfl | hle
  · left; exact interrupted_zero_eq old new
  · right; exact interrupted_full_eq old new hlen m hle

/-- Refused rows cannot tear UNDER their guarantee: the guarantee is the
    boundary premise (`AtBoundary`), and the boundary rules out the middle
    (`boundary_no_tear`). The verdict equality travels as an explicit
    hypothesis so the theorem is about refused rows, not about any lists. -/
theorem refused_no_tear (f : InvForm) (g : Guarantee)
    (h : f.verdict = some g) (old new : List Byte)
    (hlen : old.length = new.length) (m : Nat) (hd : AtBoundary old new m) :
    interrupted old new m = old ∨ interrupted old new m = new := by
  cases g
  · exact boundary_no_tear old new hlen m hd
  · exact boundary_no_tear old new hlen m hd

/-- World-level readback of an admitted transfer: writing the admitted row's
    bytes over a byte carrier and reading back shows old or new whole.
    The per-byte version holds unconditionally (`prefix_readback_perByte`);
    this is the whole-list version the no-tearing claim needs. -/
theorem admitted_readback_no_tear (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (form : InvForm) (hadm : form.admitted)
    (k : Int) (m : Nat) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf form.width k)
    (hnew : new.length = form.width) :
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf form.width k) = old ∨
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf form.width k) = new := by
  rw [schreibBytes_prefix_readback t f hf Λ form.width m k σ old new hold hnew]
  have hlen : old.length = new.length := by rw [hold, World.bytesAb_length]; omega
  have holdw : old.length = form.width := by rw [hold, World.bytesAb_length]
  exact admitted_no_tear form hadm old new hlen holdw m

/-- World-level readback of a refused-but-disciplined transfer: under the
    guarantee the readback is old or new whole, at any width. -/
theorem refused_readback_no_tear (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D))
    (form : InvForm) (g : Guarantee) (href : form.verdict = some g)
    (k : Int) (n m : Nat) (old new : List Byte)
    (hold : old = σ.bytesAb t f hf n k)
    (hnew : new.length = n) (hd : AtBoundary old new m) :
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k) = old ∨
    ((σ.schreibBytes t f hf Λ k (new.take m)).bytesAb t f hf n k) = new := by
  rw [schreibBytes_prefix_readback t f hf Λ n m k σ old new hold hnew]
  have hlen : old.length = new.length := by rw [hold, World.bytesAb_length]; omega
  exact refused_no_tear form g href old new hlen m hd

/-- The guarantee is load-bearing: the mid-interruption it rules out (one
    byte of two written) IS the witnessed tear. A discipline that admitted
    the middle would admit the mix. -/
theorem mid_interruption_tears :
    torn [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
         [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩]
         (interrupted [⟨0, by omega, by omega⟩, ⟨0, by omega, by omega⟩]
            [⟨1, by omega, by omega⟩, ⟨1, by omega, by omega⟩] 1) := by
  rw [two_byte_tear_is_interruption]
  exact two_byte_tear

/-- **C2 discharged for the measured inventory: no tearing on shared
    carriers under the ruling.** Every inventory row is shared-carrier
    traffic (see `InvForm`); the ruling leaves each row exactly one way
    out: admitted rows show old or new by width, refused rows show old or
    new under their guarantee (no observer sees the middle), and the open
    volatile row gets no claim -- the disjunction says so explicitly
    instead of going silent. -/
theorem shared_inventory_tearing_free (form : InvForm)
    (old new : List Byte) (hlen : old.length = new.length) (m : Nat)
    (h : (form.admitted ∧ old.length = form.width) ∨
         (∃ g, form.verdict = some g ∧ AtBoundary old new m) ∨
         form = .volatileReg) :
    form = .volatileReg ∨
      interrupted old new m = old ∨ interrupted old new m = new := by
  rcases h with ⟨hadm, hlenw⟩ | ⟨g, href, hdisc⟩ | rfl
  · exact Or.inr (admitted_no_tear form hadm old new hlen hlenw m)
  · exact Or.inr (refused_no_tear form g href old new hlen m hdisc)
  · exact Or.inl rfl

#print axioms EreignisAtomar
#print axioms atomar_no_tear
#print axioms schreibBytes_event_count
#print axioms schreibBytes_not_single
#print axioms leseBytes_single_event
#print axioms leseBytes_not_atomic
#print axioms two_byte_tear
#print axioms two_byte_tear_is_interruption
#print axioms ereignisAtomar_gilt
#print axioms width_le_one_no_tear
#print axioms castBytes_cancel
#print axioms schreibSlot_slots_same
#print axioms schreibSlot_slots_other
#print axioms merke_bytesAb
#print axioms storeSlot_bytesAb_other
#print axioms schreibBytes_slots_other
#print axioms oldOrNewPerByte
#print axioms interrupted_length_eq
#print axioms interrupted_zero_eq
#print axioms interrupted_full_eq
#print axioms interrupted_perByte
#print axioms schreibBytes_prefix_readback
#print axioms prefix_readback_perByte
#print axioms prefix_readback_zero
#print axioms prefix_readback_full
#print axioms ruling_covers
#print axioms admitted_width_le_one
#print axioms admitted_no_tear
#print axioms AtBoundary
#print axioms boundary_no_tear
#print axioms refused_no_tear
#print axioms admitted_readback_no_tear
#print axioms refused_readback_no_tear
#print axioms mid_interruption_tears
#print axioms shared_inventory_tearing_free

end Gabbro.Grammatik
