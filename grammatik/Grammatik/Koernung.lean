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

  CUTS (booked, not hidden):
  - C1: interruption-as-prefix (`interrupted`: first m bytes new, rest
    old) is a byte-LIST model. No world-level readback lemma (write a
    prefix, read it back) is proven here.
  - C2: read tearing under a concurrent write DURING the n-cell fold is
    not proven -- only the granularity mismatch (1 event vs n cells).
    No interleaving semantics for `eval` exists in the tree (cf. the
    honest section 5 of `Wettlauf.lean`).
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

end Gabbro.Grammatik
