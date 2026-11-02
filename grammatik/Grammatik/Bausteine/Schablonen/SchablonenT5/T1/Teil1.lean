module
public import Grammatik.Bausteine.Schablonen.SchablonenT5.T1.Teil1Basis
import all Grammatik.Bausteine.Schablonen.SchablonenT5.T1.Teil1Basis

public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik
/-! ## 6. `format.roundtrip` (format: 58 corpus lines).

(1) `read(write(x)) == x` for every representable `x` (`hRep`: the
written value fits the declared width, established by `M101`).
(2) A write to one field does not disturb a separate field (`hne`:
the fields are separate -- `trennt f g` from the layout itself,
held by `N008`). Model: one cell per field name; the layout-level
bit-disjointness this abstraction rests on is booked in CUTS, not
proved here. -/

/-- Abstract field store: one cell per field name. -/
def fieldStore : Type := String → Nat

/-- Write `v` to field `f` (masked to the declared width). -/
def fieldWrite (width : String → Nat) (σ : fieldStore) (f : String)
    (v : Nat) : fieldStore :=
  fun g => if g = f then v % 2 ^ (width f) else σ g

/-- Read field `f`. -/
def fieldRead (σ : fieldStore) (f : String) : Nat := σ f

/-- Roundtrip: reading back what was written gives the value. `hRep`
    is consumed by the mask removal. -/
theorem format_roundtrip (width : String → Nat) (σ : fieldStore)
    (f : String) (v : Nat) (hRep : v < 2 ^ (width f)) :
    fieldRead (fieldWrite width σ f v) f = v := by
  simp only [fieldRead, fieldWrite]
  rw [if_true, Nat.mod_eq_of_lt hRep]

/-- Non-interference: writing `f` leaves a separate field `g`
    undisturbed. `hne` is consumed by the branch. -/
theorem format_separate (width : String → Nat) (σ : fieldStore)
    (f g : String) (v : Nat) (hne : g ≠ f) :
    fieldRead (fieldWrite width σ f v) g = fieldRead σ g := by
  simp only [fieldRead, fieldWrite, if_neg hne]

/-- Witness for the `format` pair: roundtrip of `7` and undisturbed
    `"b"` after writing `"a"`. -/
theorem format_roundtrip_zeuge :
    (fieldRead (fieldWrite (fun _ => 8) (fun _ => 0) "a" 7) "a" = 7 ∧
      fieldRead (fieldWrite (fun _ => 8) (fun _ => 0) "a" 7) "b" =
        fieldRead (fun _ => 0) "b")
:= by
  have hRep : 7 < 2 ^ ((fun _ => 8 : String → Nat) "a") := by decide
  have hne : (("b" : String) ≠ "a") := by decide
  exact ⟨format_roundtrip _ _ "a" 7 hRep, format_separate _ _ "a" "b" 7 hne⟩

/-! ## 7. `gruppe.sperrabdruck` (locks: 292 corpus lines).

The group operation takes ALL locks of its carriers in ascending
`rank` order and holds them across the whole move (`U003`/`U005`/`H006`
establish the order; `U006` the absence of intermediate exits).
Three parts: (a) the declared order is acyclic -- a strictly ascending
take sequence never re-enters a lock, so the wait graph stays in
`less_than`; (b) the connecting invariant holds at BEGIN and END, NOT
in between -- the intermediate state is exactly why a group operation
exists; (c) no intermediate exit strands the move mid-way. -/

/-- Part (a): ascending rank order never re-enters a lock. `hAsc` is
    consumed by the induction. -/
theorem lock_order_no_reentry (ranks : List Nat)
    (hAsc : ranks.Pairwise (· < ·)) : ranks.Nodup := by
  induction ranks with
  | nil => exact List.nodup_nil
  | cons r rs ih =>
    cases hAsc with
    | cons hmem hrs =>
      rw [List.nodup_cons]
      exact ⟨fun hm => absurd (hmem _ hm) (Nat.lt_irrefl r), ih hrs⟩

/-- Part (b): BEGIN and END do not constrain the MIDDLE. There are a
    proposition, a start, a middle and an end with the proposition at
    both ends and its negation in the middle -- so demanding the
    invariant in between would be a strictly stronger, unkept promise.
    (This is `beobachtbares_gilt` read backwards: the locale spans the
    move, never its inside.) -/
theorem group_move_middle_free :
    ∃ (inv : Bool → Prop) (pre mid post : Bool),
      inv pre ∧ inv post ∧ ¬ inv mid :=
  ⟨(· = true), true, false, true, rfl, rfl, by decide⟩

/-- A group-move script: plain steps plus a leaving exit. -/
inductive GAct : Type
  | step : Nat → GAct
  | leave : GAct
  deriving DecidableEq

/-- Execution: `leave` aborts to `none`. -/
def gexec : List GAct → Nat → Option Nat
  | [], s => some s
  | .step k :: rest, s => gexec rest (s + k)
  | .leave :: _, _ => none

/-- The total step fold, ignoring exits. -/
def gfold : List GAct → Nat → Nat
  | [], s => s
  | .step k :: rest, s => gfold rest (s + k)
  | .leave :: rest, s => gfold rest s

/-- Part (c): with no intermediate exit in the script (`hNoExit`,
    established by `U006`), execution never aborts -- it equals the
    total fold. `hNoExit` is consumed in the `leave` case. -/
theorem group_move_no_exit (script : List GAct)
    (hNoExit : GAct.leave ∉ script) (s : Nat) :
    gexec script s = some (gfold script s) := by
  induction script generalizing s with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | step k =>
      have hr : GAct.leave ∉ rest :=
        fun hm => hNoExit (List.mem_cons_of_mem _ hm)
      show gexec rest (s + k) = some (gfold rest (s + k))
      exact ih hr _
    | leave =>
      have hc : False := hNoExit (List.mem_cons.mpr (Or.inl rfl))
      exact hc.elim

/-- Witness for `lock_order_no_reentry`: ranks `[0, 1]` ascend. -/
theorem lock_order_no_reentry_zeuge :
    ([0, 1] : List Nat).Nodup
:= by
  have hAsc : ([0, 1] : List Nat).Pairwise (· < ·) := by decide
  exact lock_order_no_reentry _ hAsc

/-! ## 8. `entry.abdruck` (entry 89 / clobbers 80 corpus lines).

(1) The generated entry path preserves every register from
`preserves` (`hPres`: no path write targets a preserved register).
(2) It writes no register outside `clobbers` (`hClob`: every path
write targets `clobbers`). (3) The stack switch is NOT an obligation
but an undefined word -- documented, not stated. Model: an abstract
register file; the hardware meaning of each register is booked in
CUTS. -/

/-- Abstract register file. -/
def regFile : Type := String → Nat

/-- Run an entry path over a register file. -/
def regRun : List (String × Nat) → regFile → regFile
  | [], σ => σ
  | (r, v) :: rest, σ => regRun rest (fun q => if q = r then v else σ q)

/-- Part (1): preserved registers survive the path. -/
private theorem entry_keeps_aux (P : List String) (path : List (String × Nat))
    (hPres : ∀ w ∈ path, w.1 ∉ P) (σ : regFile) (r : String)
    (hr : r ∈ P) : regRun path σ r = σ r := by
  induction path generalizing σ with
  | nil => rfl
  | cons w rest ih =>
    obtain ⟨a, b⟩ := w
    have hni : a ∉ P := hPres _ (List.mem_cons.mpr (Or.inl rfl))
    have hrne : r ≠ a := fun he => hni (he ▸ hr)
    have hrest : ∀ u ∈ rest, u.1 ∉ P :=
      fun u hu => hPres u (List.mem_cons_of_mem _ hu)
    exact (ih hrest _).trans (if_neg hrne)

theorem entry_keeps (path : List (String × Nat)) (P : List String)
    (hPres : ∀ w ∈ path, w.1 ∉ P) (σ : regFile) (r : String)
    (hr : r ∈ P) : regRun path σ r = σ r :=
  entry_keeps_aux P path hPres σ r hr

/-- Part (2): a changed register is in `clobbers`. -/
private theorem entry_same_aux (C : List String) (path : List (String × Nat))
    (hClob : ∀ w ∈ path, w.1 ∈ C) (σ : regFile) (r : String)
    (hrC : r ∉ C) : regRun path σ r = σ r := by
  induction path generalizing σ with
  | nil => rfl
  | cons w rest ih =>
    obtain ⟨a, b⟩ := w
    have hmem : a ∈ C := hClob _ (List.mem_cons.mpr (Or.inl rfl))
    have hrne : r ≠ a := fun he => hrC (he.symm ▸ hmem)
    have hrest : ∀ u ∈ rest, u.1 ∈ C :=
      fun u hu => hClob u (List.mem_cons_of_mem _ hu)
    have step : (fun q => if q = a then b else σ q) r = σ r :=
      if_neg hrne
    exact (ih hrest _).trans step

theorem entry_clobbers (path : List (String × Nat)) (C : List String)
    (hClob : ∀ w ∈ path, w.1 ∈ C) (σ : regFile) (r : String)
    (h : regRun path σ r ≠ σ r) : r ∈ C := by
  by_cases hrC : r ∈ C
  · exact hrC
  · exact absurd (entry_same_aux C path hClob σ r hrC) h

/-- Witness for the `entry` pair: path `[("t0", 1)]` keeps `"s0"` and
    changes only `"t0"`. -/
theorem entry_keeps_zeuge :
    (regRun [("t0", 1)] (fun _ => 0) "s0" = 0 ∧
      "t0" ∈ (["t0"] : List String))
:= by
  have hPres : ∀ w ∈ ([("t0", 1)] : List (String × Nat)), w.1 ∉ (["s0"] : List String) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [hw, List.mem_cons, String.reduceEq, List.not_mem_nil, or_self, not_false_eq_true]
  have hClob : ∀ w ∈ ([("t0", 1)] : List (String × Nat)), w.1 ∈ (["t0"] : List String) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
  have hkeep := entry_keeps _ ["s0"] hPres (fun _ => 0) "s0" (by decide)
  have hchange := entry_clobbers _ ["t0"] hClob (fun _ => 0) "t0" (by decide)
  exact ⟨hkeep, hchange⟩

/-! ## 9. `transition.transset` (transition: 34 corpus lines).

Several places in ONE move: no intermediate state is observable FOR A
NAMED OBSERVER (`Obs`: the observer's footprint; `hObs` names the two
moved places as outside it -- on one core the control flow, on several
every core that does not hold the move's lock). Without a named
observer the promise is empty on a multicore. Model: slot states as
place valuations; the joint move writes both places at once; the trace
holds exactly the before/after worlds. -/

/-- A joint move writes two places at once. -/
def jointMove (σ : Nat → Nat) (p1 p2 v1 v2 : Nat) : Nat → Nat :=
  fun p => if p = p1 then v1 else if p = p2 then v2 else σ p

/-- The trace of the joint move: before and after, no middle. -/
def jointTrace (σ : Nat → Nat) (p1 p2 v1 v2 : Nat) : List (Nat → Nat) :=
  [σ, jointMove σ p1 p2 v1 v2]

end Gabbro.Grammatik
