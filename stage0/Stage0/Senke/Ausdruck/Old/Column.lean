/- Runtime old-slot indices select from an immutable, complete entry field column. -/
module
public import Stage0.Senke.Ausdruck.Old.Environment
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

namespace EntrySnapshots

/-- Ascending cell order makes a field column a contiguous sequence of full values. -/
def column (t : D.Tab) (f : D.Feld t) (first : Nat) : Nat → List (Zelle D)
  | 0 => []
  | n + 1 => .elem t f first :: column t f (first + 1) n

/-- Check before enumerating cells: oversized tables cannot allocate a compiler-side list.
    The final image additionally checks the caller-selected stack capacity. -/
def columnFits (t : D.Tab) (f : D.Feld t) : Bool :=
  decide (0 < (D.count t).toNat ∧ 8 * valueWords (D.typ t f) < 2 ^ 31 ∧
    FB + (D.count t).toNat * valueWords (D.typ t f) < 2 ^ 31)

@[simp] theorem column_words (t : D.Tab) (f : D.Feld t) (first n : Nat) :
    words (column t f first n) = n * valueWords (D.typ t f) := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih => simp only [column, words, Zelle.ty, ih, Nat.add_mul, Nat.one_mul]; omega

/-- Every in-range runtime index has its own saved complete span. -/
theorem column_at {L : Lay D} {world : World D} {m : Runner.Mem} {fp : Runner.W}
    (t : D.Tab) (f : D.Feld t) (n : Nat) :
    ∀ (first base j : Nat), j < n → At L world m fp (column t f first n) base →
      ValueAt L m fp (base + j * valueWords (D.typ t f))
        (D.typ t f) (world.slots t (first + j : Nat) f) := by
  induction n with
  | zero => intro first base j bound; omega
  | succ n ih =>
    intro first base j bound saved
    cases j with
    | zero => simpa only [Nat.zero_mul, Nat.add_zero, column, At, Zelle.ty, Zelle.val] using saved.1
    | succ j =>
      have tail := ih (first + 1) (base + valueWords (D.typ t f)) j (by omega) saved.2
      simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

end EntrySnapshots
end Gabbro.Stage0.Senke
