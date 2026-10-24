import Grammatik.Bausteine.Arena.Unbounded.Realization
import Grammatik.Bausteine.Arena.Struktur.ArenaDynZeuge

namespace Gabbro.Grammatik.ArenaStorage.Witnesses

open ArenaOwnership (Frame)

inductive Region where | storage

def owner : Frame := ⟨0, 0⟩
def borrower : Frame := ⟨0, 1⟩
def anotherThread : Frame := ⟨1, 0⟩
def empty : Heap Region Bool := .empty

def first : Heap Region Bool × Ref Region :=
  (empty.allocate .unbounded true owner true).get (by decide)

theorem first_allocation : empty.allocate .unbounded true owner true = some first := rfl

def released : Heap Region Bool := (first.1.release owner first.2).get (by decide)
theorem release_first : first.1.release owner first.2 = some released := rfl

def reused : Heap Region Bool × Ref Region :=
  (released.allocate .unbounded true owner false).get (by decide)

theorem reuse_allocation : released.allocate .unbounded true owner false = some reused := rfl

theorem read_write_zeuge :
    first.1.read owner first.2 = some true ∧
    (first.1.write owner first.2 false).bind (fun H => H.read owner first.2) = some false := by
  decide

theorem stale_and_double_free_zeuge :
    released.read owner first.2 = none ∧ released.release owner first.2 = none ∧
    reused.1.read owner first.2 = none ∧ reused.1.read owner reused.2 = some false ∧
    first.2.handle.slot = reused.2.handle.slot ∧
    first.2.handle.grant ≠ reused.2.handle.grant ∧ reused.1.extent = 1 := by decide

/-- Refusal is possible before the first cell and even on a reusable free slot. -/
theorem oom_zeuge :
    empty.allocate .unbounded false owner true = none ∧
    released.allocate .unbounded false owner false = none ∧
    released.allocateThen .unbounded false owner false
      (fun _ _ => true) (fun H => H.extent == 1) = true := by
  exact ⟨rfl, rfl, rfl⟩

def borrowed : Heap Region Bool := (first.1.lend owner borrower first.2).get (by decide)

theorem borrowing_zeuge :
    borrowed.read owner first.2 = none ∧ borrowed.read borrower first.2 = some true ∧
    borrowed.release owner first.2 = none ∧ borrowed.release borrower first.2 = none ∧
    borrowed.reset owner = none ∧ borrowed.reset borrower = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem loan_return_zeuge : borrowed.endLoan borrower first.2 = some first.1 :=
  Heap.lend_endLoan (by rfl : first.1.lend owner borrower first.2 = some borrowed)

def moved : Heap Region Bool × Ref Region :=
  (first.1.move owner borrower first.2).get (by decide)

theorem moving_zeuge :
    moved.1.read owner first.2 = none ∧ moved.1.read borrower first.2 = none ∧
    moved.1.read borrower moved.2 = some true ∧ moved.1.reset owner = none ∧
    first.1.move owner anotherThread first.2 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def resetHeap : Heap Region Bool := (first.1.reset owner).get (by decide)
def afterReset : Heap Region Bool × Ref Region :=
  (resetHeap.allocate .unbounded true owner false).get (by decide)

theorem reset_zeuge :
    resetHeap.extent = 0 ∧ resetHeap.rights.next = first.1.rights.next ∧
    afterReset.1.read owner first.2 = none ∧ afterReset.1.read owner afterReset.2 = some false := by
  decide

theorem bounded_unchanged_zeuge :
    first.1.allocate (.bounded 1) true owner false = none ∧
    (released.allocate (.bounded 1) true owner false).isSome = true := by exact ⟨rfl, rfl⟩

/-- This is a theorem about arbitrary finite growth, not a giant allocation test. -/
theorem beyond_u32_zeuge :
    ∃ H : Heap Region Bool, Allocations owner true (4294967295 + 1) H ∧
      4294967295 < H.extent ∧ ∀ i : Nat, i ≤ 4294967295 → H.payload (i : Int) = some true :=
  no_static_memory_bound owner true 4294967295

theorem mixed_execution_zeuge : Reachable .unbounded reused.1 ∧ reused.1.Valid .unbounded := by
  have hfirst : Reachable .unbounded first.1 := .next .empty (.allocate first_allocation)
  have hreleased : Reachable .unbounded released := .next hfirst (.release release_first)
  have hreused : Reachable .unbounded reused.1 := .next hreleased (.allocate reuse_allocation)
  exact ⟨hreused, hreused.valid⟩

theorem finite_batch_oom_zeuge :
    allocateList .unbounded (fun _ => false) owner 0 empty [] [true, false] =
      .outOfMemory empty [] := rfl

/-! Actual G: a non-empty stored byte, starting from an empty four-slot arena. -/

open InvDynZeuge

def gWorld : World FD := wd 0 4 4 nx0 rn0 rn0

theorem gFree : FA.FreiOk gWorld := by
  refine ⟨[], ?_, .nil, by simp⟩
  change FA.Kette gWorld 4 []
  exact .nil

def byte : Wert FD (FD.typ FA.tab FA.feld) := ⟨7, by decide, by decide⟩
def gHeap : Heap Region (Wert FD (FD.typ FA.tab FA.feld)) := .empty

theorem gRepresented : PayloadRepresented (A := FA) gHeap gWorld := by
  refine ⟨⟨⟨ArenaOwnership.State.empty_valid, ?_⟩, rfl, by decide⟩, ?_⟩
  · intro i
    constructor
    · intro hl
      have hh : FA.stand gWorld = 0 := rfl
      have := hl.1
      have := hl.2.1
      omega
    · rintro ⟨c, hc⟩; cases hc
  · intro i value hp; cases hp

theorem g_payload_execution_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    ∃ H' reference σ',
      gHeap.allocate .unbounded true owner byte = some (H', reference) ∧
      execBlock O passes R
        (Block.arenaAlloc (V := FV) (l := false) FA.toArenaForm
          (.var .here) rfl fdarf rfl (fgdarf _)
          (.ret .empty (List.Perm.refl [])) (.nil)) gWorld (.cons byte .nil) = .ok σ' (.cons byte .nil) ∧
      PayloadRepresented (A := FA) H' σ' ∧ H'.rights.owns owner reference.handle ∧ FA.FreiOk σ' :=
  fresh_payload_execution O passes R (V := FV) (l := false) (Λ := []) FA gHeap owner .here rfl fdarf rfl (fgdarf _)
    (.ret .empty (List.Perm.refl [])) gWorld (.cons byte .nil)
    (Heap.empty_valid _) gRepresented gFree rfl (by decide)

/-- Refusal under an ordinary G Boolean goes to an ordinary terminating return. -/
theorem g_refusal_zeuge (O : Orakel FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) :
    execBlock O passes R
      (Block.allocationAttempt (V := FV) (l := false) (Λ' := []) (.fls)
        (.ret .empty (List.Perm.refl [])) (.nil)) gWorld (.nil) = .zurueck gWorld () := by
  rfl

end Gabbro.Grammatik.ArenaStorage.Witnesses
