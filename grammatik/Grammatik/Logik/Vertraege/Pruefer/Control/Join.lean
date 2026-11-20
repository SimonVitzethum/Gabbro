/-
  Subject: Joining the continuation of a branch (the contract checker's join mode).

  The WP compiler compiles the continuation of a statement once per branch; nested branches multiply that work.
  `Continuation.joined` compiles the continuation ONCE over a fresh environment (a fresh immutable observation for
  every integer local, an unobserved value for every other local) and quantifies the fresh observations
  universally; each branch then uses the same certificate. It is sound because the shared certificate holds for every
  value of the locals; it is coarser than the per-branch continuation (the branch's local values are forgotten), so
  the checker uses it only when the per-branch work estimate exceeds the budget (`VCBudget.join`).
-/
module

public import Grammatik.Logik.Vertraege.Pruefer.Control.Havoc

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Symbolic

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.Elim.Korrekt Invarianten.Frag.Symbolic
open Invarianten.Modell

variable {D : Deklaration} {V : Vertrag D} {program : Programm D} {S : SperrInv D}

/-- A fresh observation for an integer local, an unobserved value for every other local. -/
def freshValue (start : Nat) : (τ : Ty) → SymValue D Nat τ × Nat
  | .int _ _ => (.integer (.var start), start + 1)
  | _ => (.unobserved, start)

theorem freshValue_le (start : Nat) (τ : Ty) : start ≤ (freshValue (D := D) start τ).2 := by
  cases τ
  case int lo hi => exact Nat.le_succ start
  all_goals exact Nat.le_refl start

theorem freshValue_bounded (start : Nat) (τ : Ty) :
    (freshValue (D := D) start τ).1.Bounded (freshValue (D := D) start τ).2 := by
  cases τ
  case int lo hi =>
    intro key member
    have same := List.mem_singleton.mp member
    subst key
    exact Nat.lt_succ_self start
  all_goals trivial

theorem freshValue_realizes (start : Nat) (τ : Ty) (valuation : Assignment Nat) (world : World D)
    (actual : Wert D τ) : ∃ other : Assignment Nat,
      (∀ key, key < start ∨ (freshValue (D := D) start τ).2 ≤ key → other key = valuation key) ∧
      (freshValue (D := D) start τ).1.Realizes other world actual := by
  cases τ
  case int lo hi =>
    refine ⟨valuation.bind start actual.n, fun key outside => ?_, bind_same valuation start actual.n⟩
    have different : key ≠ start := by
      change key < start ∨ start + 1 ≤ key at outside
      omega
    simp only [Assignment.bind, different, ↓reduceIte]
  all_goals exact ⟨valuation, fun _ _ => rfl, trivial⟩

/-- Fresh symbols for a whole environment, from `start` on; the second component is the next free key. -/
def freshEnv : (Γ : Ctx) → Nat → SymEnv D Nat Γ × Nat
  | [], start => (.nil, start)
  | τ :: Γ, start =>
      let head := freshValue (D := D) start τ
      let rest := freshEnv Γ head.2
      (.cons head.1 rest.1, rest.2)

theorem freshEnv_le : (Γ : Ctx) → (start : Nat) → start ≤ (freshEnv (D := D) Γ start).2
  | [], start => Nat.le_refl start
  | τ :: Γ, start => Nat.le_trans (freshValue_le (D := D) start τ) (freshEnv_le Γ _)

theorem freshEnv_bounded : (Γ : Ctx) → (start : Nat) →
    (freshEnv (D := D) Γ start).1.Bounded (freshEnv (D := D) Γ start).2
  | [], _ => trivial
  | τ :: Γ, start =>
      ⟨(freshValue (D := D) start τ).1.bounded_mono (freshValue_bounded start τ) (freshEnv_le Γ _),
        freshEnv_bounded Γ _⟩

theorem freshEnv_realizes : (Γ : Ctx) → (start : Nat) → (valuation : Assignment Nat) → (world : World D) →
    (actual : Env D Γ) → ∃ other : Assignment Nat,
      (∀ key, key < start ∨ (freshEnv (D := D) Γ start).2 ≤ key → other key = valuation key) ∧
      (freshEnv (D := D) Γ start).1.Realizes other world actual
  | [], _, valuation, _, actual => by cases actual; exact ⟨valuation, fun _ _ => rfl, trivial⟩
  | τ :: Γ, start, valuation, world, actual => by
      cases actual with
      | cons value rest =>
          obtain ⟨first, firstAgree, firstRealized⟩ := freshValue_realizes (D := D) start τ valuation world value
          obtain ⟨other, otherAgree, restRealized⟩ := freshEnv_realizes Γ (freshValue (D := D) start τ).2 first world rest
          have middle := freshValue_le (D := D) start τ
          have upper := freshEnv_le (D := D) Γ (freshValue (D := D) start τ).2
          refine ⟨other, fun key outside => ?_, ?_, restRealized⟩
          · change key < start ∨ (freshEnv (D := D) Γ (freshValue (D := D) start τ).2).2 ≤ key at outside
            rw [otherAgree key (by omega), firstAgree key (by omega)]
          · exact ((freshValue (D := D) start τ).1.realizes_congr _ (freshValue_bounded start τ) first other
              (fun key before => (otherAgree key (Or.inl before)).symm) world world value).mp firstRealized

/-- The fresh keys `start, …, stop - 1` as observation keys. -/
def freshNames (start stop : Nat) : List (Key D Nat) :=
  (List.range (stop - start)).map (fun index => .inr (start + index))

theorem mem_freshNames {start stop key : Nat} (inside : start ≤ key ∧ key < stop) :
    (.inr key : Key D Nat) ∈ freshNames start stop :=
  List.mem_map.mpr ⟨key - start, List.mem_range.mpr (by omega), by congr 1; omega⟩

/-- **The joined continuation**: compiled once over a fresh environment, every fresh observation quantified. -/
def Continuation.joined {context : Context A next}
    (tail : Continuation (program := program) (S := S) context Γ) :
    Continuation (program := program) (S := S) context Γ :=
  let fresh := freshEnv (D := D) Γ next
  let shared := tail.encode fresh.2 (freshEnv_le Γ next) fresh.1 (freshEnv_bounded Γ next)
  { holds := tail.holds
    encode := fun _ _ _ _ => do
      let certificate ← shared
      return {
        formula := universalClosure (freshNames next fresh.2) certificate.formula
        sound := fun valuation item present runtime world valid actual _ => by
          obtain ⟨other, agree, realized⟩ := freshEnv_realizes (D := D) Γ next valuation world actual
          have present' : context.holds other item :=
            (context.stable valuation other item (fun key before => (agree key (Or.inl before)).symm)).mp present
          have body : certificate.formula.denote (values other world) :=
            closure_transfer _ certificate.formula (values valuation world) (values other world) valid
              (fun key _ absent => by
                cases key with
                | inl memory => rfl
                | inr index =>
                    show valuation index = other index
                    by_cases inside : next ≤ index ∧ index < fresh.2
                    · exact absurd (mem_freshNames inside) absent
                    · have outside : ¬ (next ≤ index ∧ index < (freshEnv (D := D) Γ next).2) := inside
                      exact (agree index (by omega)).symm)
          exact certificate.sound other item present' runtime world body actual realized } }

/-- The goals of a branching statement: with the joined normal continuation in join mode. -/
def Goals.joinIf {context : Context A next} (join : Bool)
    (goals : Goals (program := program) (S := S) context V Γ) : Goals (program := program) (S := S) context V Γ :=
  if join then { goals with normal := goals.normal.joined } else goals

@[simp] theorem Goals.joinIf_holds {context : Context A next} {l : Bool} (join : Bool)
    (goals : Goals (program := program) (S := S) context V Γ) (item : A)
    (runtime : VC.Runtime program (fun _ => []) S) (allowed : Logik D → Prop) :
    (goals.joinIf join).holds (l := l) item runtime allowed = goals.holds item runtime allowed := by
  unfold Goals.joinIf
  split <;> rfl

end Gabbro.Grammatik.Vertraege.Pruefer.Symbolic
