module

public import Grammatik.Logik.Invarianten.VC.Fresh
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Finite domains of decoded local values. A local observation the VC cannot name as one linear term is eliminated by
case analysis over EVERY value of its decoded type: the list is complete by proof, never an author-supplied sample,
and it is refused when it exceeds the budget. Integers, Booleans, reasons and capabilities were the first types;
options over an index range, closed tagged types with finite payloads, products of finite fields and the empty type
follow by the same completeness argument, so a local of such a type no longer forces a refusal.
-/

namespace Gabbro.Grammatik.Invarianten.VC

variable {D : Deklaration}

/-- Finite elimination of a fresh local observation. The range is the actual
    decoded type, including both endpoints, never an author-supplied sample. -/
structure LocalDomain (D : Deklaration) (τ : Ty) where
  values : List (Wert D τ)
  complete : ∀ value : Wert D τ, value ∈ values

/-- Every payload value of one case of a tagged type. -/
structure PayloadDomain (D : Deklaration) (c : Option Ty) where
  values : List (Nutzlast D.Fn D.passt c)
  complete : ∀ value : Nutzlast D.Fn D.passt c, value ∈ values

/-- Every value of a tagged type over the case list `cs`. -/
structure SumDomain (D : Deklaration) (cs : List (Option Ty)) where
  values : List (Wert D (.sum cs))
  complete : ∀ value : Wert D (.sum cs), value ∈ values

/-- Every value of a product over the field list `fs`. -/
structure ProdDomain (D : Deklaration) (fs : List Ty) where
  values : List (ProdVal D.Fn D.passt fs)
  complete : ∀ value : ProdVal D.Fn D.passt fs, value ∈ values

def integerValues (lo hi : Int) (remaining : Nat) : List (Zahl lo hi) :=
  (List.range remaining).filterMap fun (offset : Nat) =>
    if h : lo ≤ lo + (offset : Int) ∧ lo + (offset : Int) ≤ hi then
      some ⟨lo + (offset : Int), h.1, h.2⟩
    else none

theorem integerValues_complete (lo hi : Int) (value : Zahl lo hi) :
    value ∈ integerValues lo hi (hi - lo + 1).toNat := by
  have lower := value.lo_le
  have upper := value.le_hi
  have nonnegative : 0 ≤ value.n - lo := by omega
  have offset : ((value.n - lo).toNat : Int) = value.n - lo := Int.toNat_of_nonneg nonnegative
  have inside : (value.n - lo).toNat < (hi - lo + 1).toNat := by omega
  apply List.mem_filterMap.mpr
  refine ⟨(value.n - lo).toNat, List.mem_range.mpr inside, ?_⟩
  have same : lo + ((value.n - lo).toNat : Int) = value.n := by omega
  simpa only [same, lower, upper, and_self, ↓reduceDIte]

/-- The values of `option index` over `0 ..< n`: absent, then every index. -/
def optionValues (n : Int) : List (Option (Zahl 0 (n - 1))) :=
  none :: (integerValues 0 (n - 1) (n - 1 - 0 + 1).toNat).map some

theorem optionValues_complete (n : Int) (value : Option (Zahl 0 (n - 1))) :
    value ∈ optionValues n := by
  cases value with
  | none => exact List.mem_cons_self
  | some index =>
      exact List.mem_cons_of_mem _ (List.mem_map_of_mem (integerValues_complete 0 (n - 1) index))

/-- Move a value of the tail case list one case up: same payload, next tag. -/
def sumShift {c : Option Ty} {cs : List (Option Ty)} (value : Wert D (.sum cs)) : Wert D (.sum (c :: cs)) :=
  ⟨value.1.succ, value.2⟩

/-- A value of the first case. -/
def sumFirst {c : Option Ty} {cs : List (Option Ty)} (payload : Nutzlast D.Fn D.passt c) :
    Wert D (.sum (c :: cs)) :=
  ⟨⟨0, Nat.succ_pos _⟩, payload⟩

theorem sum_complete {c : Option Ty} {cs : List (Option Ty)}
    (head : List (Nutzlast D.Fn D.passt c)) (headComplete : ∀ value, value ∈ head)
    (tail : List (Wert D (.sum cs))) (tailComplete : ∀ value, value ∈ tail) :
    ∀ value : Wert D (.sum (c :: cs)), value ∈ head.map sumFirst ++ tail.map sumShift := by
  intro value
  match value with
  | ⟨⟨0, _⟩, payload⟩ =>
      exact List.mem_append_left _ (List.mem_map_of_mem (f := sumFirst (cs := cs)) (headComplete payload))
  | ⟨⟨i + 1, bound⟩, payload⟩ =>
      exact List.mem_append_right _
        (List.mem_map_of_mem (f := sumShift (c := c))
          (tailComplete ⟨⟨i, Nat.lt_of_succ_lt_succ bound⟩, payload⟩))

theorem prod_complete {τ : Ty} {τs : List Ty}
    (head : List (Wert D τ)) (headComplete : ∀ value, value ∈ head)
    (tail : List (ProdVal D.Fn D.passt τs)) (tailComplete : ∀ value, value ∈ tail) :
    ∀ value : ProdVal D.Fn D.passt (τ :: τs),
      value ∈ head.flatMap (fun first => tail.map (fun rest => ((first, rest) : ProdVal D.Fn D.passt (τ :: τs)))) := by
  intro value
  obtain ⟨first, rest⟩ := value
  exact List.mem_flatMap.mpr ⟨first, headComplete first, List.mem_map_of_mem (tailComplete rest)⟩

mutual
/-- The complete finite domain of a decoded type, or a refusal when it is infinite or exceeds the budget. -/
def finiteDomain (budget : Nat) : (τ : Ty) → Except Frag.Refusal (LocalDomain D τ)
  | .int lo hi =>
      if (hi - lo + 1).toNat ≤ budget then
        .ok
          { values := integerValues lo hi (hi - lo + 1).toNat
            complete := integerValues_complete lo hi }
      else .error (.unsupported "local observation type range exceeds the VC budget")
  | .bool =>
      if 2 ≤ budget then
        .ok
          { values := (([false, true] : List Bool) : List (Wert D .bool))
            complete := by
              show ∀ value : Bool, value ∈ ([false, true] : List Bool)
              decide }
      else .error (.unsupported "Boolean local observation exceeds the VC budget")
  | .why count =>
      if count ≤ budget then
        .ok { values := List.finRange count, complete := List.mem_finRange }
      else .error (.outsideFragment "finite oracle reason choices exceed the VC budget")
  | .ptr capability =>
      -- G carries pointer authority in the type; its decoded value is Unit.
      if 1 ≤ budget then
        .ok
          { values := [show Wert D (.ptr capability) from ()]
            complete := fun value => by cases value; exact List.mem_cons_self }
      else .error (.unsupported "pointer capability exceeds the VC budget")
  | .opt n =>
      if (n - 1 - 0 + 1).toNat + 1 ≤ budget then
        .ok { values := optionValues n, complete := optionValues_complete n }
      else .error (.unsupported "option local observation exceeds the VC budget")
  | .never => .ok { values := [], complete := fun value => nomatch value }
  | .sum cs => do
      let domain ← sumDomain budget cs
      return { values := domain.values, complete := domain.complete }
  | .prod _ fs => do
      let domain ← prodDomain budget fs
      return { values := domain.values, complete := domain.complete }
  | _ => .error (.unsupported "local observation needs a finite decoded type")

def payloadDomain (budget : Nat) : (c : Option Ty) → Except Frag.Refusal (PayloadDomain D c)
  | none => .ok { values := [()], complete := fun value => by cases value; exact List.mem_cons_self }
  | some τ => do
      let domain ← finiteDomain budget τ
      return { values := domain.values, complete := domain.complete }

def sumDomain (budget : Nat) : (cs : List (Option Ty)) → Except Frag.Refusal (SumDomain D cs)
  | [] => .ok { values := [], complete := fun value => value.1.elim0 }
  | c :: cs => do
      let head ← payloadDomain budget c
      let tail ← sumDomain budget cs
      if head.values.length + tail.values.length ≤ budget then
        return { values := head.values.map sumFirst ++ tail.values.map sumShift
                 complete := sum_complete head.values head.complete tail.values tail.complete }
      else .error (.unsupported "tagged local observation exceeds the VC budget")

def prodDomain (budget : Nat) : (fs : List Ty) → Except Frag.Refusal (ProdDomain D fs)
  | [] => .ok { values := [()], complete := fun value => by cases value; exact List.mem_cons_self }
  | τ :: τs => do
      let head ← finiteDomain budget τ
      let tail ← prodDomain budget τs
      if head.values.length * tail.values.length ≤ budget then
        return { values := head.values.flatMap (fun first => tail.values.map (fun rest => (first, rest)))
                 complete := prod_complete head.values head.complete tail.values tail.complete }
      else .error (.unsupported "record local observation exceeds the VC budget")
end

end Gabbro.Grammatik.Invarianten.VC
