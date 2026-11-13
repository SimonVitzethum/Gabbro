module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section
namespace Gabbro.Grammatik.Parser

/- Computable equality for validating shared head caches. The parser's shape Booleans
    remain unchanged; these decisions carry their own equality proofs. -/
set_option maxRecDepth 100000

mutual
def SExpr.decEq (a b : SExpr) : Decidable (a = b) := by
  cases a <;> cases b <;> try (refine isFalse ?_; intro h; cases h; done)
  case lit.lit a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case float.float a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case tru.tru =>
    exact isTrue rfl
  case fls.fls =>
    exact isTrue rfl
  case «variable».«variable» a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case field.field a0 a1 b0 b1 =>
    letI := SExpr.decEq a0 b0
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case index.index a0 a1 b0 b1 =>
    letI := SExpr.decEq a0 b0
    letI := SExpr.decEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case arrow.arrow a0 a1 b0 b1 =>
    letI := SExpr.decEq a0 b0
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case un.un a0 a1 b0 b1 =>
    letI := SExpr.decEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case bin.bin a0 a1 a2 b0 b1 b2 =>
    letI := SExpr.decEq a1 b1
    letI := SExpr.decEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
  case call.call a0 a1 b0 b1 =>
    letI := SExpr.decList a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case fnref.fnref a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case built.built a0 a1 b0 b1 =>
    letI := SExpr.decList a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case old.old a0 b0 =>
    letI := SExpr.decEq a0 b0
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case res.res =>
    exact isTrue rfl
  case why.why a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case ext.ext a0 a1 a2 b0 b1 b2 =>
    letI := SExpr.decList a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
termination_by structural a

def SExpr.decList : (a b : List SExpr) → Decidable (a = b)
  | [], [] => isTrue rfl
  | a :: as, b :: bs => by
    letI := SExpr.decEq a b
    letI := SExpr.decList as bs
    exact decidable_of_iff (a = b ∧ as = bs) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
termination_by structural a _ => a
end

instance : DecidableEq SExpr := SExpr.decEq

mutual
def STyp.decEq (a b : STyp) : Decidable (a = b) := by
  cases a <;> cases b <;> try (refine isFalse ?_; intro h; cases h; done)
  case atom.atom a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case path.path a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case ptr.ptr a0 a1 a2 b0 b1 b2 =>
    letI := STyp.decEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
  case index.index a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case range.range a0 a1 a2 a3 b0 b1 b2 b3 =>
    letI := STyp.decEq a0 b0
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
  case array.array a0 a1 b0 b1 =>
    letI := STyp.decEq a0 b0
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case wrap.wrap a0 b0 =>
    letI := STyp.decEq a0 b0
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case embed.embed a0 a1 a2 b0 b1 b2 =>
    letI := STyp.decEq a0 b0
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
  case raw.raw a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case str.str a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; exact rfl)
  case entry.entry a0 a1 b0 b1 =>
    letI := STyp.decOption a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
  case dyn.dyn a0 a1 b0 b1 =>
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)
termination_by structural a

def STyp.decOption : (a b : Option STyp) → Decidable (a = b)
  | none, none => isTrue rfl
  | some a, some b => by
    letI := STyp.decEq a b
    exact decidable_of_iff (a = b) (by
      constructor
      · rintro rfl; rfl
      · intro h; cases h; rfl)
  | none, some _ | some _, none => isFalse (by intro h; cases h)
termination_by structural a _ => a
end

instance : DecidableEq STyp := STyp.decEq

deriving instance DecidableEq for SEffekt
deriving instance DecidableEq for SKlausel

end Gabbro.Grammatik.Parser
