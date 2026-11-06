module
public import Grammatik.Parser.Elab.Konst.Scalar.Names
public import Grammatik.Logik.Fortschritt.KostenG.T1.Teil1a

@[expose] public section
namespace Gabbro.Grammatik.Parser.Konst.Scalar
open Uebersetze

/-- One declared operation bound, read in the original entry context. The
    existing `kostenExpr` counts the source-derived return payload's operations;
    it is not the compiler's evaluation fuel or G's administrative step count. -/
structure CostBound {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (work : Nat) (args : Env D Γ) (source : SExpr) where
  lower : Int
  upper : Int
  code : Code D Γ (.int lower upper)
  meaning : SourceMeaning names globals source ⟨_, code⟩
  within : (work : Int) ≤ (code.denote args).n

/-- Retain every original `costs` clause, including repeated bounds. Non-cost
    clauses are handled by the existing body, predicate and effect readers. -/
def costSource : SKlausel → Option SExpr
  | .cost source => some source
  | _ => none

def CostBounds {D : Deklaration} {Γ : Ctx} (names : Locals Γ)
    (globals : List (String × Int)) (work : Nat) (args : Env D Γ) : List SKlausel → Type
  | [] => PUnit
  | clause :: rest => match costSource clause with
    | some source => CostBound names globals work args source × CostBounds names globals work args rest
    | none => CostBounds names globals work args rest

/-- Check the actual entry value of each bound without clipping negative bounds
    or substituting compiler fuel. A successful result carries its source meaning. -/
def checkCosts {D : Deklaration} {Γ : Ctx} (name : String) (names : Locals Γ)
    (globals : List (String × Int)) (work : Nat) (args : Env D Γ) :
    (clauses : List SKlausel) → Except String (CostBounds names globals work args clauses)
  | [] => .ok ⟨⟩
  | clause :: rest => match selected : costSource clause with
    | none => by
      simpa only [CostBounds, selected] using checkCosts name names globals work args rest
    | some source => do
      let normalized ← normalize (D := D) names globals source
      match hc : normalized.code with
      | ⟨.int lower upper, code⟩ =>
        if hw : (work : Int) ≤ (code.denote args).n then
          let tail ← checkCosts name names globals work args rest
          have meaning : SourceMeaning names globals source ⟨.int lower upper, code⟩ := by
            exact Eq.mp (congrArg
              (fun typed : SomeCode D Γ => SourceMeaning names globals source typed) hc)
              normalized.meaning
          let bound : CostBound names globals work args source := ⟨lower, upper, code, meaning, hw⟩
          have bounds : CostBounds names globals work args (clause :: rest) := by
            simpa only [CostBounds, selected] using (bound, tail)
          return bounds
        else throw ("const cost bound exceeded at `" ++ name ++ "`")
      | _ => throw ("const cost bound is not an integer at `" ++ name ++ "`")

/-- Every retained annotation denotes a bound on the same operation count at
    every world; the reader's denotation equation supplies the world transport. -/
theorem CostBounds.bound {D : Deklaration} {Γ : Ctx} {names : Locals Γ}
    {globals : List (String × Int)} {work : Nat} {args : Env D Γ}
    {clauses : List SKlausel} :
    CostBounds names globals work args clauses → ∀ source : SExpr,
    SKlausel.cost source ∈ clauses →
    ∃ (lower upper : Int) (code : Code D Γ (.int lower upper)),
      SourceMeaning names globals source ⟨_, code⟩ ∧
      ∀ before after, (work : Int) ≤ (eval before code.expr after args).n := by
  induction clauses with
  | nil => intro bounds source member; cases member
  | cons clause rest ih =>
    intro bounds source member
    cases clause <;> simp only [List.mem_cons] at member
    all_goals first
      | exact ih bounds source (by
          rcases member with wrong | tail
          · cases wrong
          · exact tail)
      | rcases member with same | tail
        · cases same
          exact ⟨bounds.1.lower, bounds.1.upper, bounds.1.code, bounds.1.meaning,
            fun before after => by
              rw [bounds.1.code.equation]
              exact bounds.1.within⟩
        · exact ih bounds.2 source tail

end Gabbro.Grammatik.Parser.Konst.Scalar
