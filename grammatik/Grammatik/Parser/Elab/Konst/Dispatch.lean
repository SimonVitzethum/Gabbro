module

public import Grammatik.Parser.Elab.Konst.Ableitung

@[expose] public section

namespace Gabbro.Grammatik.Parser

mutual
/-- Falling-through source blocks used by const dispatch arms. -/
inductive ConstSourceBlock (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → SAnw → Block c.D V l Γ [] [] → Prop where
  | empty : ConstSourceBlock c locals (.block [] none) .nil
  | option (value : ConstSourceExpr c locals source e)
      (present : ConstSourceBlock c (locals.extend name false (.index n)) yes p)
      (absent : ConstSourceBlock c locals no a)
      (tail : ConstSourceBlock c locals (.block rest ending) body) :
      ConstSourceBlock c locals
        (.block (.cases source [.arm "Some" (some name) yes, .arm "None" none no] :: rest) ending)
        (.cons (.onOption e p a) body)
  | tag (value : ConstSourceExpr c locals source e)
      (arms : ConstSourceTagArms c locals sources branches)
      (tail : ConstSourceBlock c locals (.block rest ending) body) :
      ConstSourceBlock c locals (.block (.cases source sources :: rest) ending)
        (.cons (.onTag e branches) body)
  | reason (value : ConstSourceExpr c locals source e)
      (arms : ConstSourceReasonArms c locals sources branches)
      (tail : ConstSourceBlock c locals (.block rest ending) body) :
      ConstSourceBlock c locals (.block (.cases source sources :: rest) ending)
        (.cons (.onWhy e branches) body)

/-- Positional tags use their canonical numeric index as their source name. -/
inductive ConstSourceTagArms (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → List SAnw → {cs : List (Option (Int × Int))} →
    Arms c.D V l Γ [] [] cs → Prop where
  | empty : ConstSourceTagArms c locals [] .nil
  | plain (body : ConstSourceBlock c locals source block)
      (tail : ConstSourceTagArms c locals sources branches) :
      ConstSourceTagArms c locals (.arm label none source :: sources)
        (cs := none :: cs) (.cons block branches)

inductive ConstSourceReasonArms (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → List SAnw → {n : Nat} →
    GrundArms c.D V l Γ [] [] n → Prop where
  | empty : ConstSourceReasonArms c locals [] .nil
  | cons (body : ConstSourceBlock c locals source block)
      (tail : ConstSourceReasonArms c locals sources branches) :
      ConstSourceReasonArms c locals (.arm label none source :: sources) (.cons block branches)
end

mutual
 theorem ConstSourceBlock.rein (h : ConstSourceBlock c locals source body) :
    ConstBlock c body := by
  cases h with
  | empty => exact .nil
  | option v p a t => exact .cons (.onOption v.rein p.rein a.rein) t.rein
  | tag v a t => exact .cons (.onTag v.rein a.rein) t.rein
  | reason v a t => exact .cons (.onWhy v.rein a.rein) t.rein

 theorem ConstSourceTagArms.rein (h : ConstSourceTagArms c locals sources arms) :
    ConstArms c arms := by
  cases h with
  | empty => exact .nil
  | plain b t => exact .cons b.rein t.rein

 theorem ConstSourceReasonArms.rein (h : ConstSourceReasonArms c locals sources arms) :
    ConstReasonArms c arms := by
  cases h with
  | empty => exact .nil
  | cons b t => exact .cons b.rein t.rein
end

end Gabbro.Grammatik.Parser
