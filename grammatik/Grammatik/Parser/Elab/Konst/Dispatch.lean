module

public import Grammatik.Parser.Elab.Konst.Basis

@[expose] public section

namespace Gabbro.Grammatik.Parser

mutual
/-- Falling-through source blocks used by const dispatch arms. -/
inductive ConstSourceBlock (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → SAnw → Block c.D V l Γ [] [] → Prop where
  | empty {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} : ConstSourceBlock c (V := V) (l := l) locals (.block [] none) .nil
  | option {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} {n : Nat} {e : Expr c.D Γ [] (.opt n)} (value : ConstSourceExpr c locals source e)
      (present : ConstSourceBlock c (V := V) (l := l) (locals.extend name false (.index n)) yes p)
      (absent : ConstSourceBlock c (V := V) (l := l) locals no a)
      (tail : ConstSourceBlock c (V := V) (l := l) locals (.block rest ending) body) :
      ConstSourceBlock c (V := V) (l := l) locals
        (.block (.cases source [.arm "Some" (some name) yes, .arm "None" none no] :: rest) ending)
        (.cons (.onOption e p a) body)
  | tag {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} (value : ConstSourceExpr c locals source e)
      (arms : ConstSourceTagArms c (V := V) (l := l) locals sources branches)
      (tail : ConstSourceBlock c (V := V) (l := l) locals (.block rest ending) body) :
      ConstSourceBlock c (V := V) (l := l) locals (.block (.cases source sources :: rest) ending)
        (.cons (.onTag e branches) body)
  | reason {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} (value : ConstSourceExpr c locals source e)
      (arms : ConstSourceReasonArms c (V := V) (l := l) locals sources branches)
      (tail : ConstSourceBlock c (V := V) (l := l) locals (.block rest ending) body) :
      ConstSourceBlock c (V := V) (l := l) locals (.block (.cases source sources :: rest) ending)
        (.cons (.onWhy e branches) body)

/-- Tag arms preserve canonical order and payload binding contexts. -/
inductive ConstSourceTagArms (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → List SAnw → {cs : List (Option Ty)} →
    Arms c.D V l Γ [] [] cs → Prop where
  | empty {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} : ConstSourceTagArms c (V := V) (l := l) locals [] .nil
  | plain {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} (body : ConstSourceBlock c (V := V) (l := l) locals source block)
      (tail : ConstSourceTagArms c (V := V) (l := l) locals sources branches) :
      ConstSourceTagArms c (V := V) (l := l) locals (.arm label none source :: sources)
        (cs := none :: cs) (.cons block branches)
  | payload {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} (body : ConstSourceBlock c (V := V) (l := l) (locals.extend name false (.int lo hi)) source block)
      (tail : ConstSourceTagArms c (V := V) (l := l) locals sources branches) :
      ConstSourceTagArms c (V := V) (l := l) locals (.arm label (some name) source :: sources)
        (cs := some (.int lo hi) :: cs) (.cons block branches)

inductive ConstSourceReasonArms (c : ConstProgram) : {V : Vertrag c.D} → {l : Bool} →
    {Γ : Ctx} → ConstLocals Γ → List SAnw → {n : Nat} →
    GrundArms c.D V l Γ [] [] n → Prop where
  | empty {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} : ConstSourceReasonArms c (V := V) (l := l) locals [] .nil
  | cons {V : Vertrag c.D} {l : Bool} {Γ : Ctx} {locals : ConstLocals Γ} (body : ConstSourceBlock c (V := V) (l := l) locals source block)
      (tail : ConstSourceReasonArms c (V := V) (l := l) locals sources branches) :
      ConstSourceReasonArms c (V := V) (l := l) locals (.arm label none source :: sources) (.cons block branches)
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
  | payload b t => exact .cons b.rein t.rein

 theorem ConstSourceReasonArms.rein (h : ConstSourceReasonArms c locals sources arms) :
    ConstReasonArms c arms := by
  cases h with
  | empty => exact .nil
  | cons b t => exact .cons b.rein t.rein
end

end Gabbro.Grammatik.Parser
