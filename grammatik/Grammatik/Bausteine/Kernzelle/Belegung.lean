module

public import Grammatik.Bausteine.Kernzelle.Operator
public import Grammatik.Kern.Syntax.Syntax.Teil1
public import Grammatik.Kern.Syntax.Syntax.Teil1b
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe.Teil1

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik

/-! ## 1. The descriptor -/

/-- **An accumulator declaration**: the elaborated form of one
    `accumulates name : T merge op per cpu N` item (SYNTAX.md §11.4,
    `SItemTief.accT`).

    `kernZahl` is the positive constant core count `N`; `breite` the
    preserved storage width `w`; `vorzeichen` the signedness; `[lo, hi]` the
    mathematical range; `op` the closed merge operator. The generated code
    owns `N` distinct private global cells and one exclusive lock per cell;
    `kernAbfrage` is the core-query binding, `aktualisiere` the generated
    update function and `falte` the generated reduction function. No new G
    execution constructor is needed: updates and reads lower to ordinary
    bind/call, dispatch, arithmetic, global stores and locks. -/
structure AccumulatorDecl (D : Deklaration) where
  name : String
  kernZahl : Nat
  breite : Nat
  vorzeichen : Bool
  lo : _root_.Int
  hi : _root_.Int
  op : AccOperator
  zellen : Fin kernZahl → D.Glob
  sperren : Fin kernZahl → D.Lock
  kernAbfrage : D.Fn
  aktualisiere : D.Fn
  falte : D.Fn

/-- The storage width fits the signedness and the range: signed cells live
    in the two's complement range, unsigned cells below `2 ^ w`. -/
def akkuBreitePasst (vorzeichen : Bool) (lo hi : Int) (w : Nat) : Prop :=
  if vorzeichen then -(2 ^ (w - 1) : Int) ≤ lo ∧ hi < 2 ^ (w - 1)
  else 0 ≤ lo ∧ hi < 2 ^ w

/-- **Descriptor validity**: a positive core count, a positive width, a
    valid schema whose neutral inhabits the range, a fitting width, cells of
    the accumulator's value type, and pairwise distinct cells and locks. -/
def akkuOk (D : Deklaration) (a : AccumulatorDecl D) : Prop :=
  1 ≤ a.kernZahl ∧ 1 ≤ a.breite ∧ akkuGueltig a.op a.lo a.hi a.breite ∧
    akkuBreitePasst a.vorzeichen a.lo a.hi a.breite ∧
    (∀ i, D.gtyp (a.zellen i) = Ty.int a.lo a.hi) ∧
    Function.Injective a.zellen ∧ Function.Injective a.sperren

/-- The neutral element inhabits the declaration's range. -/
theorem akkuNeutralBewohnt {D : Deklaration} {a : AccumulatorDecl D}
    (h : akkuOk D a) : a.lo ≤ neutralInt a.op a.lo a.hi a.breite ∧
      neutralInt a.op a.lo a.hi a.breite ≤ a.hi :=
  neutralBewohnt h.2.2.1

/-- The cells are pairwise distinct. -/
theorem akkuZellenGetrennt {D : Deklaration} {a : AccumulatorDecl D}
    (h : akkuOk D a) {i j : Fin a.kernZahl} (hij : a.zellen i = a.zellen j) : i = j :=
  h.2.2.2.2.2.1 hij

/-! ## 2. The idle-root map -/

/-- An accumulator declaration over the program with the runtime's idle
    root: cells and locks are the declaration's (the root adds no carrier),
    functions ride `some`. -/
def AccumulatorDecl.mitRuhe {D : Deklaration} (a : AccumulatorDecl D) :
    AccumulatorDecl D.mitRuhe where
  name := a.name
  kernZahl := a.kernZahl
  breite := a.breite
  vorzeichen := a.vorzeichen
  lo := a.lo
  hi := a.hi
  op := a.op
  zellen := fun i => a.zellen i
  sperren := fun i => a.sperren i
  kernAbfrage := some a.kernAbfrage
  aktualisiere := some a.aktualisiere
  falte := some a.falte

@[simp] theorem mitRuhe_kernZahl {D : Deklaration} (a : AccumulatorDecl D) :
    (AccumulatorDecl.mitRuhe a).kernZahl = a.kernZahl := rfl

@[simp] theorem mitRuhe_zellen {D : Deklaration} (a : AccumulatorDecl D) :
    (AccumulatorDecl.mitRuhe a).zellen = a.zellen := rfl

@[simp] theorem mitRuhe_sperren {D : Deklaration} (a : AccumulatorDecl D) :
    (AccumulatorDecl.mitRuhe a).sperren = a.sperren := rfl

#print axioms Gabbro.Grammatik.Kernzelle.akkuNeutralBewohnt
#print axioms Gabbro.Grammatik.Kernzelle.akkuZellenGetrennt

end Gabbro.Grammatik.Kernzelle
