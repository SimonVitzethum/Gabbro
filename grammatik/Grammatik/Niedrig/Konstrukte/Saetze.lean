module

public import Grammatik.Niedrig.Konstrukte.Kontext
public import Grammatik.Niedrig.Konstrukte.Schnitt

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

variable {D : Deklaration}

/-! These uniqueness lemmas use the actual step functions. They make no
    determinism claim about an unconstrained environment oracle across runs. -/

theorem addrLitStep_deterministic {space : Space D} {value : Int}
    {fits : AddrRange space.width value} {world : World D}
    {first second : ValueStep D (Address space)}
    (left : addrLitStep space value fits world = first)
    (right : addrLitStep space value fits world = second) : first = second := left.symm.trans right

theorem addrOffStep_deterministic {space : Space D} {base : Address space} {delta : Int}
    {fits : AddrOffOk base delta} {world : World D}
    {first second : ValueStep D (Address space)}
    (left : addrOffStep base delta fits world = first)
    (right : addrOffStep base delta fits world = second) : first = second := left.symm.trans right

theorem narrowAddrStep_deterministic {space : Space D} {base : Address space} {width : Nat}
    {fits : NarrowAddrOk base width} {world : World D}
    {first second : ValueStep D (Address { space with width := width, positiveWidth := fits.1 })}
    (left : narrowAddrStep base width fits world = first)
    (right : narrowAddrStep base width fits world = second) : first = second := left.symm.trans right

theorem viewGetStep_deterministic {view : View D} {layout : AdressLayout D}
    {field : D.Feld view.span.table} {byteField : D.typ view.span.table field = .int 0 255}
    {index : Int} {length : Nat} {resources : List (Res D)}
    {checked : ViewGetOk view layout field index length resources} {world : World D}
    {first second : ValueStep D (Zahl 0 (256 ^ length - 1))}
    (left : viewGetStep view layout field byteField index length resources checked world = first)
    (right : viewGetStep view layout field byteField index length resources checked world = second) :
    first = second := left.symm.trans right

theorem viewPutStep_deterministic {view : View D} {layout : AdressLayout D}
    {field : D.Feld view.span.table} {index : Int} {value : Wert D (D.typ view.span.table field)}
    {resources : List (Res D)} {writes : D.Tab → Bool}
    {checked : ViewPutOk view layout field index resources writes} {world first second : World D}
    (left : viewPutStep view layout field index value resources writes checked world = first)
    (right : viewPutStep view layout field index value resources writes checked world = second) :
    first = second := left.symm.trans right

theorem bindViewStep_deterministic {P I : Type} {space : Space D}
    {a : Authority D} {c : Context D P I} {start : Address space} {length : Nat}
    {rights : DataRights} {borrower : ArenaOwnership.Frame} {world : World D}
    {first second : Except ViewFailure (ViewResult a c) × World D}
    (left : bindViewStep a c start length rights borrower world = first)
    (right : bindViewStep a c start length rights borrower world = second) :
    first = second := left.symm.trans right

theorem returnViewStep_deterministic {P I : Type} {a : Authority D} {c : Context D P I}
    {world : World D} {first second : Except ViewFailure (Context D P I) × World D}
    (left : returnViewStep a c world = first) (right : returnViewStep a c world = second) :
    first = second := left.symm.trans right

theorem arrSliceStep_deterministic {τ : Ty} {length : Nat} {value : Wert D (.arr τ length)}
    {first last : Nat} {bounds : SliceOk length first last} {world : World D}
    {left right : ValueStep D (Wert D (.arr τ (last - first)))}
    (hleft : arrSliceStep value first last bounds world = left)
    (hright : arrSliceStep value first last bounds world = right) : left = right := hleft.symm.trans hright

theorem strSliceStep_deterministic {maximum : Nat} {value : Wert D (.str maximum)}
    {first last : Nat} {bounds : SliceOk value.1.length first last} {world : World D}
    {left right : ValueStep D (Wert D (.str (last - first)))}
    (hleft : strSliceStep value first last bounds world = left)
    (hright : strSliceStep value first last bounds world = right) : left = right := hleft.symm.trans hright

theorem bindCtxStep_deterministic {Γ : Ctx} {resources : List (Res D)}
    {oracle : Orakel D} {item : D.Ax} {mark : D.Marke} {stage : Nat}
    {args : Args D Γ resources (D.aparams item)} {env : Env D Γ}
    {before after : OwnerBindings D.Marke} {source into : Nat}
    {checked : BindCtxOk item mark stage before after source into} {world : World D}
    {first second : Option (OwnerBindings D.Marke × World D ×
      Option (ErgVal D (D.aerg item) ⊕ Fin (D.agruende item)))}
    (left : bindCtxStep oracle item mark stage args env before after source into checked world = first)
    (right : bindCtxStep oracle item mark stage args env before after source into checked world = second) :
    first = second := left.symm.trans right

/-- Reading bytes depends only on the named table, with no dependence on
    other carriers, globals, traces, held locks or owner metadata. -/
theorem bytesAb_local {first second : World D} (table : D.Tab) (field : D.Feld table)
    (byteField : D.typ table field = .int 0 255)
    (same : ∀ index, first.slots table index field = second.slots table index field)
    (length : Nat) (index : Int) :
    first.bytesAb table field byteField length index = second.bytesAb table field byteField length index := by
  induction length generalizing index with
  | zero => rfl
  | succ length ih =>
    simp only [World.bytesAb, same index, ih (index + 1)]

theorem viewGetStep_local {view : View D} {layout : AdressLayout D}
    {field : D.Feld view.span.table} {byteField : D.typ view.span.table field = .int 0 255}
    {index : Int} {length : Nat} {resources : List (Res D)}
    (checked : ViewGetOk view layout field index length resources) (first second : World D)
    (same : ∀ offset, first.slots view.span.table offset field = second.slots view.span.table offset field) :
    (viewGetStep view layout field byteField index length resources checked first).value =
      (viewGetStep view layout field byteField index length resources checked second).value := by
  apply zahl_ext
  change bytesZuZahl (first.bytesAb view.span.table field byteField length index) =
    bytesZuZahl (second.bytesAb view.span.table field byteField length index)
  rw [bytesAb_local view.span.table field byteField same length index]

/-- Definitional correspondence to the current G evaluator, not another byte
    projection. This witness is generic in the index expression and environment. -/
theorem viewGetStep_eval_getBytes {Γ : Ctx} {resources : List (Res D)} {lo hi : Int}
    (view : View D) (layout : AdressLayout D) (field : D.Feld view.span.table)
    (byteField : D.typ view.span.table field = .int 0 255) (length : Nat)
    (index : Expr D Γ resources (.int lo hi)) (low : 0 ≤ lo) (high : hi + length ≤ D.count view.span.table)
    (allowed : darf D view.span.table resources) (world : World D) (env : Env D Γ)
    (checked : ViewGetOk view layout field (eval world index world env).n length resources) :
    (viewGetStep view layout field byteField (eval world index world env).n length resources checked world).value =
      eval world (.getBytes view.span.table field byteField length index low high allowed) world env := rfl

/-- Exact cost analogues for the eventual address constructors. -/
theorem literalCost_eq {Γ : Ctx} {resources : List (Res D)} (value : Int) :
    literalCost = kostenExpr (.lit value : Expr D Γ resources (.int value value)) := rfl

theorem unaryCost_eq_widen {Γ : Ctx} {resources : List (Res D)} {lo hi wideLo wideHi : Int}
    (low : wideLo ≤ lo) (high : hi ≤ wideHi) (value : Expr D Γ resources (.int lo hi)) :
    unaryCost (kostenExpr value) = kostenExpr (.widen low high value) := rfl

theorem unaryCost_eq_add_literal {Γ : Ctx} {resources : List (Res D)} {lo hi : Int}
    (value : Expr D Γ resources (.int lo hi)) (delta : Int) :
    unaryCost (kostenExpr value) = kostenExpr (.add value (.lit delta)) := by
  simp only [unaryCost, kostenExpr, Nat.add_zero]

theorem viewGetCost_bound (index : Nat) : 1 ≤ viewGetCost index := by
  unfold viewGetCost unaryCost
  omega

end Gabbro.Grammatik.LowLevel.Construct
