module
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

inductive IndexSyntax {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    {ty : Ty} → Expr D Γ Λ ty → Prop
  | literal (value : Int) : IndexSyntax (.lit value)
  | var {ty : Ty} (v : Var Γ ty) : IndexSyntax (.var v)
  | widen {lo hi lo' hi' : Int} (lower : lo' ≤ lo) (upper : hi ≤ hi')
      (value : Expr D Γ Λ (.int lo hi)) : IndexSyntax value → IndexSyntax (.widen lower upper value)

theorem indexSyntax_scope {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {ty : Ty} {value : Expr D Γ Λ ty} (shape : IndexSyntax value)
    {binderTy : Ty} (binder : Wert D binderTy) (entry state : World D) (env : Env D Γ) :
    eval entry value.weaken state (.cons binder env) = eval entry value state env := by
  induction shape with
  | literal value => rfl
  | var v => rfl
  | widen lower upper value shape ih =>
    change Zahl.weiter lower upper (eval entry value.weaken state (.cons binder env)) =
      Zahl.weiter lower upper (eval entry value state env)
    rw [ih]

theorem indexSyntax_weaken_orte {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {ty : Ty} {value : Expr D Γ Λ ty} (shape : IndexSyntax value) {binderTy : Ty} :
    (let extended : Expr D (binderTy :: Γ) Λ ty := value.weaken; extended.orte = []) := by
  induction shape with
  | literal value => rfl
  | var v => rfl
  | widen lower upper value shape ih => exact ih

/-- Membership values are lexical literals or checked numeric variables. -/
theorem lowMemberValue_syntax (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (shift : Nat) (table : Fin u.tabs.length) (source : UIdx) (value : LowSide u Γ Λ)
    (lowered : lowMemberValue u Γ Λ fn shift table source = .ok value) : IndexSyntax value.term := by
  cases source with
  | lit number => cases lowered; exact .literal _
  | param name =>
    simp only [lowMemberValue, lowParamSide, bind, Except.bind] at lowered
    repeat first | split at lowered | contradiction | (cases lowered; exact .var _)

theorem member_value_scope (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (shift : Nat) (table : Fin u.tabs.length) (source : UIdx) (value : LowSide u Γ Λ)
    (lowered : lowMemberValue u Γ Λ fn shift table source = .ok value)
    {binderTy : Ty} (binder : Wert (declOf u) binderTy)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) :
    eval entry value.term.weaken state (.cons binder env) = eval entry value.term state env :=
  indexSyntax_scope (lowMemberValue_syntax u Γ Λ fn shift table source value lowered) binder entry state env

/-- A newly expanded count has exactly the canonical integer bound, including its sign. -/
theorem count_export (values : List (String × Int)) (op : String) (a b : SExpr) (amount : Int)
    (meaning : uSchranke (values.map (fun pair => (pair.1, (pair.2, pair.2)))) (.bin op a b) = some amount)
    (nonnegative : 0 ≤ amount) : uAnzahl values (.bin op a b) = .ok amount := by
  simp only [uAnzahl, meaning, nonnegative, ↓reduceIte] <;> try rfl

/-- New scalar initializer expressions use the existing checked evaluator at the declared range. -/
theorem initializer_export (values : List (String × Int)) (lo hi : Int) (op : String)
    (a b : SExpr) (value : Int) (meaning : uKonstWert lo hi [] values 64 (.bin op a b) = some value) :
    uInitialNumber values lo hi (.one (.bin op a b)) = .ok value := by
  simp only [uInitialNumber, meaning] <;> try rfl

/-- Source relation export preserves both endpoints' explicit table identity. -/
theorem reach_export (ctx : UCtx) (field : String) (a b : SExpr) (table : String)
    (number : Nat) (origin start stop : UIdx)
    (found : uIndexOrigin ctx a = .ok (table, number, origin))
    (first : uExportIndex ctx table number a = .ok start)
    (last : uExportIndex ctx table number b = .ok stop) :
    uSichert ctx (.ext .reach [field] [a, b]) = .ok (.reach table field start stop) := by
  simp only [uSichert, uReachExport, found, bind, Except.bind, first, last, pure, Except.pure] <;> try rfl

/-- Slot membership retains the finite domain's declaration and the checked index. -/
theorem member_export (ctx : UCtx) (table : String) (number : Nat) (count : Int)
    (source : SExpr) (index : UIdx) (found : uTabNr ctx.tabs table = .ok (number, count))
    (checked : uMemberIndex ctx table number source = .ok index) :
    uSichert ctx (.ext .mem ["slots"] [source, .variable table]) = .ok (.member table index) := by
  simp only [uSichert, found, bind, Except.bind, checked, pure, Except.pure] <;> try rfl

/-- Tree membership preserves the outer seed, checked member index and direction. -/
theorem tree_membership_export (ctx : UCtx) (reverse : Bool) (value seed : SExpr)
    (table field : String) (number : Nat) (start stop : UIdx)
    (found : uTreeDomain ctx seed = .ok (table, number, start, field))
    (checked : uExportIndex ctx table number value = .ok stop) :
    uSichert ctx (.ext .mem [if reverse then "ancestors" else "descendants"] [value, seed]) =
      .ok (if reverse then .reach table field stop start else .reach table field start stop) := by
  cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> unfold uSichert <;>
    simp [found, checked, bind, Except.bind, pure, Except.pure]

/-- The actual reach lowerer retains the named optional-self field, checked endpoints and guard. -/
theorem reach_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name field : String) (a b : UIdx) (table : Fin u.tabs.length) (edge : SelfEdge u table field)
    (start stop : Expr (declOf u) Γ Λ (.index ((declOf u).count table)))
    (gate : u.exportGate = .ok ()) (found : tabIdx u.tabs name = .ok table)
    (typed : selfEdge u table field = .ok edge)
    (first : lowIdx u Γ Λ fn sh table a = .ok start) (last : lowIdx u Γ Λ fn sh table b = .ok stop)
    (guard : ∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ) :
    lowReach u Γ Λ fn sh name field a b =
      .ok (.reaches table edge.field edge.self start stop guard) := by
  simp only [lowReach, gate, bind, Except.bind, found, typed, first, last, guard, ↓reduceDIte, pure, Except.pure]
  split
  · rfl
  · contradiction

/-- Successful emission cannot lose the original-source gate even when another operand failed. -/
theorem reach_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name field : String) (a b : UIdx) (value : Expr (declOf u) Γ Λ .bool)
    (h : lowReach u Γ Λ fn sh name field a b = .ok value) : u.exportGate = .ok () := by
  cases gate : u.exportGate with
  | error error => simp only [lowReach, gate, bind, Except.bind] at h; contradiction
  | ok unit => cases unit; rfl

/-- A successful relation contains the actual checked field lookup and possession proof;
    an equal-count foreign edge cannot satisfy this certificate. -/
theorem reach_sound (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name field : String) (a b : UIdx) (value : Expr (declOf u) Γ Λ .bool)
    (h : lowReach u Γ Λ fn sh name field a b = .ok value) :
    u.exportGate = .ok () ∧
      ∃ (table : Fin u.tabs.length) (edge : SelfEdge u table field)
        (start stop : Expr (declOf u) Γ Λ (.index ((declOf u).count table))) (guard : darf (declOf u) table Λ),
        tabIdx u.tabs name = .ok table ∧ selfEdge u table field = .ok edge ∧
        lowIdx u Γ Λ fn sh table a = .ok start ∧ lowIdx u Γ Λ fn sh table b = .ok stop ∧
        value = .reaches table edge.field edge.self start stop guard := by
  have gate := reach_gate u Γ Λ fn sh name field a b value h
  refine ⟨gate, ?_⟩
  simp only [lowReach, gate, bind, Except.bind] at h
  cases found : tabIdx u.tabs name with
  | error error => simp only [found] at h; contradiction
  | ok table =>
    simp only [found] at h
    cases typed : selfEdge u table field with
    | error error => simp only [typed] at h; contradiction
    | ok edge =>
      simp only [typed] at h
      cases first : lowIdx u Γ Λ fn sh table a with
      | error error => simp only [first] at h; contradiction
      | ok start =>
        simp only [first] at h
        cases last : lowIdx u Γ Λ fn sh table b with
        | error error => simp only [last] at h; contradiction
        | ok stop =>
          simp only [last] at h
          split at h
          · rename_i guard
            exact ⟨table, edge, start, stop, guard, rfl, typed, first, last, (Except.ok.inj h).symm⟩
          · contradiction

/-- Membership keeps the actual numeric value and the existing finite domain guard. -/
theorem member_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name : String) (source : UIdx) (table : Fin u.tabs.length) (value : LowSide u Γ Λ)
    (gate : u.exportGate = .ok ()) (found : tabIdx u.tabs name = .ok table)
    (checked : lowMemberValue u Γ Λ fn sh table source = .ok value)
    (guard : ∀ resource ∈ (declOf u).braucht table, Res.von (declOf u) resource ∈ Λ) :
    lowMember u Γ Λ fn sh name source =
      .ok (Expr.existsSlots table (Expr.eq (.var .here) value.term.weaken) guard) := by
  simp only [lowMember, gate, bind, Except.bind, found, checked]
  split
  · rfl
  · contradiction

/-- Ordinary numbers outside the finite range yield false. The operand keeps its outer
    binding under the index, and membership still observes the guarded table carrier. -/
theorem member_meaning (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (shift : Nat)
    (table : Fin u.tabs.length) (source : UIdx) (value : LowSide u Γ Λ)
    (lowered : lowMemberValue u Γ Λ fn shift table source = .ok value)
    (guard : darf (declOf u) table Λ) (entry state : World (declOf u)) (env : Env (declOf u) Γ) :
    eval entry (Expr.existsSlots table (Expr.eq (.var .here) value.term.weaken) guard) state env =
      (alleIndizes ((declOf u).count table)).any
        (fun index => decide (index.n = (eval entry value.term state env).n)) := by
  have shifted (index : Zahl 0 ((declOf u).count table - 1)) :=
    member_value_scope u Γ Λ fn shift table source value lowered
      (binderTy := .index ((declOf u).count table)) index entry state env
  simp only [eval, shifted, wahr?]
  rfl

/-- A false or empty membership test still retains its table-read footprint. -/
theorem member_footprint (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (shift : Nat)
    (table : Fin u.tabs.length) (source : UIdx) (value : LowSide u Γ Λ)
    (lowered : lowMemberValue u Γ Λ fn shift table source = .ok value)
    (guard : darf (declOf u) table Λ) :
    (Expr.existsSlots table (Expr.eq (.var .here) value.term.weaken) guard).orte = [.inl table] := by
  have empty := indexSyntax_weaken_orte (lowMemberValue_syntax u Γ Λ fn shift table source value lowered)
    (binderTy := .index ((declOf u).count table))
  change .inl table :: (value.term.weaken : Expr (declOf u) (.index ((declOf u).count table) :: Γ) Λ
    (.int value.range.1 value.range.2)).orte = [.inl table]
  rw [empty]

theorem member_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat)
    (name : String) (source : UIdx) (value : Expr (declOf u) Γ Λ .bool)
    (h : lowMember u Γ Λ fn sh name source = .ok value) : u.exportGate = .ok () := by
  cases gate : u.exportGate with
  | error error => simp only [lowMember, gate, bind, Except.bind] at h; contradiction
  | ok unit => cases unit; rfl

/-- Canonical reach is bounded by the exact declared count and reads precisely the guarded carrier. -/
theorem reach_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (field : D.Feld table) (self : D.typ table field = .opt (D.count table))
    (a b : Expr D Γ Λ (.index (D.count table))) (guard : darf D table Λ)
    (entry state : World D) (env : Env D Γ) :
    eval entry (.reaches table field self a b guard) state env =
      kette (fun index => self ▸ state.slots table index field) (D.count table).toNat
        (eval entry a state env).n (eval entry b state env).n ∧
    (Expr.reaches table field self a b guard).orte = .inl table :: a.orte ++ b.orte := ⟨rfl, rfl⟩

/-- A declared nonempty carrier and a genuine optional self edge for export witnesses. -/
def relationUnit : UProg := {tabs := [{name := "T", count := 3, cols := [("next", (0, 0))], opts := [("next", 0)], kanten := [("child", "next")]}], locks := [], fns := []}

def relationContext : UCtx := {names := ["root", "last"], kinds := [.index 0, .index 0], types := [.index 3, .index 3], tabs := relationUnit.tabs, locks := [], held := [], res := none, fname := "sample", alias := [], lits := []}

def relationFunction : UFn := {name := "sample", params := [("root", .index 3), ("last", .index 3)], kinds := [.index 0, .index 0], res := none, held := [], puts := [], gives := [], body := [], ret := .empty}

private theorem lowVar_same_head (Γ : Ctx) (ty : Ty) :
    lowVar (ty :: Γ) 0 ty = .ok (.here : Var (ty :: Γ) ty) := by
  unfold lowVar
  rw [dite_eq_left (rfl : ty = ty)]

private theorem lowVar_next_head (Γ : Ctx) (head ty : Ty) :
    lowVar (head :: ty :: Γ) 1 ty = .ok (.there .here : Var (head :: ty :: Γ) ty) := by
  change (match lowVar (ty :: Γ) 0 ty with
    | .error error => .error error
    | .ok value => .ok (.there value)) = _
  rw [lowVar_same_head]

private theorem relation_table_guard :
    darf (declOf relationUnit) (⟨0, by decide⟩ : Fin relationUnit.tabs.length) [] := by
  intro resource present
  have empty : (declOf relationUnit).braucht (⟨0, by decide⟩ : Fin relationUnit.tabs.length) = [] := rfl
  rw [empty] at present
  cases present

private theorem member_root_checked :
    lowMember relationUnit [.index 3, .index 3] [] relationFunction 0 "T" (.param "root") =
      .ok (Expr.existsSlots (⟨0, by decide⟩ : Fin relationUnit.tabs.length)
        (Expr.eq (.var .here) (.var (.there .here))) relation_table_guard) := by
  exact member_lower relationUnit [.int 0 2, .int 0 2] [] relationFunction 0 "T" (.param "root")
    ⟨0, by decide⟩ {range := (0, 2), term := .var .here} rfl rfl
    (by simp [lowMemberValue, lowParamSide, relationFunction, paramPos, Ty.index,
      lowVar_same_head, bind, Except.bind, pure, Except.pure]) relation_table_guard

theorem count_export_zeuge :
    uAnzahl [("N", 2)] (.bin "*" (.variable "N") (.lit 3)) = .ok 6 ∧
    uAnzahl [] (.bin "-" (.lit 0) (.lit 1)) = .error "source export: negative constant count" :=
  ⟨rfl, rfl⟩

theorem initializer_export_zeuge :
    uInitialNumber [] 0 255 (.one (.bin "*" (.lit 21) (.lit 2))) = .ok 42 ∧
    uInitialNumber [] 0 255 (.one (.bin "-" (.bin "+" (.lit 255) (.lit 1)) (.lit 1))) =
      .error "source export: scalar initializer is outside its canonical constant domain" := ⟨rfl, rfl⟩

theorem reach_export_zeuge :
    uSichert relationContext (.ext .reach ["next"] [.variable "root", .variable "last"]) =
      .ok (.reach "T" "next" (.param "root") (.param "last")) ∧
    uSichert relationContext (.ext .mem ["slots"] [.variable "root", .variable "T"]) =
      .ok (.member "T" (.param "root")) := ⟨rfl, rfl⟩

theorem reach_lower_zeuge :
    (lowReach relationUnit [.index 3, .index 3] [] relationFunction 0 "T" "next"
      (.param "root") (.param "last")).toOption.isSome = true ∧
    (lowMember relationUnit [.index 3, .index 3] [] relationFunction 0 "T" (.param "root")).toOption.isSome = true := by
  constructor
  · have ready : (selfEdge relationUnit (⟨0, by decide⟩ : Fin relationUnit.tabs.length)
        "next").toOption.isSome = true := rfl
    cases typed : selfEdge relationUnit (⟨0, by decide⟩ : Fin relationUnit.tabs.length) "next" with
    | error error =>
      simp [typed] at ready
    | ok edge =>
      have emitted := reach_lower relationUnit [.index 3, .index 3] [] relationFunction 0
        "T" "next" (.param "root") (.param "last") ⟨0, by decide⟩ edge
        (.var .here) (.var (.there .here)) rfl rfl typed
        (by simp [lowIdx, relationFunction, paramPos, Ty.index, declOf, tabAt, relationUnit,
          lowVar_same_head])
        (by simp [lowIdx, relationFunction, paramPos, Ty.index, declOf, tabAt, relationUnit,
          lowVar_same_head, lowVar_next_head]) relation_table_guard
      rw [emitted]
      rfl
  · rw [member_root_checked]
    rfl

theorem tree_membership_export_zeuge :
    uSichert relationContext (.ext .mem ["descendants"] [.variable "last", .variable "root"]) =
      .ok (.reach "T" "next" (.param "root") (.param "last")) ∧
    uSichert relationContext (.ext .mem ["ancestors"] [.variable "root", .variable "last"]) =
      .ok (.reach "T" "next" (.param "root") (.param "last")) := ⟨rfl, rfl⟩

theorem member_numeric_export_zeuge :
    uSichert relationContext (.ext .mem ["slots"] [.lit 255, .variable "T"]) =
      .ok (.member "T" (.lit 255)) ∧
    uSichert relationContext (.ext .mem ["slots"] [.un "-" (.lit 1), .variable "T"]) =
      .ok (.member "T" (.lit (-1))) := ⟨rfl, rfl⟩

theorem member_numeric_lower_zeuge :
    (lowMember relationUnit [] [] relationFunction 0 "T" (.lit 255)).toOption.isSome = true ∧
    (lowMember relationUnit [] [] relationFunction 0 "T" (.lit (-1))).toOption.isSome = true := ⟨rfl, rfl⟩

theorem member_numeric_meaning_zeuge (entry state : World (declOf relationUnit)) :
    eval entry ((lowMember relationUnit [] [] relationFunction 0 "T" (.lit 255)).toOption.get
      member_numeric_lower_zeuge.1) state .nil = false ∧
    eval entry ((lowMember relationUnit [] [] relationFunction 0 "T" (.lit (-1))).toOption.get
      member_numeric_lower_zeuge.2) state .nil = false := ⟨rfl, rfl⟩

def numericMemberContext : UCtx := {relationContext with names := ["value"], kinds := [.int], types := [.int 0 255]}
def numericMemberFunction : UFn := {relationFunction with params := [("value", .int 0 255)], kinds := [.int]}

private theorem member_numeric_param_checked :
    lowMember relationUnit [.int 0 255] [] numericMemberFunction 0 "T" (.param "value") =
      .ok (Expr.existsSlots (⟨0, by decide⟩ : Fin relationUnit.tabs.length)
        (Expr.eq (.var .here) (.var (.there .here))) relation_table_guard) := by
  exact member_lower relationUnit [.int 0 255] [] numericMemberFunction 0 "T" (.param "value")
    ⟨0, by decide⟩ {range := (0, 255), term := .var .here} rfl rfl
    (by simp [lowMemberValue, lowParamSide, numericMemberFunction, relationFunction, paramPos,
      lowVar_same_head, bind, Except.bind, pure, Except.pure]) relation_table_guard

theorem member_numeric_param_zeuge :
    uSichert numericMemberContext (.ext .mem ["slots"] [.variable "value", .variable "T"]) =
      .ok (.member "T" (.param "value")) ∧
    (lowMember relationUnit [.int 0 255] [] numericMemberFunction 0 "T" (.param "value")).toOption.isSome = true :=
  ⟨rfl, by rw [member_numeric_param_checked]; rfl⟩

theorem member_numeric_param_meaning_zeuge (entry state : World (declOf relationUnit)) :
    let predicate := (lowMember relationUnit [.int 0 255] [] numericMemberFunction 0 "T" (.param "value")).toOption.get
      member_numeric_param_zeuge.2
    let good : Env (declOf relationUnit) [.int 0 255] := .cons ⟨2, by decide, by decide⟩ .nil
    let outside : Env (declOf relationUnit) [.int 0 255] := .cons ⟨255, by decide, by decide⟩ .nil
    eval entry predicate state good = true ∧ eval entry predicate state outside = false := by
  constructor <;>
    simp only [member_numeric_param_checked, Except.toOption, Option.get_some] <;> rfl

end Gabbro.Grammatik.Parser.ExportPreservation
