module
public import Grammatik.Parser.Elab.Export.ExportQuantifiers
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- `elems of` binds an array index, as specified in LANGUAGE section 6. The source
    binder has the exact length bound and no fabricated source table identity. -/
theorem array_quantifier_export (ctx : UCtx) (binder : String) (source body : SExpr)
    (array : USide) (element : Ty) (count : Nat) (predicate : UEns)
    (domain : uArrayDomain ctx source = .ok (array, element, count))
    (inside : uSichert {ctx with names := binder :: ctx.names, kinds := .int :: ctx.kinds, types := Ty.index count :: ctx.types, bits := 0 :: ctx.bits} body = .ok predicate) :
    uSichert ctx (.ext .all [binder, "elems"] [source, body]) =
      .ok (.arrayElements true array binder predicate) ∧
    uSichert ctx (.ext .any [binder, "elems"] [source, body]) =
      .ok (.arrayElements false array binder predicate) := by
  simp only [uSichert, domain, inside, bind, Except.bind, pure, Except.pure] <;> try rfl
  exact ⟨rfl, rfl⟩

/-- Array membership compares an outer value with each finite index, without capturing
    its source name or discarding the predicate check on an empty carrier. -/
theorem array_membership_export (ctx : UCtx) (source value : SExpr) (array compared : USide)
    (element : Ty) (count : Nat)
    (domain : uArrayDomain ctx source = .ok (array, element, count))
    (checked : uSeite ctx value = .ok compared) :
    uSichert ctx (.ext .mem ["elems"] [value, source]) =
      .ok (.arrayElements false array "#array-member" (.cmp "==" compared (.param "#array-member"))) := by
  simp only [uSichert, domain, checked, bind, Except.bind, pure, Except.pure]

/-- Array-domain extraction retains the exact represented type and the original term.
    A stateful read cannot silently become a lexical fixed domain. -/
theorem array_value_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (er : Option Ty) (source : USide) (array : ArrayValue u Γ Λ)
    (original : lowWertE u Γ Λ fn er source = .ok ⟨.arr array.element array.count, array.value⟩) :
    lowArrayValue u Γ Λ fn er source = .ok array := by
  simp only [lowArrayValue, original, bind, Except.bind, array.lexical, ↓reduceDIte] <;> try rfl

/-- The actual lowerer checks the predicate even for an empty array, retaining every
    type, guard, old/result and original-source duty before finite enumeration. -/
theorem array_quantifier_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn fnR : UFn) (er : Option Ty) (source : USide) (binder : String) (body : UEns)
    (array : ArrayValue u Γ Λ) (carrier : ArrayCarrier u array.count)
    (predicate : Expr (declOf u) (.index ((declOf u).count carrier.table) :: Γ) Λ .bool)
    (universal : Bool) (gate : u.exportGate = .ok ())
    (value : lowArrayValue u Γ Λ fn er source = .ok array)
    (iterator : arrayCarrier u array.count = .ok carrier) (result : ergAlsParam u fn er = .ok fnR)
    (guard : darf (declOf u) carrier.table Λ)
    (inside : lowEns u (.index ((declOf u).count carrier.table) :: Γ) Λ
      (fnR.mitTy binder (.index ((declOf u).count carrier.table))) none body = .ok predicate) :
    lowEns u Γ Λ fn er (.arrayElements universal source binder body) =
      .ok (if universal then .forallSlots carrier.table predicate guard
        else .existsSlots carrier.table predicate guard) := by
  simp only [lowEns, gate, value, iterator, result, guard, inside, bind, Except.bind,
    ↓reduceDIte, pure, Except.pure]
  split
  · rfl
  · contradiction

theorem array_quantifier_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (universal : Bool) (source : USide) (binder : String) (body : UEns)
    (value : Expr (declOf u) Γ Λ .bool)
    (lowered : lowEns u Γ Λ fn er (.arrayElements universal source binder body) = .ok value) :
    u.exportGate = .ok () := by
  cases gate : u.exportGate with
  | error error => simp only [lowEns, gate, bind, Except.bind] at lowered; contradiction
  | ok unit => cases unit; rfl

/-- The resulting G expression enumerates precisely the declared array index range.
    Array accesses in the predicate use the ordinary, full-value arrGet lowering. -/
theorem array_quantifier_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (count : Nat) (table : D.Tab) (same : D.count table = (count : Int)) (guard : darf D table Λ)
    (predicate : Expr D (.index (D.count table) :: Γ) Λ .bool) (universal : Bool)
    (entry state : World D) (env : Env D Γ) :
    eval entry (if universal then Expr.forallSlots table predicate guard
      else Expr.existsSlots table predicate guard) state env =
    (if universal then (alleIndizes (D.count table)).all
      (fun index => wahr? (eval entry predicate state (.cons index env)))
     else (alleIndizes (D.count table)).any
      (fun index => wahr? (eval entry predicate state (.cons index env)))) ∧
    D.count table = (count : Int) := by
  constructor
  · cases universal <;> rfl
  · exact same

/-- The production statement lowerer retains the exact invariant, lexical index binder,
    resource context, nested body and remaining statements. -/
theorem array_traversal_lower {loop : Bool} (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (top : AtTop u caller Λ)
    (binder : String) (source : USide) (invariant : UEns) (rest remaining : List UStmt)
    (array : ArrayValue u Γ Λ) (carrier : ArrayCarrier u array.count)
    (condition : Expr (declOf u) Γ Λ .bool)
    (body : Block (declOf u) (verOf u caller) true (.index ((declOf u).count carrier.table) :: Γ) Λ Λ)
    (gate : u.exportGate = .ok ()) (value : lowArrayValue u Γ Λ fn none source = .ok array)
    (iterator : arrayCarrier u array.count = .ok carrier)
    (outer : lowEns u Γ Λ fn none invariant = .ok condition)
    (inside : lowSeqL (l := true) u caller (.index ((declOf u).count carrier.table) :: Γ)
      (fn.mitTy binder (.index ((declOf u).count carrier.table))) fuel Λ top rest =
        .ok (body, .blkEnd :: remaining)) :
    lowStructL (l := loop) u caller Γ fn (fuel + 1) Λ top (.arrayLoopBeg binder source invariant) rest =
      .ok (.traverse carrier.table condition body, remaining) := by
  simp only [lowStructL_succ, lowStructStep, lowStufe_seq, gate, value, iterator, outer, inside, bind, Except.bind, pure, Except.pure]

/-- Traversal is the existing G finite-index loop. Invariant checks, leave/next/return,
    call logs and resource effects are carried by the existing traverseLauf semantics. -/
theorem array_traversal_meaning {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (table : D.Tab) (invariant : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count table) :: Γ) Λ Λ)
    (oracle : Orakel D) (passes : Nat)
    (calls : ∀ fn : D.Fn, World D → Env D (D.params fn) → RufAusgang fn)
    (state : World D) (env : Env D Γ) (loop : Bool) :
    execStmt oracle passes calls (l := loop) (.traverse table invariant body) state env =
    traverseLauf (execBlock oracle passes calls body)
      (fun state env => let observed := state.lese Λ invariant.orte
        (observed, wahr? (eval observed invariant observed env)))
      (alleIndizes (D.count table)) state env := by rfl

theorem array_membership_export_zeuge :
    let ctx : UCtx := {names := ["data"], kinds := [.wert], types := [.arr (.int 0 255) 2], tabs := [], locks := [], held := [], res := none, fname := "sample", alias := [], lits := []}
    uSichert ctx (.ext .mem ["elems"] [.lit 1, .variable "data"]) =
      .ok (.arrayElements false (.param "data") "#array-member" (.cmp "==" (.lit 1) (.param "#array-member"))) := by rfl

/-- A literal spelling a domain keyword is ordinary data, even beside an array type. -/
theorem array_carrier_marker_zeuge :
    let signature : FnSig := ⟨"impl", "sample", [("data", .array (.atom "u8") (.lit 2))], some (.atom "u8"), none, [], []⟩
    let body := SAnw.block [.bind false "message" none (.ext .text ["elems"] [])] (some (.ret (some (.lit 42))))
    uArrayCarriers [] [.fnT signature body] = [] := by rfl

end Gabbro.Grammatik.Parser.ExportPreservation
