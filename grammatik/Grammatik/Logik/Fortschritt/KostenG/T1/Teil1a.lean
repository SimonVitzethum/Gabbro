module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
public import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The cost of the syntax -/

/- Cost of an expression: loads cost one plus their indices, primitive
    operations cost one plus their children, pure constructors cost nothing.
    Mirrors `kosten.rs::ausdruck` (`1 op = one Gabbro primitive`): constants
    cost `0`, a load costs `1` plus its index expressions, `Some` costs `1`,
    `None` and `&f` cost `0`, conversions (`weiter`) and bit intrinsics cost
    `1` plus their arguments. Contract-only quantifiers (`forallSlots`,
    `existsSlots`) never execute in G; they count as one read. Expressions
    take no step of their own in G (a step evaluates all of them at once),
    so this number only enters the bound as an over-approximation. -/
mutual
def kostenExpr {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Nat
  | .lit _ => 0
  | .tru => 0
  | .fls => 0
  | .var _ => 0
  | .glob _ _ => 1
  | .slot _ _ i _ => 1 + kostenExpr i
  | .thru p _ _ _ i _ => 1 + kostenExpr p + kostenExpr i
  | .thruOwn p _ _ _ i _ _ _ _ _ _ => 1 + kostenExpr p + kostenExpr i
  | .ptrOf _ _ _ _ => 0
  | .fnref _ _ _ => 0
  | .refEq a b => 1 + kostenExpr a + kostenExpr b
  | .slotRef r _ _ _ _ _ => 1 + kostenExpr r
  | .oldG _ _ => 1
  | .oldS _ _ i _ => 1 + kostenExpr i
  | .widen _ _ e => 1 + kostenExpr e
  | .add a b => 1 + kostenExpr a + kostenExpr b
  | .sub a b => 1 + kostenExpr a + kostenExpr b
  | .neg a => 1 + kostenExpr a
  | .mul a b => 1 + kostenExpr a + kostenExpr b
  | .div _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .rem _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .sdiv _ a b => 1 + kostenExpr a + kostenExpr b
  | .srem _ a b => 1 + kostenExpr a + kostenExpr b
  | .getBytes _ _ _ _ i _ _ _ => 1 + kostenExpr i
  | .band _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .bor _ _ _ _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .bxor _ _ _ _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .shl _ _ _ _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .shr _ _ _ _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .lt a b => 1 + kostenExpr a + kostenExpr b
  | .le a b => 1 + kostenExpr a + kostenExpr b
  | .eq a b => 1 + kostenExpr a + kostenExpr b
  | .fllt a b => 1 + kostenExpr a + kostenExpr b
  | .flle a b => 1 + kostenExpr a + kostenExpr b
  | .and a b => 1 + kostenExpr a + kostenExpr b
  | .or a b => 1 + kostenExpr a + kostenExpr b
  | .not a => 1 + kostenExpr a
  | .none _ => 0
  | .some e => 1 + kostenExpr e
  | .istSome e => 1 + kostenExpr e
  | .case _ _ nutz => 1 + kostenNutz nutz
  | .why _ _ => 0
  | .forallSlots _ _ _ => 1
  | .existsSlots _ _ _ => 1
  | .reaches _ _ _ a b _ => 1 + kostenExpr a + kostenExpr b
  | .arrNil => 0
  | .arrCons a b => 1 + kostenExpr a + kostenExpr b
  | .arrGet a b => 1 + kostenExpr a + kostenExpr b
  | .arrSet a i v => 1 + kostenExpr a + kostenExpr i + kostenExpr v
  | .strLit _ _ => 0
  | .strLen s => 1 + kostenExpr s
  | .strCat a b => 1 + kostenExpr a + kostenExpr b
  | .strGet a b => 1 + kostenExpr a + kostenExpr b
  | .strEq a b => 1 + kostenExpr a + kostenExpr b
  | .strLt a b => 1 + kostenExpr a + kostenExpr b
  | .strWeit _ s => 1 + kostenExpr s
  | .wenn c a b => 1 + kostenExpr c + kostenExpr a + kostenExpr b
  | .eng e _ _ s => 1 + kostenExpr e + kostenExpr s
  | .intBuiltin1 op a => op.arbeit + kostenExpr a
  | .intBuiltin2 op a b => op.arbeit + kostenExpr a + kostenExpr b
  | .count n body => 1 + n * (kostenExpr body + 1)
  | .prod _ args => kostenArgs args
  | .prodGet v _ => 1 + kostenExpr v
  | .prodSet v _ e => 1 + kostenExpr v + kostenExpr e

def kostenNutz {Γ : Ctx} {Λ : List (Res D)} {c : Option Ty} :
    NutzlastExpr D Γ Λ c → Nat
  | .empty => 0
  | .val e => kostenExpr e

/-- Cost of product field arguments and call arguments: the sum, as `kosten.rs::ruf` adds each one. -/
def kostenArgs {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} :
    Args D Γ Λ τs → Nat
  | .nil => 0
  | .cons e rest => kostenExpr e + kostenArgs rest
end

/-- Return predicates evaluated by `rufAt`, in declaration order. Reads and
    predicate evaluation occur inside a G return step, not as separate
    transitions; `kostenExpr` charges their primitive operations, including loads. -/
def kostenEpilog (P : Programm D) (f : D.Fn) : Nat :=
  kostenExpr (P.ensures f) +
    ((D.invs.filter (schuldet f)).map (fun i => kostenExpr (P.invariante i))).sum

/-- Cost of a return payload: nothing for `none`, the expression otherwise. -/
def kostenErg {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} :
    ErgExpr D Γ Λ o → Nat
  | .empty => 0
  | .val e => kostenExpr e

/-- The extra dispatch step of a compound at END position: G first moves
    it into block position (`endeEntf`), one step the block position does
    not take; the `2` pays that step and the empty-block close behind it. -/
def entfZ {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') : Nat :=
  if GEntfaltbar s = true then 2 else 0

theorem entfZ_wahr {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D V l Γ Λ Λ'} (h : GEntfaltbar s = true) : entfZ s = 2 := by
  simp only [entfZ, h, ↓reduceIte]

/- **The cost of statements, blocks and end blocks** -- the number of G
    steps a thread may take to run them, parametrised by
    * `ep : Nat`, the return-predicate price of this function, and
    * `c : D.Fn → Nat`, the cost a call counts for its callee (the callee's
      computed cost one depth down, `kostenTief`, or a declared table,
      `kostenPasst`), and
    * `pa : Nat`, the machine's `forever` budget (`passes` of
      `RufSchrittG`: `dannForever` gives the loop `passes` passes).
    Unit costs: every leaf `1` plus its expressions (one `blatt` step);
    branches take the maximum; `traverse` multiplies its body by the domain
    bound `(count t).toNat`, `retry n` by its `n` tries, `forever` by `pa`;
    every G step beyond the leaves (unfold, branch choice, lock take and
    release, `schrumpf`, empty-block close, loop resume) is paid by a
    constant `1` or `2`. The relation to the checker's number is in §10. -/
/- The mutually recursive costs take the scalar epilogue price explicitly.
   A `Vertrag` need not identify a unique function, so it cannot recover P/f.
   Threading this scalar through every return site also preserves the exact
   `kostenBlock_alsBlock = kostenSonst` equation; a top-level wrapper would
   miss returns inside blocks and would charge reason exits. Program-level
   consumers supply `kostenEpilog P f`; local body-only accounts supply 0.
   Scoped value returns deliver the same value answer after cleanup and owe
   the same epilogue. `rufAt`'s `.why` arm evaluates no return predicates. -/
mutual
def kostenStmt (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  | .assignSlot _ _ i e _ _ => 1 + kostenExpr i + kostenExpr e
  | .assignThru p _ _ _ i e _ _ => 1 + kostenExpr p + kostenExpr i + kostenExpr e
  | .assignThruOwn p _ _ _ i e _ _ _ _ _ _ _ => 1 + kostenExpr p + kostenExpr i + kostenExpr e
  | .assignSlotRef r _ _ _ _ e _ _ => 1 + kostenExpr r + kostenExpr e
  | .assignGlob _ e _ _ => 1 + kostenExpr e
  | .putBytes _ _ _ _ i _ _ e _ _ => 1 + kostenExpr i + kostenExpr e
  | .assignVar _ e => 1 + kostenExpr e
  | .shift _ _ _ i _ _ _ _ _ _ => 1 + kostenExpr i
  | .ite b t e => 1 + kostenExpr b + max (kostenBlock ep c pa t) (kostenBlock ep c pa e)
  | .onOption o p a => 2 + kostenExpr o + max (kostenBlock ep c pa p) (kostenBlock ep c pa a)
  | .onTag v arms => 2 + kostenExpr v + kostenArms ep c pa arms
  | .onWhy r arms => 1 + kostenExpr r + kostenGrundArms ep c pa arms
  | .call g args _ _ => 1 + kostenArgs args + c g
  /- Indirect call: the callee is named by a pointer VALUE, so the Lean
      model has no number for it (the checker reads `costs` off the
      pointer TYPE -- `kosten.rs::ruf`, «B8» -- and the Lean signature has
      no cost field). Counted without a callee here and EXCLUDED from the
      bound: the cost engine runs the gates with `ZS = fun _ => false` (see CUTS). -/
  | .callInd p args _ _ => 1 + kostenExpr p + kostenArgs args
  | .callIndElse p args _ _ _ err => 1 + kostenExpr p + kostenArgs args + (kostenSonst ep c pa err + 2)
  | .locks _ _ body => 2 + kostenBlock ep c pa body
  | .breaking _ body => 1 + kostenBlock ep c pa body
  | .traverse t inv body =>
      2 + (D.count t).toNat * (kostenBlock ep c pa body + kostenExpr inv + 2)
  -- Each selection pass spends one unit of the fuel installed by `dannVerbrauch`.
  | .consumeTraverse t member edge inv bound mass body =>
      2 + ((D.count t).toNat + bound.toNat + 1) * (kostenBlock ep c pa body + kostenExpr member +
        kostenExpr edge + kostenExpr inv + kostenExpr mass + 2)
  | .retry n bis body ueber =>
      2 + n * (kostenBlock ep c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock ep c pa ueber)
  | .forever _ inv body => 2 + pa * (kostenBlock ep c pa body + kostenExpr inv + 2)
  | .axiomCall _ args _ _ _ _ _ => 1 + kostenArgs args
  | .axiomCallElse _ _ args _ _ _ _ _ err => 1 + kostenArgs args + (kostenSonst ep c pa err + 2)
  | .regWrite _ _ e => 1 + kostenExpr e
  | .transition _ _ _ _ _ _ _ => 1
  | .publish _ e _ _ _ _ => 1 + kostenExpr e
  | .advances _ _ _ _ => 1
  | .retires _ _ _ _ => 1
  | .ret e _ => 1 + kostenErg e + ep
  | .retWhy _ _ => 1
  | .retScoped e _ => 1 + kostenErg e + ep
  | .retWhyScoped _ _ => 1
  | .leave _ => 1
  | .next _ => 1

def kostenBlock (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil => 1
  | .cons s rest => kostenStmt ep c pa s + kostenBlock ep c pa rest
  | .bind e rest => 2 + kostenExpr e + kostenBlock ep c pa rest
  | .bindCall g args _ _ _ rest => 2 + kostenArgs args + c g + kostenBlock ep c pa rest
  | .bindCallInd p args _ _ _ rest =>
      2 + kostenExpr p + kostenArgs args + kostenBlock ep c pa rest
  | .bindCallIndElse p args _ _ _ err rest =>
      2 + kostenExpr p + kostenArgs args + max (kostenSonst ep c pa err + 2) (kostenBlock ep c pa rest + 1)
  | .bindCallElse g args _ _ _ err rest =>
      2 + kostenArgs args + c g + max (kostenSonst ep c pa err + 2) (kostenBlock ep c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 2 + kostenArgs args + kostenBlock ep c pa rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      4 + kostenArgs args + kostenSonst ep c pa err + kostenBlock ep c pa rest
  | .bindAxiomOpt _ _ args _ _ _ _ rest => 2 + kostenArgs args + kostenBlock ep c pa rest
  | .bindAxiomOptElse _ _ args _ _ _ _ _ err rest =>
      4 + kostenArgs args + kostenSonst ep c pa err + kostenBlock ep c pa rest
  | .regRead _ _ rest => 2 + kostenBlock ep c pa rest
  | .regReadElse _ _ zusage sonst rest =>
      2 + kostenExpr zusage + max (kostenSonst ep c pa sonst + 1) (kostenBlock ep c pa rest + 1)
  | .awaits _ _ _ _ _ rest => 2 + kostenBlock ep c pa rest
  | .exchange _ neu _ _ rest => 2 + kostenExpr neu + kostenBlock ep c pa rest
  | .narrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenSonst ep c pa sonst + 1) (kostenBlock ep c pa rest + 1)
  | .narrowRequired e _ _ rest => 2 + kostenExpr e + (kostenBlock ep c pa rest + 1)
  | .check b sonst rest =>
      1 + kostenExpr b + max (kostenSonst ep c pa sonst + 1) (kostenBlock ep c pa rest)
  | .float _ a b _ _ rest => 2 + kostenExpr a + kostenExpr b + kostenBlock ep c pa rest
  | .floatLit _ _ _ rest => 2 + kostenBlock ep c pa rest
  | .floatOf e _ _ rest => 2 + kostenExpr e + kostenBlock ep c pa rest
  | .floatNarrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenSonst ep c pa sonst + 1) (kostenBlock ep c pa rest + 1)

def kostenArms (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (kostenBlock ep c pa b) (kostenArms ep c pa rest)

def kostenGrundArms (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (kostenBlock ep c pa b) (kostenGrundArms ep c pa rest)

def kostenEnd (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret e _ => 1 + kostenErg e + ep
  | .retWhy _ _ => 1
  | .retScoped e _ => 1 + kostenErg e + ep
  | .retWhyScoped _ _ => 1
  | .leave _ => 1
  | .next _ => 1
  | .cons s rest => entfZ s + kostenStmt ep c pa s + kostenEnd ep c pa rest
  | .bind e rest => 1 + kostenExpr e + kostenEnd ep c pa rest
  | .bindCall g args _ _ _ rest => 5 + kostenArgs args + c g + kostenSonst ep c pa rest
  | .bindCallElse g args _ _ _ err rest =>
      5 + kostenArgs args + c g + max (kostenSonst ep c pa err + 2) (kostenSonst ep c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 1 + kostenArgs args + kostenEnd ep c pa rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      1 + kostenArgs args + kostenEnd ep c pa err + kostenEnd ep c pa rest
  | .bindAxiomOpt _ _ args _ _ _ _ rest => 1 + kostenArgs args + kostenEnd ep c pa rest
  | .bindAxiomOptElse _ _ args _ _ _ _ _ err rest =>
      1 + kostenArgs args + kostenEnd ep c pa err + kostenEnd ep c pa rest
  | .regRead _ _ rest => 5 + kostenSonst ep c pa rest
  | .regReadElse _ _ zusage sonst rest =>
      5 + kostenExpr zusage + max (kostenSonst ep c pa sonst + 1) (kostenSonst ep c pa rest + 1)
  | .awaits _ _ _ _ _ rest => 5 + kostenSonst ep c pa rest
  | .bindCallInd p args _ _ _ rest => 5 + kostenExpr p + kostenArgs args + kostenSonst ep c pa rest
  | .bindCallIndElse p args _ _ _ err rest =>
      5 + kostenExpr p + kostenArgs args + max (kostenSonst ep c pa err + 2) (kostenSonst ep c pa rest + 1)
  -- unfolded into block position like the other compound end forms: the unfold step and the block's price
  | .narrow e _ _ sonst rest => 5 + kostenExpr e + max (kostenSonst ep c pa sonst + 1) (kostenSonst ep c pa rest + 1)
  | .narrowRequired e _ _ rest => 5 + kostenExpr e + (kostenSonst ep c pa rest + 1)
  | .exchange _ neu _ _ rest => 5 + kostenExpr neu + kostenSonst ep c pa rest
  | .ite b t e => 4 + kostenExpr b + max (kostenSonst ep c pa e + 1) (kostenSonst ep c pa t)

  | .float _ a b _ _ rest => 2 + kostenExpr a + kostenExpr b + kostenEnd ep c pa rest
  | .floatLit _ _ _ rest => 2 + kostenEnd ep c pa rest
  | .floatOf e _ _ rest => 2 + kostenExpr e + kostenEnd ep c pa rest
  -- Both branches stay in end position, including the narrowing fallback.
  | .floatNarrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenEnd ep c pa sonst + 1) (kostenEnd ep c pa rest + 1)
/-- The steps of an `else` branch: the end block run in BLOCK position
    (`Endblock.alsBlock`, since 2026-09-13), where a `leave`/`next` in it
    reaches the enclosing loop. Priced as that block: a compound needs no
    unfold, a `let` pays its `schrumpf` layer, the final statement its
    empty-block tail. -/
def kostenSonst (ep : Nat) (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret e _ => 2 + kostenErg e + ep
  | .retWhy _ _ => 2
  | .retScoped e _ => 2 + kostenErg e + ep
  | .retWhyScoped _ _ => 2
  | .leave _ => 2
  | .next _ => 2
  | .cons s rest => kostenStmt ep c pa s + kostenSonst ep c pa rest
  | .bind e rest => 2 + kostenExpr e + kostenSonst ep c pa rest
  | .bindCall g args _ _ _ rest => 2 + kostenArgs args + c g + kostenSonst ep c pa rest
  | .bindCallElse g args _ _ _ err rest =>
      2 + kostenArgs args + c g + max (kostenSonst ep c pa err + 2) (kostenSonst ep c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 2 + kostenArgs args + kostenSonst ep c pa rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      4 + kostenArgs args + kostenSonst ep c pa err + kostenSonst ep c pa rest
  | .bindAxiomOpt _ _ args _ _ _ _ rest => 2 + kostenArgs args + kostenSonst ep c pa rest
  | .bindAxiomOptElse _ _ args _ _ _ _ _ err rest =>
      4 + kostenArgs args + kostenSonst ep c pa err + kostenSonst ep c pa rest
  | .regRead _ _ rest => 2 + kostenSonst ep c pa rest
  | .regReadElse _ _ zusage sonst rest =>
      2 + kostenExpr zusage + max (kostenSonst ep c pa sonst + 1) (kostenSonst ep c pa rest + 1)
  | .awaits _ _ _ _ _ rest => 2 + kostenSonst ep c pa rest
  | .bindCallInd p args _ _ _ rest => 2 + kostenExpr p + kostenArgs args + kostenSonst ep c pa rest
  | .bindCallIndElse p args _ _ _ err rest =>
      2 + kostenExpr p + kostenArgs args + max (kostenSonst ep c pa err + 2) (kostenSonst ep c pa rest + 1)
  | .narrow e _ _ sonst rest => 2 + kostenExpr e + max (kostenSonst ep c pa sonst + 1) (kostenSonst ep c pa rest + 1)
  | .narrowRequired e _ _ rest => 2 + kostenExpr e + (kostenSonst ep c pa rest + 1)
  | .exchange _ neu _ _ rest => 2 + kostenExpr neu + kostenSonst ep c pa rest
  -- run as `Block.check b e t` (`Endblock.alsBlock`)
  | .ite b t e => 1 + kostenExpr b + max (kostenSonst ep c pa e + 1) (kostenSonst ep c pa t)
  | .float _ a b _ _ rest => 2 + kostenExpr a + kostenExpr b + kostenSonst ep c pa rest
  | .floatLit _ _ _ rest => 2 + kostenSonst ep c pa rest
  | .floatOf e _ _ rest => 2 + kostenExpr e + kostenSonst ep c pa rest
  | .floatNarrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenSonst ep c pa sonst + 1) (kostenSonst ep c pa rest + 1)

end

end Gabbro.Grammatik
