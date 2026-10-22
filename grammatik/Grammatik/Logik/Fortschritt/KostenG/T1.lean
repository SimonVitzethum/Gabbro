/-
  File:      Grammatik/KostenG.lean
  Subject:   A STEP BOUND PER FRAME ON THE CALL MACHINE G -- the time half
             of the goal: a frame's OWN steps between its entry and its
             return are bounded by a syntax-directed cost of its body.

  Claim (in one sentence):
    On any run of G, the number of steps thread `f` takes between the entry
    of a frame and that frame's return is at most `kosten` of the frame's
    body, where a call counts the callee's cost (by call depth, or by a
    declared table checked by a decidable `K001`-style test) and loops count
    their static bound; other threads' steps interleave and are not counted.

  What the bound counts: firings of `RufSchrittG P O passes M f M'` with the
    frame's thread `f` as actor, while the frame is on `f`'s stack. It does
    NOT count
    * steps of other threads (they never change `f`'s thread state,
      `rufSchrittG_fremd`), and
    * waiting: a `locks L` unfold (`dannLocks`) fires only while no other
      thread holds `L` (`RufFreiG`), an `awaits` only while the oracle says
      the payload is visible (`O.sichtbar`). While it cannot fire, it is not
      a step of anybody. How long a thread WAITS is therefore a scheduler
      fact: **SCHEDULER ASSUMPTION (not proved here): fair scheduling and a
      bounded hold time of every lock**. The surface language has the hold
      bound (`lock L … held <= N ops`, SYNTAX.md §lockdecl, checked by
      `kosten.rs` as `K002`), but the Lean declaration `Deklaration` does not
      carry it (the `Lock` fields are `rang` and `maskiert` only), so no
      waiting bound is stated here.

  The proof is a potential argument: `potRest` reads `kosten` as a function
  of the machine residue; every own step of the head frame lowers it by at
  least one (`schrittArt`), a push hands the callee at most the cost the
  caller counted for it, and a pop drops a frame whose potential is at least
  one. Nothing about reachability, lock discipline or contracts is needed.

  No `mathlib`, no `sorry`, no `axiom`.
-/

import Grammatik.Logik.Ruf.Maschine.RufMaschineG
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG
import Grammatik.Logik.Ruf.Umkehr.RufUmkehrRufG

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
  | .ptrOf _ _ _ _ => 0
  | .fnref _ _ _ => 0
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

def kostenNutz {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} :
    NutzlastExpr D Γ Λ c → Nat
  | .empty => 0
  | .num e => kostenExpr e
end
/-- Cost of call arguments: the sum, as `kosten.rs::ruf` adds each one. -/
def kostenArgs {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} :
    Args D Γ Λ τs → Nat
  | .nil => 0
  | .cons e rest => kostenExpr e + kostenArgs rest

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
  simp [entfZ, h]

/- **The cost of statements, blocks and end blocks** -- the number of G
    steps a thread may take to run them, parametrised by
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
mutual
def kostenStmt (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Nat
  | .assignSlot _ _ i e _ _ => 1 + kostenExpr i + kostenExpr e
  | .assignThru p _ _ _ i e _ _ => 1 + kostenExpr p + kostenExpr i + kostenExpr e
  | .assignGlob _ e _ _ => 1 + kostenExpr e
  | .putBytes _ _ _ _ i _ _ e _ _ => 1 + kostenExpr i + kostenExpr e
  | .assignVar _ e => 1 + kostenExpr e
  | .shift _ _ _ i _ _ _ _ _ _ => 1 + kostenExpr i
  | .ite b t e => 1 + kostenExpr b + max (kostenBlock c pa t) (kostenBlock c pa e)
  | .onOption o p a => 2 + kostenExpr o + max (kostenBlock c pa p) (kostenBlock c pa a)
  | .onTag v arms => 2 + kostenExpr v + kostenArms c pa arms
  | .onWhy r arms => 1 + kostenExpr r + kostenGrundArms c pa arms
  | .call g args _ _ => 1 + kostenArgs args + c g
  /- Indirect call: the callee is named by a pointer VALUE, so the Lean
      model has no number for it (the checker reads `costs` off the
      pointer TYPE -- `kosten.rs::ruf`, «B8» -- and the Lean signature has
      no cost field). Counted without a callee here and EXCLUDED from the
      bound: the cost engine runs the gates with `ZS = fun _ => false` (see CUTS). -/
  | .callInd p args _ _ => 1 + kostenExpr p + kostenArgs args
  | .locks _ _ body => 2 + kostenBlock c pa body
  | .breaking _ body => 1 + kostenBlock c pa body
  | .traverse t inv body =>
      2 + (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2)
  | .retry n bis body ueber =>
      2 + n * (kostenBlock c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock c pa ueber)
  | .forever _ inv body => 2 + pa * (kostenBlock c pa body + kostenExpr inv + 2)
  | .axiomCall _ args _ _ _ _ _ => 1 + kostenArgs args
  | .regWrite _ _ e => 1 + kostenExpr e
  | .transition _ _ _ _ _ _ _ => 1
  | .publish _ e _ _ _ _ => 1 + kostenExpr e
  | .advances _ _ _ _ => 1
  | .retires _ _ _ _ => 1
  | .ret e _ => 1 + kostenErg e
  | .retWhy _ _ => 1
  | .leave _ => 1
  | .next _ => 1

def kostenBlock (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Nat
  | .nil => 1
  | .cons s rest => kostenStmt c pa s + kostenBlock c pa rest
  | .bind e rest => 2 + kostenExpr e + kostenBlock c pa rest
  | .bindCall g args _ _ _ rest => 2 + kostenArgs args + c g + kostenBlock c pa rest
  | .bindCallInd p args _ _ _ rest =>
      2 + kostenExpr p + kostenArgs args + kostenBlock c pa rest
  | .bindCallElse g args _ _ _ err rest =>
      2 + kostenArgs args + c g + max (kostenSonst c pa err + 2) (kostenBlock c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 2 + kostenArgs args + kostenBlock c pa rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      4 + kostenArgs args + kostenSonst c pa err + kostenBlock c pa rest
  | .regRead _ _ rest => 2 + kostenBlock c pa rest
  | .regReadElse _ _ zusage sonst rest =>
      2 + kostenExpr zusage + max (kostenSonst c pa sonst + 1) (kostenBlock c pa rest + 1)
  | .awaits _ _ _ _ _ rest => 2 + kostenBlock c pa rest
  | .exchange _ neu _ _ rest => 2 + kostenExpr neu + kostenBlock c pa rest
  | .narrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenSonst c pa sonst + 1) (kostenBlock c pa rest + 1)
  | .check b sonst rest =>
      1 + kostenExpr b + max (kostenSonst c pa sonst + 1) (kostenBlock c pa rest)
  | .float _ a b _ _ rest => 2 + kostenExpr a + kostenExpr b + kostenBlock c pa rest
  | .floatLit _ _ _ rest => 2 + kostenBlock c pa rest
  | .floatOf e _ _ rest => 2 + kostenExpr e + kostenBlock c pa rest
  | .floatNarrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenSonst c pa sonst + 1) (kostenBlock c pa rest + 1)

def kostenArms (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Nat
  | .nil => 0
  | .cons b rest => max (kostenBlock c pa b) (kostenArms c pa rest)

def kostenGrundArms (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Nat
  | .nil => 0
  | .cons b rest => max (kostenBlock c pa b) (kostenGrundArms c pa rest)

def kostenEnd (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret e _ => 1 + kostenErg e
  | .retWhy _ _ => 1
  | .leave _ => 1
  | .next _ => 1
  | .cons s rest => entfZ s + kostenStmt c pa s + kostenEnd c pa rest
  | .bind e rest => 1 + kostenExpr e + kostenEnd c pa rest
  | .bindCall g args _ _ _ rest => 5 + kostenArgs args + c g + kostenSonst c pa rest
  | .bindCallElse g args _ _ _ err rest =>
      5 + kostenArgs args + c g + max (kostenSonst c pa err + 2) (kostenSonst c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 1 + kostenArgs args + kostenEnd c pa rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      1 + kostenArgs args + kostenEnd c pa err + kostenEnd c pa rest
  | .regRead _ _ rest => 5 + kostenSonst c pa rest
  | .regReadElse _ _ zusage sonst rest =>
      5 + kostenExpr zusage + max (kostenSonst c pa sonst + 1) (kostenSonst c pa rest + 1)
  | .awaits _ _ _ _ _ rest => 5 + kostenSonst c pa rest
  | .bindCallInd p args _ _ _ rest => 5 + kostenExpr p + kostenArgs args + kostenSonst c pa rest

/-- The steps of an `else` branch: the end block run in BLOCK position
    (`Endblock.alsBlock`, since 2026-09-13), where a `leave`/`next` in it
    reaches the enclosing loop. Priced as that block: a compound needs no
    unfold, a `let` pays its `schrumpf` layer, the final statement its
    empty-block tail. -/
def kostenSonst (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Nat
  | .ret e _ => 2 + kostenErg e
  | .retWhy _ _ => 2
  | .leave _ => 2
  | .next _ => 2
  | .cons s rest => kostenStmt c pa s + kostenSonst c pa rest
  | .bind e rest => 2 + kostenExpr e + kostenSonst c pa rest
  | .bindCall g args _ _ _ rest => 2 + kostenArgs args + c g + kostenSonst c pa rest
  | .bindCallElse g args _ _ _ err rest =>
      2 + kostenArgs args + c g + max (kostenSonst c pa err + 2) (kostenSonst c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 2 + kostenArgs args + kostenSonst c pa rest
  | .bindAxiomElse _ args _ _ _ _ _ _ err rest =>
      4 + kostenArgs args + kostenSonst c pa err + kostenSonst c pa rest
  | .regRead _ _ rest => 2 + kostenSonst c pa rest
  | .regReadElse _ _ zusage sonst rest =>
      2 + kostenExpr zusage + max (kostenSonst c pa sonst + 1) (kostenSonst c pa rest + 1)
  | .awaits _ _ _ _ _ rest => 2 + kostenSonst c pa rest
  | .bindCallInd p args _ _ _ rest => 2 + kostenExpr p + kostenArgs args + kostenSonst c pa rest
end
/-! ## 2. Which callees a body names -/

/- `rufeS Z ZS EW EW s`: every DIRECT callee named in `s` satisfies `Z`, and every
    indirect call in `s` goes through a signature `n` with `ZS n` (the syntax
    names the signature, not the callee; `ZS = fun _ => false` excludes
    indirect calls), and a `forever` stands in `s` only if `EW`. The
    bound needs to know, before a push, that the callee's cost was counted
    at a table the callee's own body fits under; this is the Bool that
    carries the admission of the callees down the residue. -/
mutual
def rufeS (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => rufeB Z ZS EW t && rufeB Z ZS EW e
  | .onOption _ p a => rufeB Z ZS EW p && rufeB Z ZS EW a
  | .onTag _ arms => rufeArms Z ZS EW arms
  | .onWhy _ arms => rufeGArms Z ZS EW arms
  | .call g _ _ _ => Z g
  | .callInd (n := n) _ _ _ _ => ZS n
  | .locks _ _ body => rufeB Z ZS EW body
  | .breaking _ body => rufeB Z ZS EW body
  | .traverse _ _ body => rufeB Z ZS EW body
  | .retry _ _ body ueber => rufeB Z ZS EW body && rufeB Z ZS EW ueber
  | .forever _ _ body => EW && rufeB Z ZS EW body
  | .assignSlot .. => true
  | .assignThru .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .axiomCall .. => true
  | .regWrite .. => true
  | .transition .. => true
  | .publish .. => true
  | .advances .. => true
  | .retires .. => true
  | .ret .. => true
  | .retWhy .. => true
  | .leave _ => true
  | .next _ => true

def rufeB (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => rufeS Z ZS EW s && rufeB Z ZS EW rest
  | .bind _ rest => rufeB Z ZS EW rest
  | .bindCall g _ _ _ _ rest => Z g && rufeB Z ZS EW rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => ZS n && rufeB Z ZS EW rest
  | .bindCallElse g _ _ _ _ err rest => Z g && rufeE Z ZS EW err && rufeB Z ZS EW rest
  | .bindAxiom _ _ _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => rufeE Z ZS EW err && rufeB Z ZS EW rest
  | .regRead _ _ rest => rufeB Z ZS EW rest
  | .regReadElse _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest
  | .awaits _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .exchange _ _ _ _ rest => rufeB Z ZS EW rest
  | .narrow _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest
  | .check _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest
  | .float _ _ _ _ _ rest => rufeB Z ZS EW rest
  | .floatLit _ _ _ rest => rufeB Z ZS EW rest
  | .floatOf _ _ _ rest => rufeB Z ZS EW rest
  | .floatNarrow _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeB Z ZS EW rest

def rufeArms (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => rufeB Z ZS EW b && rufeArms Z ZS EW rest

def rufeGArms (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => rufeB Z ZS EW b && rufeGArms Z ZS EW rest

def rufeE (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => rufeS Z ZS EW s && rufeE Z ZS EW rest
  | .bind _ rest => rufeE Z ZS EW rest
  | .bindCall g _ _ _ _ rest => Z g && rufeE Z ZS EW rest
  | .bindCallElse g _ _ _ _ err rest => Z g && rufeE Z ZS EW err && rufeE Z ZS EW rest
  | .bindAxiom _ _ _ _ _ _ _ rest => rufeE Z ZS EW rest
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => rufeE Z ZS EW err && rufeE Z ZS EW rest
  | .regRead _ _ rest => rufeE Z ZS EW rest
  | .regReadElse _ _ _ sonst rest => rufeE Z ZS EW sonst && rufeE Z ZS EW rest
  | .awaits _ _ _ _ _ rest => rufeE Z ZS EW rest
  | .bindCallInd (n := n) _ _ _ _ _ rest => ZS n && rufeE Z ZS EW rest
end
/-- The callees of a residue: those of every block, end block and loop body
    still to run. -/
def rufeR (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende e => rufeE Z ZS EW e
  | .dann b k => rufeB Z ZS EW b && rufeR Z ZS EW k
  | .schrumpf k => rufeR Z ZS EW k
  | .frei _ k => rufeR Z ZS EW k
  | .trav _ _ body _ k => rufeB Z ZS EW body && rufeR Z ZS EW k
  | .travRest _ _ body _ k => rufeB Z ZS EW body && rufeR Z ZS EW k
  | .wieder _ _ body ueber k => rufeB Z ZS EW body && rufeB Z ZS EW ueber && rufeR Z ZS EW k
  | .wiederRest _ _ body ueber k => rufeB Z ZS EW body && rufeB Z ZS EW ueber && rufeR Z ZS EW k
  | .ewig _ _ _ body k => EW && rufeB Z ZS EW body && rufeR Z ZS EW k
  | .ewigRest _ _ _ body k => EW && rufeB Z ZS EW body && rufeR Z ZS EW k
  | .wartet rest k => rufeB Z ZS EW rest && rufeR Z ZS EW k
  | .wartetSonst _ err rest k => rufeE Z ZS EW err && rufeB Z ZS EW rest && rufeR Z ZS EW k
  | .abbruch k => rufeR Z ZS EW k
  | .leer => true

/-! ## 3. The potential: `kosten` read as a function of the residue -/

/-- The steps a residue may still take: an end block or block costs what
    §1 says; a `schrumpf`/`frei` layer one step; a loop state its remaining
    iterations (list length, tries, budget) times one pass plus one; a
    `Rest` shim one more than the loop it resumes; a waiting caller its
    continuation (the callee's steps are counted in the callee's frame). -/
def potRest (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : GRest D V l Γ Λ → Nat
  | .ende e => kostenEnd c pa e
  | .dann b k => kostenBlock c pa b + potRest c pa k
  | .schrumpf k => 1 + potRest c pa k
  | .frei _ k => 1 + potRest c pa k
  | .trav _ inv body ks k =>
      1 + ks.length * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .travRest _ inv body ks k =>
      2 + ks.length * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .wieder n bis body ueber k =>
      1 + n * (kostenBlock c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock c pa ueber) +
        potRest c pa k
  | .wiederRest n bis body ueber k =>
      2 + n * (kostenBlock c pa body + kostenExpr bis + 2) + (2 + kostenExpr bis + kostenBlock c pa ueber) +
        potRest c pa k
  | .ewig _ n inv body k =>
      1 + n * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .ewigRest _ n inv body k =>
      2 + n * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .wartet rest k => kostenBlock c pa rest + 1 + potRest c pa k
  | .wartetSonst _ err rest k =>
      max (kostenSonst c pa err + 2 + potRest c pa k) (kostenBlock c pa rest + 1 + potRest c pa k)
  | .abbruch k => 1 + potRest c pa k
  | .leer => 1

section Positiv

variable (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem kostenStmt_pos {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') :
    1 ≤ kostenStmt c pa s := by
  cases s <;> simp only [kostenStmt] <;> omega

theorem kostenBlock_pos {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') :
    1 ≤ kostenBlock c pa b := by
  cases b with
  | cons s rest => have := kostenStmt_pos c pa s; simp only [kostenBlock]; omega
  | _ => simp only [kostenBlock]; omega

theorem kostenEnd_pos {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    1 ≤ kostenEnd c pa e := by
  cases e with
  | cons s rest => have := kostenStmt_pos c pa s; simp only [kostenEnd]; omega
  | _ => simp only [kostenEnd]; omega

theorem potRest_pos {Λ : List (Res D)} (r : GRest D V l Γ Λ) : 1 ≤ potRest c pa r := by
  cases r with
  | ende e => exact kostenEnd_pos c pa e
  | dann b k => have := kostenBlock_pos c pa b; simp only [potRest]; omega
  | wartet rest k => simp only [potRest]; omega
  | wartetSonst n err rest k => simp only [potRest]; omega
  | _ => simp only [potRest]; omega

/-- An end block run as a block costs `kostenSonst`. -/
theorem kostenBlock_alsBlock :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      kostenBlock c pa e.alsBlock.2 = kostenSonst c pa e
  | _, _, .ret _ _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]; omega
  | _, _, .retWhy _ _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .leave _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .next _ => by simp only [Endblock.alsBlock, kostenBlock, kostenStmt, kostenSonst]
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCall g args _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindAxiom _ args _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCallElse _ args _ _ _ err rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindAxiomElse _ args _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, kostenBlock, kostenSonst, kostenBlock_alsBlock rest]

/-- An end block run as a block names the callees the end block names. -/
theorem rufeB_alsBlock (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ),
      rufeB Z ZS EW e.alsBlock.2 = rufeE Z ZS EW e
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons s rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bind e rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCallElse _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, rufeB, rufeE, rufeB_alsBlock Z ZS EW rest]

end Positiv
/-! ## 4. Arm selection keeps cost and callees -/

theorem kostenBlock_armWahlG (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    kostenBlock c pa (armWahlG arms v).2.1 ≤ kostenArms c pa arms
  | _, .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩ => by
      simp only [armWahlG, kostenArms]; omega
  | _, .cons b rest, ⟨⟨n + 1, h⟩, nutz⟩ => by
      have ih := kostenBlock_armWahlG c pa rest ⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, by simpa using nutz⟩
      simp only [armWahlG, kostenArms]; omega

theorem rufeB_armWahlG (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    rufeArms Z ZS EW arms = true → rufeB Z ZS EW (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [rufeArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [rufeArms, Bool.and_eq_true] at h
      exact rufeB_armWahlG Z ZS EW rest _ h.2

theorem kostenBlock_grundWahlG (c : D.Fn → Nat) (pa : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    kostenBlock c pa (grundWahlG arms r) ≤ kostenGrundArms c pa arms
  | _, .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩ => by
      simp only [grundWahlG, kostenGrundArms]; omega
  | _, .cons b rest, ⟨k + 1, h⟩ => by
      have ih := kostenBlock_grundWahlG c pa rest ⟨k, Nat.lt_of_succ_lt_succ h⟩
      simp only [grundWahlG, kostenGrundArms]; omega

theorem rufeB_grundWahlG (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    rufeGArms Z ZS EW arms = true → rufeB Z ZS EW (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h
      exact rufeB_grundWahlG Z ZS EW rest _ h.2

/-- The index list of a `traverse` has at most `count` entries. -/
theorem alleIndizes_length (n : Int) : (alleIndizes n).length ≤ n.toNat := by
  unfold alleIndizes
  have h := List.length_filterMap_le
    (fun (k : Nat) => if h : ((k : Nat) : Int) ≤ n - 1 then
      some (⟨((k : Nat) : Int), by omega, h⟩ : Zahl 0 (n - 1)) else none) (List.range n.toNat)
  rw [List.length_range] at h
  exact h

/-! ## 5. One own step of the head

    Every step of thread `f` is one of three kinds (`schrittArt`):
    * (A) the head frame moves and the stack stays -- its potential drops
      by at least one;
    * (B) a push -- the callee enters its body, the caller continues below
      it, and the caller's potential drops by at least one PLUS the cost
      `c g` it counted for the callee (an indirect call admitted by `ZS`:
      by at least one, its callee uncounted);
    * (C) a pop -- the head frame (potential at least one, `potRest_pos`)
      leaves and the caller below resumes with at most its old potential.
    And the callees named in the residue stay admitted (`rufeR`). With
    `ZS = fun _ => false` an indirect-call push falls in (B) only
    vacuously: its residue fails `rufeR`. -/

set_option hygiene false in
/-- Case (A) of `schrittArt`: rewrite the new head and the old head into
    their residues and unfold the costs. -/
macro "kopfA" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ⟨?_, ?_⟩⟩ <;> dsimp only <;>
  rw [rufUpdateG_self] <;>
  rw [‹(M.faeden f).kopf.rest = _›] at hok <;> (try rw [‹(M.faeden f).kopf.rest = _›]) <;>
  dsimp only at hok ⊢ <;>
  simp only [potRest, kostenEnd, kostenBlock, kostenStmt, rufeR, rufeE, rufeB, rufeS,
    kostenBlock_alsBlock, rufeB_alsBlock,
    Bool.and_eq_true, List.length_cons, Nat.add_mul, Nat.one_mul] at hok ⊢))


