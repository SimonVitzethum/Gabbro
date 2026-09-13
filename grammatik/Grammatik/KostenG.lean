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

import Grammatik.RufMaschineG
import Grammatik.RufAdaequatG

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
  | .wahr => 0
  | .falsch => 0
  | .var _ => 0
  | .glob _ _ => 1
  | .slot _ _ i _ => 1 + kostenExpr i
  | .durch p _ _ _ i _ => 1 + kostenExpr p + kostenExpr i
  | .ptrOf _ _ _ _ => 0
  | .fnref _ _ _ => 0
  | .altGlob _ _ => 1
  | .altSlot _ _ i _ => 1 + kostenExpr i
  | .weiter _ _ e => 1 + kostenExpr e
  | .add a b => 1 + kostenExpr a + kostenExpr b
  | .sub a b => 1 + kostenExpr a + kostenExpr b
  | .neg a => 1 + kostenExpr a
  | .mul a b => 1 + kostenExpr a + kostenExpr b
  | .div _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .rem _ _ a b => 1 + kostenExpr a + kostenExpr b
  | .sdiv _ a b => 1 + kostenExpr a + kostenExpr b
  | .srem _ a b => 1 + kostenExpr a + kostenExpr b
  | .leseBytes _ _ _ _ i _ _ _ => 1 + kostenExpr i
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
  | .und a b => 1 + kostenExpr a + kostenExpr b
  | .oder a b => 1 + kostenExpr a + kostenExpr b
  | .nicht a => 1 + kostenExpr a
  | .none _ => 0
  | .some e => 1 + kostenExpr e
  | .istSome e => 1 + kostenExpr e
  | .fall _ _ nutz => 1 + kostenNutz nutz
  | .grund _ _ => 0
  | .forallSlots _ _ _ => 1
  | .existsSlots _ _ _ => 1
  | .reaches _ _ _ a b _ => 1 + kostenExpr a + kostenExpr b

def kostenNutz {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} :
    NutzlastExpr D Γ Λ c → Nat
  | .keine => 0
  | .zahl e => kostenExpr e
end

/-- Cost of call arguments: the sum, as `kosten.rs::ruf` adds each one. -/
def kostenArgs {Γ : Ctx} {Λ : List (Res D)} {τs : List Ty} :
    Args D Γ Λ τs → Nat
  | .nil => 0
  | .cons e rest => kostenExpr e + kostenArgs rest

/-- Cost of a return payload: nothing for `none`, the expression otherwise. -/
def kostenErg {Γ : Ctx} {Λ : List (Res D)} {o : Option Ty} :
    ErgExpr D Γ Λ o → Nat
  | .keine => 0
  | .wert e => kostenExpr e

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
  | .assignDurch p _ _ _ i e _ _ => 1 + kostenExpr p + kostenExpr i + kostenExpr e
  | .assignGlob _ e _ _ => 1 + kostenExpr e
  | .schreibBytes _ _ _ _ i _ _ e _ _ => 1 + kostenExpr i + kostenExpr e
  | .assignVar _ e => 1 + kostenExpr e
  | .uebergang _ _ _ i _ _ _ _ _ _ => 1 + kostenExpr i
  | .ite b t e => 1 + kostenExpr b + max (kostenBlock c pa t) (kostenBlock c pa e)
  | .onOption o p a => 2 + kostenExpr o + max (kostenBlock c pa p) (kostenBlock c pa a)
  | .onTag v arms => 2 + kostenExpr v + kostenArms c pa arms
  | .onGrund r arms => 1 + kostenExpr r + kostenGrundArms c pa arms
  | .call g args _ _ => 1 + kostenArgs args + c g
  /- Indirect call: the callee is named by a pointer VALUE, so the Lean
      model has no number for it (the checker reads `costs` off the
      pointer TYPE -- `kosten.rs::ruf`, «B8» -- and the Lean signature has
      no cost field). Counted without a callee here and EXCLUDED from the
      bound by `rufeS` (see CUTS). -/
  | .callInd p args _ _ => 1 + kostenExpr p + kostenArgs args
  | .locks _ _ body => 2 + kostenBlock c pa body
  | .breaking _ body => 1 + kostenBlock c pa body
  | .traverse t inv body =>
      2 + (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2)
  | .retry n bis body ueber =>
      2 + n * (kostenBlock c pa body + kostenExpr bis + 2) + kostenBlock c pa ueber
  | .forever _ inv body => 2 + pa * (kostenBlock c pa body + kostenExpr inv + 2)
  | .axiomCall _ args _ _ _ _ _ => 1 + kostenArgs args
  | .regSchreib _ _ e => 1 + kostenExpr e
  | .transition _ _ _ _ _ _ _ => 1
  | .publish _ e _ _ _ _ => 1 + kostenExpr e
  | .advances _ _ _ _ => 1
  | .retires _ _ _ _ => 1
  | .ret e _ => 1 + kostenErg e
  | .retGrund _ _ => 1
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
      2 + kostenArgs args + c g + max (kostenEnd c pa err) (kostenBlock c pa rest + 1)
  | .bindAxiom _ args _ _ _ _ _ rest => 2 + kostenArgs args + kostenBlock c pa rest
  | .regLies _ _ rest => 2 + kostenBlock c pa rest
  | .regLiesElse _ _ zusage sonst rest =>
      2 + kostenExpr zusage + max (kostenEnd c pa sonst) (kostenBlock c pa rest + 1)
  | .awaits _ _ _ _ rest => 2 + kostenBlock c pa rest
  | .exchange _ neu _ _ rest => 2 + kostenExpr neu + kostenBlock c pa rest
  | .narrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenEnd c pa sonst) (kostenBlock c pa rest + 1)
  | .pruefung b sonst rest =>
      1 + kostenExpr b + max (kostenEnd c pa sonst) (kostenBlock c pa rest)
  | .gleit _ a b _ _ rest => 2 + kostenExpr a + kostenExpr b + kostenBlock c pa rest
  | .gleitLit _ _ _ rest => 2 + kostenBlock c pa rest
  | .gleitVon e _ _ rest => 2 + kostenExpr e + kostenBlock c pa rest
  | .gleitNarrow e _ _ sonst rest =>
      2 + kostenExpr e + max (kostenEnd c pa sonst) (kostenBlock c pa rest + 1)

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
  | .retGrund _ _ => 1
  | .leave _ => 1
  | .next _ => 1
  | .cons s rest => entfZ s + kostenStmt c pa s + kostenEnd c pa rest
  | .bind e rest => 1 + kostenExpr e + kostenEnd c pa rest
end

/-! ## 2. Which callees a body names -/

/- `rufeS Z s`: every DIRECT callee named in `s` satisfies `Z`, and `s`
    contains no indirect call (whose callee the syntax does not name). The
    bound needs to know, before a push, that the callee's cost was counted
    at a table the callee's own body fits under; this is the Bool that
    carries the admission of the callees down the residue. -/
mutual
def rufeS (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => rufeB Z t && rufeB Z e
  | .onOption _ p a => rufeB Z p && rufeB Z a
  | .onTag _ arms => rufeArms Z arms
  | .onGrund _ arms => rufeGArms Z arms
  | .call g _ _ _ => Z g
  | .callInd _ _ _ _ => false
  | .locks _ _ body => rufeB Z body
  | .breaking _ body => rufeB Z body
  | .traverse _ _ body => rufeB Z body
  | .retry _ _ body ueber => rufeB Z body && rufeB Z ueber
  | .forever _ _ body => rufeB Z body
  | .assignSlot .. => true
  | .assignDurch .. => true
  | .assignGlob .. => true
  | .schreibBytes .. => true
  | .assignVar .. => true
  | .uebergang .. => true
  | .axiomCall .. => true
  | .regSchreib .. => true
  | .transition .. => true
  | .publish .. => true
  | .advances .. => true
  | .retires .. => true
  | .ret .. => true
  | .retGrund .. => true
  | .leave _ => true
  | .next _ => true

def rufeB (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => rufeS Z s && rufeB Z rest
  | .bind _ rest => rufeB Z rest
  | .bindCall g _ _ _ _ rest => Z g && rufeB Z rest
  | .bindCallInd _ _ _ _ _ _ => false
  | .bindCallElse g _ _ _ _ err rest => Z g && rufeE Z err && rufeB Z rest
  | .bindAxiom _ _ _ _ _ _ _ rest => rufeB Z rest
  | .regLies _ _ rest => rufeB Z rest
  | .regLiesElse _ _ _ sonst rest => rufeE Z sonst && rufeB Z rest
  | .awaits _ _ _ _ rest => rufeB Z rest
  | .exchange _ _ _ _ rest => rufeB Z rest
  | .narrow _ _ _ sonst rest => rufeE Z sonst && rufeB Z rest
  | .pruefung _ sonst rest => rufeE Z sonst && rufeB Z rest
  | .gleit _ _ _ _ _ rest => rufeB Z rest
  | .gleitLit _ _ _ rest => rufeB Z rest
  | .gleitVon _ _ _ rest => rufeB Z rest
  | .gleitNarrow _ _ _ sonst rest => rufeE Z sonst && rufeB Z rest

def rufeArms (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => rufeB Z b && rufeArms Z rest

def rufeGArms (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => rufeB Z b && rufeGArms Z rest

def rufeE (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => rufeS Z s && rufeE Z rest
  | .bind _ rest => rufeE Z rest
end

/-- The callees of a residue: those of every block, end block and loop body
    still to run. -/
def rufeR (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .ende e => rufeE Z e
  | .dann b k => rufeB Z b && rufeR Z k
  | .schrumpf k => rufeR Z k
  | .frei _ k => rufeR Z k
  | .trav _ _ body _ k => rufeB Z body && rufeR Z k
  | .travRest _ _ body _ k => rufeB Z body && rufeR Z k
  | .wieder _ _ body ueber k => rufeB Z body && rufeB Z ueber && rufeR Z k
  | .wiederRest _ _ body ueber k => rufeB Z body && rufeB Z ueber && rufeR Z k
  | .ewig _ _ _ body k => rufeB Z body && rufeR Z k
  | .ewigRest _ _ _ body k => rufeB Z body && rufeR Z k
  | .wartet rest k => rufeB Z rest && rufeR Z k
  | .wartetSonst _ err rest k => rufeE Z err && rufeB Z rest && rufeR Z k

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
      1 + n * (kostenBlock c pa body + kostenExpr bis + 2) + kostenBlock c pa ueber +
        potRest c pa k
  | .wiederRest n bis body ueber k =>
      2 + n * (kostenBlock c pa body + kostenExpr bis + 2) + kostenBlock c pa ueber +
        potRest c pa k
  | .ewig _ n inv body k =>
      1 + n * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .ewigRest _ n inv body k =>
      2 + n * (kostenBlock c pa body + kostenExpr inv + 2) + potRest c pa k
  | .wartet rest k => kostenBlock c pa rest + 1 + potRest c pa k
  | .wartetSonst _ err rest k =>
      max (kostenEnd c pa err) (kostenBlock c pa rest + 1 + potRest c pa k)

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

theorem rufeB_armWahlG (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)),
    rufeArms Z arms = true → rufeB Z (armWahlG arms v).2.1 = true
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨⟨0, _⟩, _⟩, h => by
      simp only [rufeArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨⟨n + 1, hn⟩, nutz⟩, h => by
      simp only [rufeArms, Bool.and_eq_true] at h
      exact rufeB_armWahlG Z rest _ h.2

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

theorem rufeB_grundWahlG (Z : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n),
    rufeGArms Z arms = true → rufeB Z (grundWahlG arms r) = true
  | _, .nil, ⟨k, hk⟩, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons b rest, ⟨0, _⟩, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h
      exact h.1
  | _, .cons b rest, ⟨k + 1, hk⟩, h => by
      simp only [rufeGArms, Bool.and_eq_true] at h
      exact rufeB_grundWahlG Z rest _ h.2

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
      `c g` it counted for the callee;
    * (C) a pop -- the head frame (potential at least one, `potRest_pos`)
      leaves and the caller below resumes with at most its old potential.
    And the callees named in the residue stay admitted (`rufeR`). The
    indirect-call pushes fall in (B) only vacuously: their residue fails
    `rufeR`. -/

set_option hygiene false in
/-- Case (A) of `schrittArt`: rewrite the new head and the old head into
    their residues and unfold the costs. -/
macro "kopfA" : tactic => `(tactic| (
  refine Or.inl ⟨by dsimp only; rw [rufUpdateG_self], fun hok => ⟨?_, ?_⟩⟩ <;> dsimp only <;>
  rw [rufUpdateG_self] <;>
  rw [‹(M.faeden f).kopf.rest = _›] at hok <;> (try rw [‹(M.faeden f).kopf.rest = _›]) <;>
  dsimp only at hok ⊢ <;>
  simp only [potRest, kostenEnd, kostenBlock, kostenStmt, rufeR, rufeE, rufeB, rufeS,
    Bool.and_eq_true, List.length_cons, Nat.add_mul, Nat.one_mul] at hok ⊢))

/-- **One own step of the head: the potential argument, per rule of G.** -/
theorem schrittArt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O pa M f M') (c : D.Fn → Nat) (Z : D.Fn → Bool) :
    ((M'.faeden f).stapel = (M.faeden f).stapel ∧
      (rufeR Z (M.faeden f).kopf.rest.2.2.2.2 = true →
        rufeR Z (M'.faeden f).kopf.rest.2.2.2.2 = true ∧
        potRest c pa (M'.faeden f).kopf.rest.2.2.2.2 + 1 ≤
          potRest c pa (M.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (g : D.Fn) (caller' : RufRahmenG D) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden f).stapel = caller' :: (M.faeden f).stapel ∧
      (M'.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
        rho, .ende (P.rumpf g)⟩⟩ ∧
      (rufeR Z (M.faeden f).kopf.rest.2.2.2.2 = true →
        Z g = true ∧ rufeR Z caller'.rest.2.2.2.2 = true ∧
        potRest c pa caller'.rest.2.2.2.2 + 1 + c g ≤
          potRest c pa (M.faeden f).kopf.rest.2.2.2.2)) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst ∧ (M'.faeden f).stapel = rst ∧
      ∀ (c' : D.Fn → Nat) (Z' : D.Fn → Bool),
        (rufeR Z' caller.rest.2.2.2.2 = true →
          rufeR Z' (M'.faeden f).kopf.rest.2.2.2.2 = true) ∧
        potRest c' pa (M'.faeden f).kopf.rest.2.2.2.2 ≤ potRest c' pa caller.rest.2.2.2.2) := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead =>
    kopfA
    · simp_all
    · have := kostenStmt_pos c pa s; omega
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead =>
    kopfA
    · simp_all
    · have := kostenStmt_pos c pa s; omega
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    kopfA
    · simp_all
    · rw [entfZ_wahr hent]; omega
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw =>
    kopfA
    · have h := rufeB_armWahlG Z arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : rufeB Z b = true := h
      simp_all
    · have h := kostenBlock_armWahlG c pa arms (eval σ₁ v σ₁ ρ)
      rw [hw] at h
      have h2 : kostenBlock c pa b ≤ kostenArms c pa arms := h
      omega
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw =>
    kopfA
    · have h := rufeB_armWahlG Z arms (eval σ₁ v σ₁ ρ) hok.1.1
      rw [hw] at h
      have h2 : rufeB Z b = true := h
      simp_all
    · have h := kostenBlock_armWahlG c pa arms (eval σ₁ v σ₁ ρ)
      rw [hw] at h
      have h2 : kostenBlock c pa b ≤ kostenArms c pa arms := h
      omega
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw =>
    kopfA
    · have h := rufeB_grundWahlG Z arms (eval σ₁ r σ₁ ρ) hok.1.1
      rw [hw] at h
      simp_all
    · have h := kostenBlock_grundWahlG c pa arms (eval σ₁ r σ₁ ρ)
      rw [hw] at h
      omega
  | dannTrav l Γ Λ Λ'' t inv body rest k ρ hhead =>
    kopfA
    · simp_all
    · have h : @List.length (Wert D (.index (D.count t))) (alleIndizes (D.count t)) *
          (kostenBlock c pa body + kostenExpr inv + 2) ≤
          (D.count t).toNat * (kostenBlock c pa body + kostenExpr inv + 2) :=
        Nat.mul_le_mul_right _ (alleIndizes_length (D.count t))
      omega
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenEnd, kostenStmt, rufeR, rufeE, rufeS, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1, hok.2, by omega⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenBlock, kostenStmt, rufeR, rufeB, rufeS,
        Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1, ⟨hok.1.2, hok.2⟩, by omega⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1, ⟨hok.1.2, hok.2⟩, by omega⟩
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nach D g Λ, ρ, .wartetSonst (D.gruende g) err rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok ⊢
      dsimp only at hok ⊢
      simp only [potRest, kostenBlock, rufeR, rufeB, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1.1, ⟨⟨hok.1.1.2, hok.1.2⟩, hok.2⟩, by omega⟩
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .dann rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok
      dsimp only at hok
      simp only [rufeR, rufeB, rufeS, Bool.false_and, Bool.false_eq_true] at hok
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok
      dsimp only at hok
      simp only [rufeR, rufeE, rufeS, Bool.false_and, Bool.false_eq_true] at hok
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho =>
    refine Or.inr (Or.inl ⟨g, ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
      ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .wartet rest k⟩⟩, rho, s0,
      by dsimp only; rw [rufUpdateG_self], by dsimp only; rw [rufUpdateG_self], fun hok => ?_⟩)
    · rw [hhead] at hok
      dsimp only at hok
      simp only [rufeR, rufeB, Bool.false_and, Bool.false_eq_true] at hok
  | rueck caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | rueckCons caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]
    exact ⟨id, Nat.le_refl _⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> dsimp only <;>
      simp only [potRest, rufeR, Bool.and_eq_true] <;> exact ⟨fun h => by simp_all, by omega⟩
  | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potRest, rufeR, Bool.and_eq_true]
    exact ⟨fun h => h.1.1, by omega⟩
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potRest, rufeR, Bool.and_eq_true]
    exact ⟨fun h => h.1.1, by omega⟩
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    refine Or.inr (Or.inr ⟨caller, rst, hpop, by dsimp only; rw [rufUpdateG_self],
      fun c' Z' => ?_⟩)
    dsimp only; rw [rufUpdateG_self]; dsimp only
    rw [hcaller]; dsimp only
    simp only [potRest, rufeR, Bool.and_eq_true]
    exact ⟨fun h => h.1.1, by omega⟩
  | peelDannLeave l Γ Λ rest b k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; have := kostenBlock_pos c pa b; omega
  | peelDannNext l Γ Λ rest b k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; have := kostenBlock_pos c pa b; omega
  | peelSchrumpfLeave l Γ Λ τ rest k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelSchrumpfNext l Γ Λ τ rest k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelFreiLeave l Γ Λ L rest k ρ hleave hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | peelFreiNext l Γ Λ L rest k ρ hnext hhead =>
    kopfA
    · simp_all
    · have := kostenBlock_pos c pa rest; omega
  | _ =>
    kopfA
    · simp_all
    · omega
/-! ## 6. Counting one thread's steps -/

/- `RufErreichbarG` lives in `Prop`, so no function can count the steps of
    its derivations. `SegLauf` is the `Type`-valued twin: the same steps,
    made explicit, so `segZaehle` can count one thread's firings.
    `segLauf_erreichbar` forgets back, and `erreichbar_segLauf` is the
    converse (as a `Nonempty`): "any reachable run" and "any `SegLauf`"
    are the same runs. -/
inductive SegLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) : RufMaschineG D → Type where
  | start : SegLauf P O passes M0 M0
  | schritt (M M' : RufMaschineG D) (f : Faden)
      (h : SegLauf P O passes M0 M) (hs : RufSchrittG P O passes M f M') :
      SegLauf P O passes M0 M'

/-- Number of steps of thread `f` in an explicit run. Steps of other
    threads interleave freely and contribute nothing -- this is where
    scheduling delay drops out of the bound. -/
def segZaehle {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} : SegLauf P O passes M0 M → Faden → Nat
  | .start, _ => 0
  | .schritt _ _ g h' _, f => segZaehle h' f + (if g = f then 1 else 0)

/-- Every counted run is reachable. -/
theorem segLauf_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} (h : SegLauf P O passes M0 M) :
    RufErreichbarG P O passes M0 M := by
  induction h with
  | start => exact .start
  | schritt M M' f _ hs ih => exact .schritt M M' f ih hs

/-- Every reachable machine is the end of a counted run. -/
theorem erreichbar_segLauf {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 M : RufMaschineG D} (h : RufErreichbarG P O passes M0 M) :
    Nonempty (SegLauf P O passes M0 M) := by
  induction h with
  | start => exact ⟨.start⟩
  | schritt M M' f _ hs ih => exact ⟨.schritt M M' f (Classical.choice ih) hs⟩

/-- The frame has not returned before the last step: before every step of
    the run, thread `f` still has at least `k` frames below its head. A
    frame entered with `k` frames below it returns exactly when that number
    drops under `k`, so the return, if the run contains it, is the LAST
    step. -/
def aktivVor {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 : RufMaschineG D} (f : Faden) (k : Nat) : {M : RufMaschineG D} →
    SegLauf P O passes M0 M → Prop
  | _, .start => True
  | _, .schritt (M := M) _ _ h' _ => aktivVor f k h' ∧ k ≤ (M.faeden f).stapel.length

/-! ## 7. Where frames begin -/

/-- The entry of a frame: thread `f`'s head is a fresh frame of `g`
    (parameters `rho`, entry world `s0`, residue the whole body), with `k`
    frames below it. Every frame of G begins so: the start frames
    (`eintritt_start`) and every pushed callee (`eintritt_push`). -/
def Eintritt (P : Programm D) (f : Faden) (g : D.Fn) (rho : Env D (D.params g))
    (s0 : World D) (k : Nat) (M : RufMaschineG D) : Prop :=
  (M.faeden f).kopf = ⟨g, rho, s0, ⟨false, D.params g, Signatur.anfang D (D.signatur g),
    rho, .ende (P.rumpf g)⟩⟩ ∧ (M.faeden f).stapel.length = k

/-- The start frames are entries (no frame below). -/
theorem eintritt_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (f : Faden) :
    Eintritt P f (init f).1 (init f).2 (sp.welt []) 0 (RufStartG P sp init) :=
  ⟨rfl, rfl⟩

/-- Every push enters a frame: after a step of `f` that grows `f`'s stack,
    `f`'s head is an entry with one more frame below it. -/
theorem eintritt_push {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {f : Faden} (hs : RufSchrittG P O pa M f M')
    (hl : (M.faeden f).stapel.length < (M'.faeden f).stapel.length) :
    ∃ (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D),
      Eintritt P f g rho s0 ((M.faeden f).stapel.length + 1) M' := by
  rcases schrittArt hs (fun _ => 0) (fun _ => true) with
    ⟨hst, _⟩ | ⟨g, caller', rho, s0, hst, hk, _⟩ | ⟨caller, rst, hpop, hst, _⟩
  · rw [hst] at hl; exact absurd hl (Nat.lt_irrefl _)
  · exact ⟨g, rho, s0, hk, by rw [hst]; rfl⟩
  · rw [hst, hpop] at hl; simp only [List.length_cons] at hl; omega

/-! ## 8. The invariant and the engine -/

/-- The frames at and above the entry frame, each with an index `i` of the
    cost table `T i` it is costed at and of the admission `S i` its callees
    satisfy, and their total potential. -/
inductive Seg {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa : Nat) :
    List (RufRahmenG D) → Nat → Prop where
  | nil : Seg T S pa [] 0
  | cons (r : RufRahmenG D) (i : ι) (rs : List (RufRahmenG D)) (p : Nat)
      (hok : rufeR (S i) r.rest.2.2.2.2 = true) (h : Seg T S pa rs p) :
      Seg T S pa (r :: rs) (potRest (T i) pa r.rest.2.2.2.2 + p)

/-- **The invariant**: thread `f` runs the segment `kopf :: oben` above the
    `k` frames below the entry frame, `n` own steps are counted, and counted
    plus remaining potential fit under the budget `B`. Frames below the
    entry frame belong to callers outside the segment and carry nothing. -/
def KInv {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa B : Nat) (f : Faden)
    (k : Nat) (M : RufMaschineG D) (n : Nat) : Prop :=
  ∃ (oben unten : List (RufRahmenG D)) (Φ : Nat),
    (M.faeden f).stapel = oben ++ unten ∧ unten.length = k ∧
    Seg T S pa ((M.faeden f).kopf :: oben) Φ ∧ n + Φ ≤ B

section Motor

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  (P : Programm D) (O : Orakel D) (pa : Nat)

/-- Entry establishes the invariant with nothing counted, at the budget of
    the body costed at the entry frame's table. -/
theorem kinv_eintritt {f : Faden} {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D}
    {k : Nat} {M : RufMaschineG D} (hE : Eintritt P f g rho s0 k M) (i0 : ι)
    (hok : rufeE (S i0) (P.rumpf g) = true) :
    KInv T S pa (kostenEnd (T i0) pa (P.rumpf g)) f k M 0 := by
  obtain ⟨hk, hl⟩ := hE
  refine ⟨[], (M.faeden f).stapel, kostenEnd (T i0) pa (P.rumpf g) + 0, rfl, hl, ?_,
    by omega⟩
  rw [hk]
  exact Seg.cons _ i0 [] 0 hok Seg.nil

/-- **The engine step.** A step of any thread keeps the invariant as long
    as the frame is active: a foreign step changes nothing, an own step
    counts one and lowers the potential by at least one (`schrittArt`); the
    return of the entry frame itself still fits the budget. The two
    admission facts say that a callee admitted at index `i` has a body that
    fits the cost `T i g` counted for it, at the index `nx i g`, whose own
    callees are admitted there. -/
theorem kinv_schritt
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {B : Nat} {f : Faden} {k : Nat} {M M' : RufMaschineG D} {n : Nat} {g : Faden}
    (hI : KInv T S pa B f k M n) (hs : RufSchrittG P O pa M g M') :
    n + (if g = f then 1 else 0) ≤ B ∧
    (k ≤ (M'.faeden f).stapel.length →
      KInv T S pa B f k M' (n + (if g = f then 1 else 0))) := by
  by_cases hgf : g = f
  · subst hgf
    simp only [if_true]
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    cases hseg with
    | cons _ i _ p hok hrest =>
      rcases schrittArt hs (T i) (S i) with
        ⟨hst', hA⟩ | ⟨g', caller', rho, s0, hst', hk', hB'⟩ | ⟨caller, rst, hpop, hst', hC⟩
      · obtain ⟨hok', hpot⟩ := hA hok
        refine ⟨by omega, fun _ => ⟨oben, unten, _, by rw [hst', hst], hul,
          Seg.cons _ i oben p hok' hrest, by omega⟩⟩
      · obtain ⟨hZ, hokc, hpot⟩ := hB' hok
        have h1 := hS1 i g' hZ
        have h2 := hS2 i g' hZ
        refine ⟨by omega, fun _ => ⟨caller' :: oben, unten,
          kostenEnd (T (nx i g')) pa (P.rumpf g') + (potRest (T i) pa caller'.rest.2.2.2.2 + p),
          by rw [hst', hst]; rfl, hul, ?_, by omega⟩⟩
        rw [hk']
        exact Seg.cons _ (nx i g') _ _ h2 (Seg.cons _ i oben p hokc hrest)
      · have hpos := potRest_pos (T i) pa (M.faeden g).kopf.rest.2.2.2.2
        refine ⟨by omega, fun hk => ?_⟩
        cases oben with
        | nil =>
          rw [hst', ← List.nil_append rst] at hk
          rw [hst, List.nil_append] at hpop
          rw [hpop] at hul
          simp only [List.length_cons] at hul
          simp only [List.nil_append] at hk
          omega
        | cons o oben' =>
          rw [hst] at hpop
          simp only [List.cons_append, List.cons.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          cases hrest with
          | cons _ j _ p' hokj hrest' =>
            obtain ⟨hokc, hpotc⟩ := hC (T j) (S j)
            refine ⟨oben', unten, _, hst', hul, Seg.cons _ j oben' p' (hokc hokj) hrest', ?_⟩
            omega
  · simp only [hgf, if_false, Nat.add_zero]
    have hEq : M'.faeden f = M.faeden f := rufSchrittG_fremd hs f (Ne.symm hgf)
    obtain ⟨oben, unten, Φ, hst, hul, hseg, hB⟩ := hI
    refine ⟨by omega, fun _ => ⟨oben, unten, Φ, ?_, hul, ?_, hB⟩⟩
    · rw [hEq]; exact hst
    · rw [hEq]; exact hseg

/-- **The engine over a run.** From the entry invariant, along any run on
    which the frame stays active, the own steps never exceed the budget. -/
theorem kinv_lauf
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {B : Nat} {f : Faden} {k : Nat} {M1 : RufMaschineG D}
    (h0 : KInv T S pa B f k M1 0) :
    ∀ {M2 : RufMaschineG D} (run : SegLauf P O pa M1 M2), aktivVor f k run →
      segZaehle run f ≤ B ∧
      (k ≤ (M2.faeden f).stapel.length → KInv T S pa B f k M2 (segZaehle run f)) := by
  intro M2 run
  induction run with
  | start =>
    intro _
    refine ⟨?_, fun _ => h0⟩
    obtain ⟨_, _, _, _, _, _, hB⟩ := h0
    simp only [segZaehle]
    omega
  | schritt M M' g run' hs ih =>
    intro hA
    obtain ⟨hA', hk⟩ := hA
    have hI := (ih hA').2 hk
    exact kinv_schritt T S nx P O pa hS1 hS2 hI hs

/-- **The engine theorem**: a frame entered at index `i0` whose body names
    only callees admitted at `i0` takes at most `kostenEnd (T i0)` of its
    body own steps until (and including) its return. -/
theorem rahmen_schritte
    (hS1 : ∀ i g, S i g = true → kostenEnd (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (P.rumpf g) = true)
    {f : Faden} {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D} {k : Nat}
    {M1 M2 : RufMaschineG D} (hE : Eintritt P f g rho s0 k M1) (i0 : ι)
    (hok : rufeE (S i0) (P.rumpf g) = true)
    (run : SegLauf P O pa M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenEnd (T i0) pa (P.rumpf g) :=
  (kinv_lauf T S nx P O pa hS1 hS2 (kinv_eintritt T S P pa hE i0 hok) run hA).1

end Motor

/-! ## 9. TARGET 1: the bound by call depth -/

/-- The cost of `g` with calls nested at most `n` deep: at depth `0` no
    callee is admitted (cost `0`, never used); at depth `n + 1` the body,
    each call counting its callee at depth `n`. -/
def kostenTief (P : Programm D) (pa : Nat) : Nat → D.Fn → Nat
  | 0, _ => 0
  | n + 1, g => kostenEnd (kostenTief P pa n) pa (P.rumpf g)

/-- The call-depth admission, as a Bool: at depth `n + 1` a function is
    admitted if every direct callee of its body is admitted at depth `n`
    and the body has no indirect call; at depth `0` none is. The same depth
    discipline as `TiefK`/`Tief` (RufUmkehrRufG.lean, RufAdaequatRufG.lean),
    over the WHOLE syntax instead of a fragment, and decidable. -/
def rufTief (P : Programm D) : Nat → D.Fn → Bool
  | 0, _ => false
  | n + 1, g => rufeE (rufTief P n) (P.rumpf g)

/-- **TARGET 1 -- `frame_schritte_beschraenkt`.** Let thread `f` enter a
    frame of `g` with `k` frames below it (`Eintritt`, as every start frame
    and every pushed callee does), and let `g` be admitted at call depth
    `n + 1` (`rufTief`: callees nested at most `n` deep, no indirect call).
    On ANY run from there on which the frame has not returned before the
    last step (`aktivVor`), thread `f` takes at most
    `kostenTief P passes (n + 1) g` steps -- the body's cost with each call
    counting its callee's cost one depth down, each `traverse` its body
    times `count`, each `retry n` its body `n` times, each `forever` its
    body `passes` times.

    Counted: firings of `RufSchrittG` by `f`, including the frame's return
    if the run ends with it. Not counted: other threads' steps, and time
    during which a step of `f` cannot fire (a `locks` whose lock another
    thread holds, an `awaits` whose payload is not visible) -- the
    SCHEDULER ASSUMPTION of the file header. -/
theorem frame_schritte_beschraenkt (P : Programm D) (O : Orakel D) (passes : Nat)
    (f : Faden) (g : D.Fn) (n : Nat) (hadm : rufTief P (n + 1) g = true)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ kostenTief P passes (n + 1) g :=
  rahmen_schritte (kostenTief P passes) (rufTief P) (fun i _ => i - 1) P O passes
    (fun i h hS => by
      cases i with
      | zero => simp [rufTief] at hS
      | succ m => exact Nat.le_refl _)
    (fun i h hS => by
      cases i with
      | zero => simp [rufTief] at hS
      | succ m => exact hS)
    hE n hadm run hA

/-! ## 10. TARGET 2: the declared costs -/

/-- **`K001` as a Bool.** Every function of `fs` has a body whose cost --
    each call counting the callee's DECLARED cost `decl`, as `kosten.rs`
    counts it (SPRACHE.md §7) -- fits under its own declaration, and names
    only callees of `fs`, directly (no indirect call). -/
def kostenPasst [DecidableEq D.Fn] (P : Programm D) (passes : Nat) (decl : D.Fn → Nat)
    (fs : List D.Fn) : Bool :=
  fs.all fun g =>
    decide (kostenEnd decl passes (P.rumpf g) ≤ decl g) &&
      rufeE (fun h => fs.contains h) (P.rumpf g)

/-- **TARGET 2 -- `kosten_passt_deklaration`.** If the decidable check
    `kostenPasst` holds for the function list `fs`, every frame of a
    function of `fs`, on any run on which it has not returned before the
    last step, takes at most its function's DECLARED cost of own steps.
    (Recursion is not excluded by hand: a call counts `decl` of the callee,
    so a direct cycle fails the check, and any cycle the check lets through
    is still bounded -- the potential argument needs no well-founded call
    graph.) -/
theorem kosten_passt_deklaration [DecidableEq D.Fn] (P : Programm D) (O : Orakel D)
    (passes : Nat) (decl : D.Fn → Nat) (fs : List D.Fn)
    (hK : kostenPasst P passes decl fs = true)
    (f : Faden) (g : D.Fn) (hg : g ∈ fs)
    {rho : Env D (D.params g)} {s0 : World D} {k : Nat} {M1 M2 : RufMaschineG D}
    (hE : Eintritt P f g rho s0 k M1)
    (run : SegLauf P O passes M1 M2) (hA : aktivVor f k run) :
    segZaehle run f ≤ decl g := by
  have hall := List.all_eq_true.mp hK
  have hfs : ∀ h, h ∈ fs →
      kostenEnd decl passes (P.rumpf h) ≤ decl h ∧
        rufeE (fun h => fs.contains h) (P.rumpf h) = true := by
    intro h hh
    have := hall h hh
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  have hb := rahmen_schritte (fun (_ : Unit) => decl) (fun _ h => fs.contains h)
    (fun _ _ => ()) P O passes
    (fun _ h hS => (hfs h (List.contains_iff_mem.mp hS)).1)
    (fun _ h hS => (hfs h (List.contains_iff_mem.mp hS)).2)
    hE () (hfs g hg).2 run hA
  exact Nat.le_trans hb (hfs g hg).1

end Gabbro.Grammatik
