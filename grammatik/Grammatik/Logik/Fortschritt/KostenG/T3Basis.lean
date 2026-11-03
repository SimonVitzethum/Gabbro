/- Part 3 of 5 of `KostenG` (split by instrumente/teile/lean-teilen.py; the umbrella `KostenG.lean` imports all parts). -/
module
public import Grammatik.Logik.Fortschritt.KostenG.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **`K001` as a Bool.** Every function of `fs` has a body whose cost --
    each call counting the callee's DECLARED cost `decl`, as `kosten.rs`
    counts it (LANGUAGE.md §7) -- fits under its own declaration, and names
    only callees of `fs`, directly (no indirect call). -/
def kostenPasst [DecidableEq D.Fn] (P : Programm D) (passes : Nat) (decl : D.Fn → Nat)
    (fs : List D.Fn) : Bool :=
  fs.all fun g =>
    decide (kostenEnd decl passes (P.rumpf g) ≤ decl g) &&
      rufeE (fun h => fs.contains h) (fun _ => false) true (P.rumpf g)

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
        rufeE (fun h => fs.contains h) (fun _ => false) true (P.rumpf h) = true := by
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

/-! ## 11. TARGET 3: the checker's number

    `kosten.rs` counts OPERATIONS (LANGUAGE.md §7: `1 op` = one assignment,
    arithmetic operation, load or store; a call counts the callee's
    declared `costs`; branches the maximum; `traverse` the body times the
    domain bound). The bound above counts STEPS of machine G. The two are
    different units, and the Lean number is NOT at most the checker's
    number: G takes steps the checker prices at `0` (an `if` branch, a
    `leave`, a `return`, a lock take and release, an empty-block close).

    What holds, per statement form, is the converse with a remainder:
    `kostenK` is the checker's number as `kosten.rs` computes it, written
    over the Lean syntax (for the forms where the Lean term determines it,
    `spiegelS`), `zusatz` the remainder, and

      `kostenStmt c pa s ≤ kostenKS c s + zusatzS s`   (`spiegel_stmt`,
      likewise for blocks and end blocks), with the SAME callee table `c`.

    `zusatz` is, form by form:
    * the G dispatch steps, a constant per node: `ite` 1, `match` (option,
      tag) 2, `match` on a reason 1, a call 1 (the push; the pop is paid by
      the callee's `return`), `locks` 2 (take, release), `breaking` 1,
      `let` 1, `let x = g(…)` 1, `return`/`leave`/`next`/`retGrund` 1, an
      empty block 1, a compound in end position 2 (`entfZ`), per
      `traverse` iteration 2 plus the invariant, `awaits`/`exchange` 1;
    * and the parts the checker does not count at all (FINDINGS below):
      the index expressions of an assignment's TARGET place (F1), the
      `requires` predicate of a failable register read (F4), the subject
      of a `narrow` (F5), a `traverse` invariant (F6).

    FINDINGS for the transfer phase (kosten.rs vs. the Lean model):
    * F1 -- `StmtArt::Zuweisung` counts `1 + ausdruck(wert)` and never
      looks at the target place `ziel`: `t.slots[teuer()].x = 5` pays no
      op for `teuer()`, while a READ of the same place pays it (the
      2026-09-02 repair covered loads only). The same for compound
      assignment (`+=`: the load and the arithmetic are not counted).
    * F2 -- `retry … bounded N ops` costs `N` (`schleife`), and `K006`
      checks only that ONE pass fits `N`. The Lean loop `retry n` runs up
      to `n` passes (tries, not ops); the machine bound is
      `n * (pass + 2) + overflow`. Unless the lowering enforces the ops
      budget at run time, `N` does not bound the loop.
    * F3 -- `forever` has no checker number (`Unbekannt`, `K003` under a
      `costs` clause); the Lean bound multiplies by the machine budget
      `passes`, which the surface language names nowhere (`per_pass`
      bounds one pass; the number of passes is the `progress` assumption).
    * F4 -- `let x = R else …` (`LetSonst` over a place) counts `1 + 1 +
      sonst` and not the device `requires` predicate G evaluates.
    * F5 -- `narrow` counts `1 + sonst` and not its subject expression.
    * F6 -- `traverse` counts `body × bound` and not the loop invariant
      that G evaluates before every iteration (`travNext`, `travDone`).
    * F7 -- a recursive call under `decreases` costs NOTHING in kosten.rs
      («K5.4»); in the Lean check it costs the callee's `decl`, so such a
      function never passes `kostenPasst` (a direct self-call exceeds its
      own declaration).
    * F8 -- an indirect call costs its POINTER TYPE's `costs` in kosten.rs;
      the Lean signature has no cost field, so the bound excludes indirect
      calls (`rufeS`), and `spiegelS` excludes them too.
    * F9 -- constant expressions cost `0` in kosten.rs (`konst_wert`);
      `kostenExpr` counts their operators. G evaluates every expression in
      the step that uses it, so this only makes the Lean number larger.
    Not mirrored (no checker number determined by the Lean term): indirect
    calls (F8), `retry` (F2), `forever` (F3), `transition`, `advances`,
    `retires`. Axiom calls are outside `spiegelS` (their checker number is a
    certificate line, not a Lean term), but §13 counts them in the Lean bound
    through the declared table `fa`. -/

mutual
/-- The forms whose checker number the Lean term determines. -/
def spiegelS {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => spiegelB t && spiegelB e
  | .onOption _ p a => spiegelB p && spiegelB a
  | .onTag _ arms => spiegelArms arms
  | .onWhy _ arms => spiegelGArms arms
  | .locks _ _ body => spiegelB body
  | .breaking _ body => spiegelB body
  | .traverse _ _ body => spiegelB body
  | .consumeTraverse .. => false
  | .callInd .. => false
  | .callIndElse .. => false
  | .retry .. => false
  | .forever .. => false
  | .axiomCall .. => false
  | .axiomCallElse .. => false
  | .transition .. => false
  | .advances .. => false
  | .retires .. => false
  | .assignSlot .. => true
  | .assignThru .. | .assignThruOwn .. | .assignSlotRef .. => true
  | .assignGlob .. => true
  | .putBytes .. => true
  | .assignVar .. => true
  | .shift .. => true
  | .call .. => true
  | .regWrite .. => true
  | .publish .. => true
  | .ret .. => true
  | .retWhy .. => true
  | .retScoped .. => false
  | .retWhyScoped .. => false
  | .leave _ => true
  | .next _ => true

def spiegelB {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => spiegelS s && spiegelB rest
  | .bind _ rest => spiegelB rest
  | .bindCall _ _ _ _ _ rest => spiegelB rest
  | .bindCallInd .. => false
  | .bindCallIndElse .. => false
  | .bindCallElse _ _ _ _ _ err rest => spiegelE err && spiegelB rest
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead _ _ rest => spiegelB rest
  | .regReadElse _ _ _ sonst rest => spiegelE sonst && spiegelB rest
  | .awaits _ _ _ _ _ rest => spiegelB rest
  | .exchange _ _ _ _ rest => spiegelB rest
  | .narrow _ _ _ sonst rest => spiegelE sonst && spiegelB rest
  | .narrowRequired _ _ _ rest => spiegelB rest
  | .check _ sonst rest => spiegelE sonst && spiegelB rest
  | .float _ _ _ _ _ rest => spiegelB rest
  | .floatLit _ _ _ rest => spiegelB rest
  | .floatOf _ _ _ rest => spiegelB rest
  | .floatNarrow _ _ _ sonst rest => spiegelE sonst && spiegelB rest

def spiegelArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => spiegelB b && spiegelArms rest

def spiegelGArms {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => spiegelB b && spiegelGArms rest

def spiegelE {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retWhy .. => true
  | .leave _ => true
  | .next _ => true
  | .cons s rest => spiegelS s && spiegelE rest
  | .bind _ rest => spiegelE rest
  | .bindCall _ _ _ _ _ rest => spiegelE rest
  | .bindCallElse _ _ _ _ _ err rest => spiegelE err && spiegelE rest
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead _ _ rest => spiegelE rest
  | .regReadElse _ _ _ sonst rest => spiegelE sonst && spiegelE rest
  | .awaits _ _ _ _ _ rest => spiegelE rest
  | .bindCallInd .. => false
  | .bindCallIndElse .. => false
  -- the end-block forms of stage 0 are outside the checker's mirror until `kosten.rs` prices them (TODO.md)
  | .narrow .. => false
  | .narrowRequired .. => false
  | .retScoped .. => false
  | .retWhyScoped .. => false
  | .exchange .. => false
  | .ite .. => false
end
end Gabbro.Grammatik
