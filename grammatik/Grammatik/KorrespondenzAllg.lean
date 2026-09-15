/-
  File:      Grammatik/KorrespondenzAllg.lean
  Subject:   T2 PROPER: ONE decidable correspondence check for EVERY program
             whose emitted forms it covers, and its soundness down to the
             callee relation at every call depth (plan
             `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2, stage (a)).

  Before this file the correspondence certificate was checked in two ways,
  neither generic:
  * `certOk`/`certOkG` (Korrespondenz104.lean, Schlusssatz104.lean) compare
    the printed rows with 104's rows -- a check of ONE program;
  * `gbodyOk` (Korrespondenz.lean) decides shape and hygiene of general
    rows, but the link row <-> Gabbro statement is a PROOF (`REnd`) that a
    human writes per body.

  Here the link is DECIDED. `korrOk EL fnum c P fs` walks every body of
  `P` together with its printed rows and asks, statement by statement,
  whether the row is the emitted form of that statement: the slot store
  through a pointer or at a named table (`assignDurch`, `assignSlot`), the
  store to a local (`assignVar`), the compound assignment `x op= e`
  (`setOp`, the same C statement), the store to a plain file-scope scalar
  (`assignGlob`), the direct call with its arguments (`call`), `let`
  (`bind`), the `(void)x;` of an unused parameter, and the return of an
  expression or nothing (`ret`, falling off a `void` body).
  Expressions: literals, `true`/`false`, locals, widenings, slot loads
  through a pointer or at a named table (`slot`, `durch`), table pointers
  (`ptrOf`), plain globals, the arithmetic `+ - * / %` (signed and
  unsigned), the bitwise `& | ^ << >>`, the comparisons `< <= == > >=` and
  the boolean `&& || !`. Every other form makes the Bool `false` -- a
  refusal, never an admission.

  WIDENED 2026-09-15 (`OPUS-BERICHT-KORROK.md`). The check was NARROWER
  THAN ITS OWN STOCK OF PROVED LEMMAS: `ecorr_add` … `ecorr_shr`,
  `ecorr_lt` … `ecorr_eq`, `ecorr_nicht`, `ecorr_und`, `ecorr_oder`,
  `ecorr_glob`, `scorr_assignGlob` and the four `Zucker` compound
  assignments were all proved in `CFormenI.lean`/`CFormenM.lean` and all
  fell through `_ => false`. Nineteen arms moved inside the certificate
  with no new model reasoning; the ONE new lemma is `ecorr_geSwap` (the C
  operator `>=` for Gabbro's `le b a`), and it is `ecorr_cmp` with its
  operator fact. Every arm has a positive probe and a PLANTED DEFECT in
  `KorrespondenzWeitZeuge.lean` -- an arm that accepts a wrong row is worse
  than a missing arm.

  BLOCK STRUCTURE 2026-09-15 (`OPUS-BERICHT-BLOCK.md`). The check walks
  BLOCKS as well as terminal blocks: `if (c) { … } else { … }`
  (`GRow.ite` against `Stmt.ite`) is decided arm by arm, and inside a
  block `T y = g(a);` (`GRow.call` with a destination against
  `Block.bindCall`) binds the callee's answer to a fresh C local; the
  `traverse` header `for (T v = 0; v < N; v += 1) { … }` (`GRow.forTrav`
  against `Stmt.traverse`) is decided with its bound, its loop variable's
  freshness and the body's hygiene. A row that
  carries rows needs a recursion, and the recursion is STAGED, not
  mutual: `stOk0` (flat, no recursion) -> `blOk` (self-recursive over the
  rows, structurally) -> `stOk` (`stOk0` plus the block arms) -> `enOk`
  (unchanged). *It has to stay structural*: `korrOk` is settled by
  `decide` in every chain instance, and a well-founded definition does
  not reduce in the kernel. The soundness runs on a plain measure
  (`rowSize`), which a proof may do because a proof never reduces.

  THE SOUNDNESS (`korrOk_fnCorr`): a certificate that checks gives, for
  EVERY function and at EVERY call depth `n` and `forever` budget, the
  callee relation `FnCorr` between Gabbro's `rufAt P O passes n` and the
  C call `CallAt … (kProg c) n` of the unit the certificate elaborates
  to. Nothing is re-proved: each row is one existing T4 lemma
  (`scorr_assignDurch`, `scorr_assignVar`, `scorr_call`, `ecorr_slotVia`,
  `cCorr_ruf`, `cCorr_end`, …); the one new lemma is the argument passing
  of a call (`argsTo_of`), stated once for every argument list.

  THE LOCALS MAP is the EXPORTER'S: Gabbro variable `j` of a function is C
  local `vm[j]`, a pointer parameter is an ordinary variable whose value
  is the table's address (`ValCorr` at a pointer type). A callee's map
  must be exactly its C parameter list (`callMapOk`) -- the map the model
  of the source text has, not `refD`'s index-fixed map.
-/
import Grammatik.Korrespondenz
import Grammatik.CFormenDet

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0. The certificate -/

/-- One emitted function as certificate data: its C parameters (local
    number and declared C type, in order), its address-taken locals, its
    body rows in emission order, and the locals map of its Gabbro body
    (`vm`: variable `j` lives in C local `vm[j]`; `pp`/`ks` as in
    `CEnvLay`, empty in the exporter's map). -/
structure KFun (D : Deklaration) where
  params : List (Nat × CTy)
  locals : List Nat
  rows : List GRow
  vm : List Nat
  pp : List (Nat × D.Tab)
  ks : List (Nat × Int)

/-- A certificate: the unit's functions by C function number. -/
abbrev KCert (D : Deklaration) := List (KFun D)

/-- The locals map of one certified function. -/
def KFun.lay (k : KFun D) {Γ : Ctx} : CEnvLay D Γ := ⟨k.vm, k.pp, k.ks⟩

/-- Elaboration of a body's rows: sequencing; a trailing return row is the
    `return` itself; falling off the end is `skip`. -/
def endCS : List GRow → CS
  | [] => .skip
  | r :: rs => match r, rs with
    | .ret cr, [] => .ret cr
    | r, rs => .seq (growRow r) (endCS rs)

/-- The C unit a certificate elaborates to: function `n` is row list `n`. -/
def kProg (c : KCert D) : CProg := fun n =>
  (c[n]?).map fun k => { params := k.params, locals := k.locals, body := endCS k.rows }

/-! ## 1. The decidable check -/

/-- Every variable of a context, with its type. -/
def varsOf : (Γ : Ctx) → List (Σ τ, Var Γ τ)
  | [] => []
  | τ :: Γ => ⟨τ, .hier⟩ :: (varsOf Γ).map fun p => ⟨p.1, .dort p.2⟩

/-- A type is a pointer to table `t`. -/
def istZeigerAuf (t : D.Tab) : Ty → Bool
  | .ptr n _ => decide (D.tabNr n = some t)
  | _ => false

/-- The computation type of a binary or comparison node holds BOTH operand
    ranges -- the two `t.holds` facts `ecorr_binop`/`ecorr_cmp` need, and the
    reason C's conversions keep the Gabbro numbers (the signed/unsigned
    pitfall `-1 < 1u` is excluded by exactly this). -/
def randOk (t : CIT) (l1 h1 l2 h2 : Int) : Bool :=
  decide (t.holds l1 h1) && decide (t.holds l2 h2)

section Pruefung

variable (EL : EmitLay D) {Γ : Ctx} (K : CEnvLay D Γ)

/-- A C expression that is the address of table `t`: the named object, a
    pointer parameter of the map (`pp`), or the C local of a Gabbro pointer
    variable to `t`. -/
def ptrOk : CX → D.Tab → Bool
  | .addr (.tab k), t => decide (k = EL.tnr t)
  | .var kp, t => decide ((kp, t) ∈ K.pp) ||
      (varsOf Γ).any fun p => decide (K.loc p.2 = kp) && istZeigerAuf t p.1
  | _, _ => false

/-- The address `b->slots[·].f` and the loaded C type are the emitter's for
    field `f` of table `t` (the layout numbers of `EL`), `t` not a ghost. -/
def slotOk (b : CX) (n ss off : Nat) (τc : CTy) (t : D.Tab) (f : D.Feld t) : Bool :=
  ptrOk EL K b t && decide (n = (EL.trec t).count) && decide (ss = (EL.trec t).ssize) &&
    decide (off = (EL.trec t).off (EL.fnr t f)) && decide (τc = EL.slotTy t f) && !(D.geist t)

/-- EXPRESSIONS: the C expression is the emitted form of the Gabbro one. -/
def exOk {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (c : CX) : Bool :=
  match e, c with
  | .lit n, c => match c with
    | .lit m => decide (m = n)
    | _ => false
  | .var x, c => match c with
    | .var k => decide (k = K.loc x)
    | _ => false
  | .weiter _ _ e, c => exOk e c
  | .slot t f i _, c => match c with
    | .ld (.slotA b ci n ss off) τc => slotOk EL K b n ss off τc t f && exOk i ci
    | _ => false
  | .durch _ t _ f i _, c => match c with
    | .ld (.slotA b ci n ss off) τc => slotOk EL K b n ss off τc t f && exOk i ci
    | _ => false
  | .ptrOf t _ _ _, c => ptrOk EL K c t
  | .wahr, c => match c with
    | .lit m => decide (m = 1)
    | _ => false
  | .falsch, c => match c with
    | .lit m => decide (m = 0)
    | _ => false
  | .glob g _, c => match c with
    | .ld (.addr (.glob gn)) τc =>
        decide (gn = EL.gnr g) && decide (τc = EL.gty g) && !(D.ggeist g) && !(D.atomar g)
    | _ => false
  | .add (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, c => match c with
    | .bin .add t ca cb =>
        randOk t l1 h1 l2 h2 && decide (t.holds (l1 + l2) (h1 + h2)) && exOk a ca && exOk b cb
    | _ => false
  | .sub (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, c => match c with
    | .bin .sub t ca cb =>
        randOk t l1 h1 l2 h2 && decide (t.holds (l1 - h2) (h1 - l2)) && exOk a ca && exOk b cb
    | _ => false
  | .mul (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, c => match c with
    | .bin .mul t ca cb =>
        randOk t l1 h1 l2 h2 &&
          decide (t.holds (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
            (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) && exOk a ca && exOk b cb
    | _ => false
  | .div (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, c => match c with
    | .bin .div t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | _ => false
  | .rem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, c => match c with
    | .bin .mod t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | _ => false
  | .sdiv (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ a b, c => match c with
    | .bin .div t ca cb =>
        randOk t l1 h1 l2 h2 && (decide (t.sgn = false) || decide (t.lo < l1)) &&
          exOk a ca && exOk b cb
    | _ => false
  | .srem (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ a b, c => match c with
    | .bin .mod t ca cb =>
        randOk t l1 h1 l2 h2 && (decide (t.sgn = false) || decide (t.lo < l1)) &&
          exOk a ca && exOk b cb
    | _ => false
  | .band (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ a b, c => match c with
    | .bin .band t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | _ => false
  | .bor (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, c => match c with
    | .bin .bor t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | _ => false
  | .bxor (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, c => match c with
    | .bin .bxor t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | _ => false
  | .shl (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, c => match c with
    | .bin .shl t ca cb =>
        randOk t l1 h1 l2 h2 && decide (h2 < (t.bits : Int)) &&
          decide (t.holds 0 (h1 * 2 ^ h2.toNat)) && exOk a ca && exOk b cb
    | _ => false
  | .shr (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) _ _ _ _ _ a b, c => match c with
    | .bin .shr t ca cb =>
        randOk t l1 h1 l2 h2 && decide (h2 < (t.bits : Int)) && exOk a ca && exOk b cb
    | _ => false
  | .lt (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, c => match c with
    | .cmp .lt t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | .cmp .gt t ca cb => randOk t l2 h2 l1 h1 && exOk b ca && exOk a cb
    | _ => false
  | .le (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, c => match c with
    | .cmp .le t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | .cmp .ge t ca cb => randOk t l2 h2 l1 h1 && exOk b ca && exOk a cb
    | _ => false
  | .eq (l1 := l1) (h1 := h1) (l2 := l2) (h2 := h2) a b, c => match c with
    | .cmp .eq t ca cb => randOk t l1 h1 l2 h2 && exOk a ca && exOk b cb
    | _ => false
  | .und a b, c => match c with
    | .land ca cb => exOk a ca && exOk b cb
    | _ => false
  | .oder a b, c => match c with
    | .lor ca cb => exOk a ca && exOk b cb
    | _ => false
  | .nicht a, c => match c with
    | .lnot ca => exOk a ca
    | _ => false
  | _, _ => false
termination_by structural e

/-- The arguments of a call against the callee's C parameters: each
    argument is the emitted form of the Gabbro one, and the declared C type
    holds its Gabbro type. -/
def argsOk {Λ : List (Res D)} : {τs : List Ty} → Args D Γ Λ τs → List CX → List (Nat × CTy) → Bool
  | _, .nil, cs, ps => cs.isEmpty && ps.isEmpty
  | _, .cons (τ := τ) e rest, cs, ps => match cs, ps with
    | ce :: cs, (_, τc) :: ps => exOk EL K e ce && declOk τ τc && argsOk rest cs ps
    | _, _ => false

/-- A callee's map is its C parameter list (the exporter's map). -/
def callMapOk (k : KFun D) : Bool :=
  decide (k.vm = k.params.map Prod.fst) && k.pp.isEmpty && k.ks.isEmpty &&
    decide (k.params.map Prod.fst).Nodup

/-- A `(void)x;` names the C local of some Gabbro variable. -/
def voidOk (x : Nat) : Bool := (varsOf Γ).any fun p => decide (K.loc p.2 = x)

/-- The answer of a `return`. -/
def ergOk {Λ : List (Res D)} : {e : Option Ty} → ErgExpr D Γ Λ e → Option (CTy × CX) → Bool
  | _, .keine, none => true
  | some τ, .wert e, some (τc, ce) => declOk τ τc && exOk EL K e ce
  | _, _, _ => false

end Pruefung

section Rumpf

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D)

/-- STATEMENTS WITHOUT A SUB-BLOCK: the row is the emitted form of the
    statement. This is the FLAT stage of the staged recursion
    `stOk0` -> `blOk` -> `stOk` -> `enOk`; it does not recurse at all, so
    the only recursion in the check is `blOk`'s, and that one is
    STRUCTURAL on the rows. *The staging is not decoration*: `korrOk` is
    settled by `decide` in every chain instance, and a well-founded
    definition does not reduce in the kernel. -/
def stOk0 {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ) :
    Stmt D V l Γ Λ Λ' → GRow → Bool
  | .assignDurch _ t _ f i e _ _, r => match r with
    | .storeSlot kp ci n ss off τc ce =>
        slotOk EL K (.var kp) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | .storeNamed tn ci n ss off τc ce =>
        slotOk EL K (.addr (.tab tn)) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | _ => false
  | .assignSlot t f i e _ _, r => match r with
    | .storeSlot kp ci n ss off τc ce =>
        slotOk EL K (.var kp) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | .storeNamed tn ci n ss off τc ce =>
        slotOk EL K (.addr (.tab tn)) n ss off τc t f && exOk EL K i ci && exOk EL K e ce
    | _ => false
  | .assignVar (τ := τ) x e, r => match r with
    | .setVar k τc ce => K.okB && decide (k = K.loc x) && declOk τ τc && exOk EL K e ce
    -- `x op= e;` -- `Zucker`'s four compound assignments ARE `assignVar` of a
    -- binary expression whose left operand is `x` itself; the row spells the
    -- same C statement (`growRow`: `.set x τc (.bin op t (.var x) ce)`), so
    -- the arm is the `setVar` one at the assembled expression.
    | .setOp k τc op t ce =>
        K.okB && decide (k = K.loc x) && declOk τ τc && exOk EL K e (.bin op t (.var k) ce)
    | _ => false
  | .assignGlob g e _ _, r => match r with
    | .storeGlob gn τc ce =>
        decide (gn = EL.gnr g) && decide (τc = EL.gty g) && !(D.ggeist g) && !(D.atomar g) &&
          exOk EL K e ce
    | _ => false
  | .call g args _ _, r => match r with
    | .call fc cargs none => decide (fc = fnum g) &&
        (match c[fnum g]? with
          | some k => callMapOk k && argsOk EL K args cargs k.params
          | none => false)
    | _ => false
  | _, _ => false

mutual

/-- **STATEMENTS**: `stOk0` plus the two statements that carry a BLOCK.
    `if (c) { … } else { … }` is the row `GRow.ite`, which carries a row
    list per branch and elaborates to exactly the C `if`/`else` the
    emitter writes (`growRow`); the Gabbro side is `Stmt.ite` with a
    `Block` per branch, and both branches are walked by `blOk`. The
    `traverse` header is `GRow.forTrav` with the loop body's rows. The
    descent is STRUCTURAL on the ROW -- `tRows`, `eRows` and `bodyRows`
    are components of the row -- so no fuel and no well-founded recursion
    enter the check. -/
def stOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ)
    (s : Stmt D V l Γ Λ Λ') : GRow → Bool
  | .ite cc tRows eRows => (match s with
      | .ite cnd t e => exOk EL K cnd cc && blOk K t tRows && blOk K e eRows
      | _ => false)
  -- `for (T v = 0; v < N; v += 1) { … }` -- the `traverse` header. The
  -- upper bound must be the LITERAL count of the table (`scorr_traverse`
  -- wants `ev hiC = N` at every state, and a literal is the only C
  -- expression this file can decide that of), the loop variable must be
  -- fresh, and the body must not write it (`hw`, decided on the
  -- ELABORATED rows, as `rowsTravOk` does it in Korrespondenz.lean).
  | .forTrav x ti hiC bodyRows _m' => (match s, hiC with
      | .traverse tb _ body, .lit v =>
          K.okB && K.freshB x && decide (v = D.count tb) && decide (0 ≤ D.count tb) &&
            decide (ti.holds 0 (D.count tb)) &&
            decide ((growsCS bodyRows .skip).writesV x = false) &&
            blOk (K.push (.index (D.count tb)) x) body bodyRows
      | _, _ => false)
  | r => stOk0 EL fnum c K s r

/-- **BLOCKS** (`Block`: an `if` arm or a loop body): row by row, the same
    reading `enOk` gives a terminal block -- `(void)x;`, `let`, `let` of a
    call, and every other row against the block's head statement. A block
    does not end in a `return`, so there is no `ret` row here; the list
    ends with the block (`Block.nil`). -/
def blOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ)
    (b : Block D V l Γ Λ Λ') : List GRow → Bool
  | [] => (match b with
      | .nil => true
      | _ => false)
  | r :: rs => match r with
      | .void x => voidOk K x && blOk K b rs
      | .bindLet y τc ce => (match b with
          | .bind (τ := τ) e rest =>
              K.okB && K.freshB y && declOk τ τc && exOk EL K e ce &&
                blOk (K.push τ y) rest rs
          | _ => false)
      -- `T y = g(a, b);` -- the call whose ANSWER is bound. `Endblock` has
      -- no such constructor, so this row can only ever stand in a block.
      | .call fc cargs (some (y, τc)) => (match b with
          | .bindCall (τ := τ) g args _ _ _ rest =>
              decide (fc = fnum g) && K.okB && K.freshB y && declOk τ τc &&
                (match c[fnum g]? with
                  | some k => callMapOk k && argsOk EL K args cargs k.params
                  | none => false) &&
                blOk (K.push τ y) rest rs
          | _ => false)
      | r => (match b with
          | .cons s rest => stOk K s r && blOk K rest rs
          | _ => false)

end

/-- TERMINAL BLOCKS (a function body): row by row. `top` says the block is
    the whole body (a `void` body may fall off its end). -/
def enOk (top : Bool) {V : Vertrag D} {l : Bool} :
    List GRow → {Γ : Ctx} → {Λ : List (Res D)} → CEnvLay D Γ → Endblock D V l Γ Λ → Bool
  | [], _, _, _, b => match b with
    | .ret _ _ => top && decide (V.erg = none)
    | _ => false
  | r :: rs, _, _, K, b => match r with
    | .void x => voidOk K x && enOk top rs K b
    | .ret cr => rs.isEmpty && (match b with
        | .ret e _ => ergOk EL K e cr
        | _ => false)
    | .bindLet x τc ce => (match b with
        | .bind (τ := τ) e rest =>
            K.okB && K.freshB x && declOk τ τc && exOk EL K e ce && enOk top rs (K.push τ x) rest
        | _ => false)
    | r => (match b with
        | .cons s rest => stOk EL fnum c K s r && enOk top rs K rest
        | _ => false)

/-- **THE CHECK**: every function of `fs` has a certified C function (number
    `fnum f`), whose rows are the emitted form of its body under its map. -/
def korrOk (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => match c[fnum f]? with
    | some k => enOk EL fnum c true k.rows k.lay (P.rumpf f)
    | none => false

end Rumpf

/-! ### The measure the SOUNDNESS runs on

    The CHECK must be structural, because `korrOk` is settled by `decide`
    and the kernel has to reduce it. The PROOF is under no such duty -- a
    proof never reduces -- so the induction below runs on a plain measure
    over the rows, which spares the soundness theorem the shape of the
    mutual definition. -/

mutual
/-- The nesting weight of one row. -/
def rowSize : GRow → Nat
  | .void _ => 1
  | .storeSlot .. => 1
  | .storeNamed .. => 1
  | .storeGlob .. => 1
  | .setVar .. => 1
  | .setOp .. => 1
  | .bindLet .. => 1
  | .ite _ t e => rowsSize t + rowsSize e + 1
  | .call .. => 1
  | .ret .. => 1
  | .forTrav _ _ _ body _ => rowsSize body + 1
/-- The nesting weight of a row list. -/
def rowsSize : List GRow → Nat
  | [] => 0
  | r :: rs => rowSize r + rowsSize rs
end

theorem rowSize_pos (r : GRow) : 1 ≤ rowSize r := by
  cases r <;> simp only [rowSize] <;> omega

theorem rowsSize_nil : ∀ (rs : List GRow), rowsSize rs = 0 → rs = []
  | [], _ => rfl
  | r :: rs, h => by
      simp only [rowsSize] at h
      have := rowSize_pos r
      omega

/-! ## 2. Soundness, expression by expression -/

section Sound

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

theorem ptrOk_sound {cp : CX} {t : D.Tab} (h : ptrOk X.EL K cp t = true) : PtrTo X K cp t := by
  match cp, h with
  | .addr (.tab k), h =>
      have hk : k = X.EL.tnr t := of_decide_eq_true h
      subst hk
      exact ptrTo_named X K t
  | .var kp, h =>
      simp only [ptrOk, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ptrTo_param X K (of_decide_eq_true h)
      · obtain ⟨⟨τ, v⟩, -, hv⟩ := List.any_eq_true.mp h
        simp only [Bool.and_eq_true] at hv
        obtain ⟨hl, hz⟩ := hv
        have hl' : K.loc v = kp := of_decide_eq_true hl
        subst hl'
        cases τ with
        | ptr n rw => exact ptrTo_var X K v (of_decide_eq_true hz)
        | _ => simp [istZeigerAuf] at hz

theorem slotOk_sound {b : CX} {n ss off : Nat} {τc : CTy} {t : D.Tab} {f : D.Feld t}
    (h : slotOk X.EL K b n ss off τc t f = true) :
    PtrTo X K b t ∧ n = (X.EL.trec t).count ∧ ss = (X.EL.trec t).ssize ∧
      off = (X.EL.trec t).off (X.EL.fnr t f) ∧ τc = X.EL.slotTy t f ∧ D.geist t = false := by
  simp only [slotOk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hp, hn⟩, hs⟩, ho⟩, hτ⟩, hg⟩ := h
  exact ⟨ptrOk_sound X K hp, of_decide_eq_true hn, of_decide_eq_true hs, of_decide_eq_true ho,
    of_decide_eq_true hτ, hg⟩

/-- A table pointer in C against Gabbro's `ptrOf`. -/
theorem ecorr_ptrOf {cp : CX} {t : D.Tab} {n : Nat} {ht : D.tabNr n = some t} {rw : Bool}
    (hp : PtrTo X K cp t) : ExprCorr X K cp (Expr.ptrOf (Λ := Λ) t n ht rw) := by
  intro σ st ρG ρC _ hr
  exact ⟨_, st, hp st ρG ρC hr, t, ht, rfl⟩

/-- `a >= b`: `Zucker.ge a b` is `le b a`, and C writes `>=`. The one
    comparison operator the lemma stock did not name; `ecorr_cmp` (the
    scheme that excludes the signed/unsigned pitfall `-1 < 1u`) with its
    operator fact, nothing new assumed. `Zucker.gt` is `lt b a` and already
    has `ecorr_gt`. -/
theorem ecorr_geSwap (t : CIT) {l1 h1 l2 h2 : Int} {ca cb : CX}
    {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) (hta : t.holds l1 h1)
    (htb : t.holds l2 h2) :
    ExprCorr X K (.cmp .ge t ca cb) (.le b a) :=
  ecorr_cmp X K .ge t ha hb hta htb (fun _ _ => rfl)

/-- **Soundness of the expression check.** -/
theorem exOk_lit {n : Int} {c : CX} (h : exOk X.EL K (Expr.lit (Γ := Γ) (Λ := Λ) n) c = true) :
    ExprCorr X K c (Expr.lit (Γ := Γ) (Λ := Λ) n) := by
  cases c with
  | lit m =>
      have hm : m = n := of_decide_eq_true h
      subst hm
      exact ecorr_lit X K m
  | _ => exact absurd h (by simp [exOk])

theorem exOk_var {τ : Ty} {x : Var Γ τ} {c : CX} (h : exOk X.EL K (Expr.var (Λ := Λ) x) c = true) :
    ExprCorr X K c (Expr.var (Λ := Λ) x) := by
  cases c with
  | var k =>
      have hk : k = K.loc x := of_decide_eq_true h
      subst hk
      exact ecorr_var X K x
  | _ => exact absurd h (by simp [exOk])

/-- The slot-load arm, given the index correspondence. -/
theorem exOk_ld {t : D.Tab} {f : D.Feld t} {e : Expr D Γ Λ (D.typ t f)}
    {i : Expr D Γ Λ (.index (D.count t))} {c : CX}
    (h : (match c with
      | .ld (.slotA b ci n ss off) τc => slotOk X.EL K b n ss off τc t f && exOk X.EL K i ci
      | _ => false) = true)
    (hev : ∀ (σ : World D) (ρG : Env D Γ), eval σ e σ ρG = σ.slots t (eval σ i σ ρG).n f)
    (ih : ∀ ci, exOk X.EL K i ci = true → ExprCorr X K ci i) : ExprCorr X K c e := by
  cases c with
  | ld p τc =>
      cases p with
      | slotA b ci n ss off =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨hs, hi⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K hs
          subst hn hss hoff hτ
          exact ecorr_slotVia X K hp f hg (ih ci hi) hev
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

/-! ### The arms added on 2026-09-15: every one is an existing T4 lemma

    `exOk` was narrower than its own stock of proved lemmas -- the arithmetic,
    bitwise, comparison and boolean families all fell through `_ => false`
    although `ecorr_add` … `ecorr_shr`, `ecorr_lt` … `ecorr_eq`, `ecorr_nicht`,
    `ecorr_und`, `ecorr_oder` and `ecorr_glob` were proved. Each helper below
    takes the arm's own match as its hypothesis (so the check's text and the
    proof's text cannot drift apart) and the soundness of the operands, and
    ends in the lemma. NOTHING new is assumed. -/

theorem exOk_wahr {c : CX} (h : (match c with | .lit m => decide (m = 1) | _ => false) = true) :
    ExprCorr X K c (Expr.wahr (D := D) (Γ := Γ) (Λ := Λ)) := by
  cases c with
  | lit m =>
      have hm : m = 1 := of_decide_eq_true h
      subst hm
      exact ecorr_wahr X K
  | _ => exact absurd h (by simp)

theorem exOk_falsch {c : CX} (h : (match c with | .lit m => decide (m = 0) | _ => false) = true) :
    ExprCorr X K c (Expr.falsch (D := D) (Γ := Γ) (Λ := Λ)) := by
  cases c with
  | lit m =>
      have hm : m = 0 := of_decide_eq_true h
      subst hm
      exact ecorr_falsch X K
  | _ => exact absurd h (by simp)

theorem exOk_glob {g : D.Glob} {hL : gdarf D g Λ} {c : CX}
    (h : (match c with
      | .ld (.addr (.glob gn)) τc =>
          decide (gn = X.EL.gnr g) && decide (τc = X.EL.gty g) && !(D.ggeist g) && !(D.atomar g)
      | _ => false) = true) :
    ExprCorr X K c (Expr.glob (Γ := Γ) g hL) := by
  cases c with
  | ld p τc =>
      cases p with
      | addr b =>
          cases b with
          | glob gn =>
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
              obtain ⟨⟨⟨hn, hτ⟩, hgg⟩, hat⟩ := h
              have hn' : gn = X.EL.gnr g := of_decide_eq_true hn
              have hτ' : τc = X.EL.gty g := of_decide_eq_true hτ
              subst hn'
              subst hτ'
              exact ecorr_glob X K g hgg hat hL
          | _ => exact absurd h (by simp)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

/-- The three range facts of a `.bin` arm come out of `randOk` and the
    result decide. -/
theorem randOk_sound {t : CIT} {l1 h1 l2 h2 : Int} (h : randOk t l1 h1 l2 h2 = true) :
    t.holds l1 h1 ∧ t.holds l2 h2 := by
  simp only [randOk, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

/-- The signed division and remainder need `INT_MIN / -1` excluded: the
    computation type is unsigned, or the dividend's range starts above its
    minimum. -/
theorem sgnMin_sound {t : CIT} {l1 : Int}
    (h : (decide (t.sgn = false) || decide (t.lo < l1)) = true) : t.sgn = true → t.lo < l1 := by
  simp only [Bool.or_eq_true] at h
  intro hs
  rcases h with h | h
  · exact absurd (hs.symm.trans (of_decide_eq_true h)) (by simp)
  · exact of_decide_eq_true h

section BinArme

variable {l1 h1 l2 h2 : Int} {a : Expr D Γ Λ (.int l1 h1)} {b : Expr D Γ Λ (.int l2 h2)}
  (iha : ∀ ca, exOk X.EL K a ca = true → ExprCorr X K ca a)
  (ihb : ∀ cb, exOk X.EL K b cb = true → ExprCorr X K cb b)

include iha ihb

theorem exOk_add {c : CX} (h : (match c with
    | .bin .add t ca cb =>
        randOk t l1 h1 l2 h2 && decide (t.holds (l1 + l2) (h1 + h2)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.add a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | add =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_add X K t (iha ca hA) (ihb cb hB) hta htb (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_sub {c : CX} (h : (match c with
    | .bin .sub t ca cb =>
        randOk t l1 h1 l2 h2 && decide (t.holds (l1 - h2) (h1 - l2)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.sub a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | sub =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_sub X K t (iha ca hA) (ihb cb hB) hta htb (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_mul {c : CX} (h : (match c with
    | .bin .mul t ca cb =>
        randOk t l1 h1 l2 h2 &&
          decide (t.holds (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
            (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.mul a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | mul =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_mul X K t (iha ca hA) (ihb cb hB) hta htb (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_div {c : CX} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (h : (match c with
    | .bin .div t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.div h0 h1' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | div =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_div X K t h0 h1' (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_rem {c : CX} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (h : (match c with
    | .bin .mod t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.rem h0 h1' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | mod =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_rem X K t h0 h1' (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_sdiv {c : CX} (hb0 : 1 ≤ l2 ∨ h2 ≤ -1) (h : (match c with
    | .bin .div t ca cb =>
        randOk t l1 h1 l2 h2 && (decide (t.sgn = false) || decide (t.lo < l1)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.sdiv hb0 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | div =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, hm⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_sdiv X K t hb0 (iha ca hA) (ihb cb hB) hta htb (sgnMin_sound hm)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_srem {c : CX} (hb0 : 1 ≤ l2 ∨ h2 ≤ -1) (h : (match c with
    | .bin .mod t ca cb =>
        randOk t l1 h1 l2 h2 && (decide (t.sgn = false) || decide (t.lo < l1)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.srem hb0 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | mod =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, hm⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_srem X K t hb0 (iha ca hA) (ihb cb hB) hta htb (sgnMin_sound hm)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_band {c : CX} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (h : (match c with
    | .bin .band t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.band h0 h0' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | band =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_band X K t h0 h0' (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_bor {c : CX} {w : Nat} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < 2 ^ w) (h : (match c with
    | .bin .bor t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.bor w h0 h0' hw1 hw2 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | bor =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_bor X K t w h0 h0' hw1 hw2 (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_bxor {c : CX} {w : Nat} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w)
    (hw2 : h2 < 2 ^ w) (h : (match c with
    | .bin .bxor t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.bxor w h0 h0' hw1 hw2 a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | bxor =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_bxor X K t w h0 h0' hw1 hw2 (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_shl {c : CX} {w : Nat} (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (h : (match c with
    | .bin .shl t ca cb =>
        randOk t l1 h1 l2 h2 && decide (h2 < (t.bits : Int)) &&
          decide (t.holds 0 (h1 * 2 ^ h2.toNat)) && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.shl w hw1 hw2 h0 h0' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | shl =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨hr, hsh⟩, htr⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_shl X K t w hw1 hw2 h0 h0' (iha ca hA) (ihb cb hB) hta htb
            (of_decide_eq_true hsh) (of_decide_eq_true htr)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_shr {c : CX} {w : Nat} (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1)
    (h0' : 0 ≤ l2) (h : (match c with
    | .bin .shr t ca cb =>
        randOk t l1 h1 l2 h2 && decide (h2 < (t.bits : Int)) &&
          exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.shr w hw1 hw2 h0 h0' a b) := by
  cases c with
  | bin op t ca cb =>
      cases op with
      | shr =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨hr, hsh⟩, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_shr X K t w hw1 hw2 h0 h0' (iha ca hA) (ihb cb hB) hta htb
            (of_decide_eq_true hsh)
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_lt {c : CX} (h : (match c with
    | .cmp .lt t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | .cmp .gt t ca cb => randOk t l2 h2 l1 h1 && exOk X.EL K b ca && exOk X.EL K a cb
    | _ => false) = true) : ExprCorr X K c (.lt a b) := by
  cases c with
  | cmp op t ca cb =>
      cases op with
      | lt =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_lt X K t (iha ca hA) (ihb cb hB) hta htb
      | gt =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨htb, hta⟩ := randOk_sound hr
          exact ecorr_gt X K t (ihb ca hA) (iha cb hB) htb hta
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_le {c : CX} (h : (match c with
    | .cmp .le t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | .cmp .ge t ca cb => randOk t l2 h2 l1 h1 && exOk X.EL K b ca && exOk X.EL K a cb
    | _ => false) = true) : ExprCorr X K c (.le a b) := by
  cases c with
  | cmp op t ca cb =>
      cases op with
      | le =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_le X K t (iha ca hA) (ihb cb hB) hta htb
      | ge =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨htb, hta⟩ := randOk_sound hr
          exact ecorr_geSwap X K t (ihb ca hA) (iha cb hB) htb hta
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

theorem exOk_eqE {c : CX} (h : (match c with
    | .cmp .eq t ca cb => randOk t l1 h1 l2 h2 && exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.eq a b) := by
  cases c with
  | cmp op t ca cb =>
      cases op with
      | eq =>
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨hr, hA⟩, hB⟩ := h
          obtain ⟨hta, htb⟩ := randOk_sound hr
          exact ecorr_eq X K t (iha ca hA) (ihb cb hB) hta htb
      | _ => exact absurd h (by simp)
  | _ => exact absurd h (by simp)

end BinArme

section BoolArme

variable {a b : Expr D Γ Λ .bool}
  (iha : ∀ ca, exOk X.EL K a ca = true → ExprCorr X K ca a)
  (ihb : ∀ cb, exOk X.EL K b cb = true → ExprCorr X K cb b)

include iha ihb

theorem exOk_und {c : CX} (h : (match c with
    | .land ca cb => exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.und a b) := by
  cases c with
  | land ca cb =>
      simp only [Bool.and_eq_true] at h
      exact ecorr_und X K (iha ca h.1) (ihb cb h.2)
  | _ => exact absurd h (by simp)

theorem exOk_oder {c : CX} (h : (match c with
    | .lor ca cb => exOk X.EL K a ca && exOk X.EL K b cb
    | _ => false) = true) : ExprCorr X K c (.oder a b) := by
  cases c with
  | lor ca cb =>
      simp only [Bool.and_eq_true] at h
      exact ecorr_oder X K (iha ca h.1) (ihb cb h.2)
  | _ => exact absurd h (by simp)

end BoolArme

/-- `!(e)`. -/
theorem exOk_nicht {a : Expr D Γ Λ .bool} {c : CX}
    (iha : ∀ ca, exOk X.EL K a ca = true → ExprCorr X K ca a)
    (h : (match c with | .lnot ca => exOk X.EL K a ca | _ => false) = true) :
    ExprCorr X K c (.nicht a) := by
  cases c with
  | lnot ca => exact ecorr_nicht X K (iha ca h)
  | _ => exact absurd h (by simp)

theorem exOk_sound : ∀ {τ : Ty} (e : Expr D Γ Λ τ) (c : CX), exOk X.EL K e c = true →
    ExprCorr X K c e
  | _, .lit _, _, h => exOk_lit X K h
  | _, .var _, _, h => exOk_var X K h
  | _, .weiter h1 h2 e, c, h => ecorr_weiter X K h1 h2 (exOk_sound e c h)
  | _, .slot _ _ i _, _, h => exOk_ld X K h (fun _ _ => rfl) (fun ci hi => exOk_sound i ci hi)
  | _, .durch _ _ _ _ i _, _, h => exOk_ld X K h (fun _ _ => rfl) (fun ci hi => exOk_sound i ci hi)
  | _, .ptrOf _ _ _ _, _, h => ecorr_ptrOf X K (ptrOk_sound X K h)
  | _, .wahr, _, h => exOk_wahr X K h
  | _, .falsch, _, h => exOk_falsch X K h
  | _, .glob .., _, h => exOk_glob X K h
  | _, .add a b, _, h =>
      exOk_add X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .sub a b, _, h =>
      exOk_sub X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .mul a b, _, h =>
      exOk_mul X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .div h0 h1' a b, _, h =>
      exOk_div X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h0 h1' h
  | _, .rem h0 h1' a b, _, h =>
      exOk_rem X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h0 h1' h
  | _, .sdiv hb0 a b, _, h =>
      exOk_sdiv X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) hb0 h
  | _, .srem hb0 a b, _, h =>
      exOk_srem X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) hb0 h
  | _, .band h0 h0' a b, _, h =>
      exOk_band X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h0 h0' h
  | _, .bor _ h0 h0' hw1 hw2 a b, _, h =>
      exOk_bor X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        h0 h0' hw1 hw2 h
  | _, .bxor _ h0 h0' hw1 hw2 a b, _, h =>
      exOk_bxor X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        h0 h0' hw1 hw2 h
  | _, .shl _ hw1 hw2 h0 h0' a b, _, h =>
      exOk_shl X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        hw1 hw2 h0 h0' h
  | _, .shr _ hw1 hw2 h0 h0' a b, _, h =>
      exOk_shr X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc)
        hw1 hw2 h0 h0' h
  | _, .lt a b, _, h =>
      exOk_lt X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .le a b, _, h =>
      exOk_le X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .eq a b, _, h =>
      exOk_eqE X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .und a b, _, h =>
      exOk_und X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .oder a b, _, h =>
      exOk_oder X K (fun ca hc => exOk_sound a ca hc) (fun cb hc => exOk_sound b cb hc) h
  | _, .nicht a, _, h => exOk_nicht X K (fun ca hc => exOk_sound a ca hc) h
  | _, .fnref .., _, h => absurd h (by simp [exOk])
  | _, .altGlob .., _, h => absurd h (by simp [exOk])
  | _, .altSlot .., _, h => absurd h (by simp [exOk])
  | _, .neg .., _, h => absurd h (by simp [exOk])
  | _, .leseBytes .., _, h => absurd h (by simp [exOk])
  | _, .fllt .., _, h => absurd h (by simp [exOk])
  | _, .flle .., _, h => absurd h (by simp [exOk])
  | _, .none .., _, h => absurd h (by simp [exOk])
  | _, .some .., _, h => absurd h (by simp [exOk])
  | _, .istSome .., _, h => absurd h (by simp [exOk])
  | _, .fall .., _, h => absurd h (by simp [exOk])
  | _, .grund .., _, h => absurd h (by simp [exOk])
  | _, .forallSlots .., _, h => absurd h (by simp [exOk])
  | _, .existsSlots .., _, h => absurd h (by simp [exOk])
  | _, .reaches .., _, h => absurd h (by simp [exOk])

/-- **Soundness of the answer check.** -/
theorem ergOk_sound : ∀ {e : Option Ty} (r : ErgExpr D Γ Λ e) (cr : Option (CTy × CX)),
    ergOk X.EL K r cr = true → ErgCorr X K r cr := by
  intro e r cr h
  cases r with
  | keine =>
      cases cr with
      | none => rfl
      | some _ => exact absurd h (by simp [ergOk])
  | wert e =>
      cases cr with
      | none => exact absurd h (by simp [ergOk])
      | some q =>
          obtain ⟨τc, ce⟩ := q
          simp only [ergOk, Bool.and_eq_true] at h
          exact ⟨τc, ce, rfl, exOk_sound X K e ce h.2, h.1⟩

/-- The value of an argument list under a map that IS the C parameter list:
    the locals relation of the bound parameters. -/
theorem argsOk_len : ∀ {τs : List Ty} (args : Args D Γ Λ τs) (cs : List CX)
    (ps : List (Nat × CTy)), argsOk X.EL K args cs ps = true → ps.length = τs.length
  | _, .nil, cs, ps, h => by
      simp only [argsOk, Bool.and_eq_true, List.isEmpty_iff] at h
      rw [h.2]; rfl
  | _, .cons _ rest, cs, ps, h => by
      match cs, ps, h with
      | _ :: cs, _ :: ps, h =>
          simp only [argsOk, Bool.and_eq_true] at h
          simp only [List.length_cons]
          rw [argsOk_len rest cs ps h.2]
      | [], _, h => simp [argsOk] at h
      | _ :: _, [], h => simp [argsOk] at h

/-- **THE ARGUMENT PASSING of a call, for every argument list**: arguments
    that are the emitted forms of Gabbro's, into C parameters that hold their
    types, establish the callee's locals relation under the map that is its
    parameter list. -/
theorem argsTo_of : ∀ {τs : List Ty} (args : Args D Γ Λ τs) (cs : List CX)
    (ps : List (Nat × CTy)), argsOk X.EL K args cs ps = true → (ps.map Prod.fst).Nodup →
    ArgsTo X K args cs ps ⟨ps.map Prod.fst, [], []⟩
  | _, .nil, cs, ps, h, _ => by
      simp only [argsOk, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨hc, hp⟩ := h
      subst hc hp
      intro σ st ρG ρC _ _
      refine ⟨[], st, fun _ => .undef, rfl, SameML.refl st, rfl, ?_, ?_, ?_⟩
      · intro τ x; exact nomatch x
      · intro q hq; exact absurd hq List.not_mem_nil
      · intro q hq; exact absurd hq List.not_mem_nil
  | _, .cons (τ := τ) e rest, [], _, h, _ => by simp [argsOk] at h
  | _, .cons _ _, _ :: _, [], h, _ => by simp [argsOk] at h
  | _, .cons (τ := τ) e rest, ce :: cs, (x, τc) :: ps, h, hnd => by
      simp only [argsOk, Bool.and_eq_true] at h
      obtain ⟨⟨he, hd⟩, hrest⟩ := h
      have hnd' : (ps.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      have hx : x ∉ ps.map Prod.fst := (List.nodup_cons.mp hnd).1
      have hlen := argsOk_len X K rest cs ps hrest
      intro σ st ρG ρC hc hr
      obtain ⟨v, st1, h1, hv, hc1⟩ := (exOk_sound X K e ce he).run X K hc hr
      have hs1 := ev_same X.EL.lay X.orc X.fr ce st ρC v st1 h1
      obtain ⟨vs, st2, ρ1, h2, hs2, hb, hrel⟩ :=
        argsTo_of rest cs ps hrest hnd' σ st1 ρG ρC hc1 hr
      refine ⟨v :: vs, st2, lokUpd ρ1 x v, ?_, hs1.trans hs2, ?_, ?_⟩
      · simp only [evArgs, h1, h2]
      · show (match convV τc v, bindParams ps vs with
          | some v', some ρ => some (lokUpd ρ x v')
          | _, _ => none) = _
        rw [convV_of_valCorr hv hd, hb]
      · refine ⟨?_, fun q hq => absurd hq List.not_mem_nil, fun q hq => absurd hq List.not_mem_nil⟩
        intro τ' y
        cases y with
        | hier =>
            show ValCorr X.EL τ (eval σ e σ ρG) (lokUpd ρ1 x v x)
            simp only [lokUpd, if_pos]
            exact hv
        | dort y =>
            show ValCorr X.EL τ' ((evalArgs σ rest σ ρG).get y)
              (lokUpd ρ1 x v ((x :: ps.map Prod.fst).getD (y.idx + 1) 0))
            have hy : y.idx < (ps.map Prod.fst).length := by
              rw [List.length_map, hlen]; exact Var.idx_lt y
            have hne : (x :: ps.map Prod.fst).getD (y.idx + 1) 0 ≠ x := by
              intro heq
              apply hx
              rw [← heq]
              show (ps.map Prod.fst).getD y.idx 0 ∈ ps.map Prod.fst
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy]
              exact List.getElem_mem _
            simp only [lokUpd]
            rw [if_neg hne]
            exact hrel.1 τ' y

end Sound

/-! ## 3. Soundness, statement by statement and body by body -/

section SoundS

variable (X : TVCtx D) (m : Nat) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- M2 through ANY pointer form (the named object, a parameter, a pointer
    variable) against Gabbro's store to the table (`assignSlot`). -/
theorem scorr_assignSlotVia {V : Vertrag D} {l : Bool} {cp : CX} {t : D.Tab}
    (hp : PtrTo X K cp t) (f : D.Feld t) (hgt : D.geist t = false)
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)} {ci ce : CX}
    (hw : V.schreibt t = true) (hL : darf D t Λ) (hi : ExprCorr X K ci i)
    (he : ExprCorr X K ce e) :
    StmtCorr X m K (Stmt.assignSlot (l := l) t f i e hw hL)
      (.store (.slotA cp ci (X.EL.trec t).count (X.EL.trec t).ssize
        ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f) ce) := by
  intro σ st ρG ρC hc hr _
  obtain ⟨st', hx, hc'⟩ := slotStore_exec X K hp f hgt hi he Λ
    ((corrW_lese _ _ _ _ _).mpr hc : corrW X.EL (σ.lese Λ (i.orte ++ e.orte)) st) hr
  exact ⟨_, hx, st', ρC, rfl, hc', hr⟩

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D)

/-- The callee relations the certificate's calls rest on: every certified
    function, at the context's call meanings. -/
def AlleRufe (X : TVCtx D) (fnum : D.Fn → Nat) (c : KCert D) : Prop :=
  ∀ (g : D.Fn) (k : KFun D), c[fnum g]? = some k →
    FnCorr X.EL X.R X.CR g (fnum g) k.params k.lay

/-- **Soundness of the FLAT statement check.** Stated over every context,
    every locals map and every loop label, because `blOk` reaches it at
    the contexts of the arms and bodies it descends into. -/
theorem stOk0_sound (hF : AlleRufe X fnum c) :
    ∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
      (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow),
      stOk0 X.EL fnum c K₀ s r = true → StmtCorr X mm K₀ s (growRow r) := by
  intro mm V l Γ₀ Λ₀ Λ₁ K₀ s r h
  cases s with
  | assignDurch p t ht f i e hw hL =>
      cases r with
      | storeSlot kp ci n ss off τc ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K₀ hs
          subst hn hss hoff hτ
          exact scorr_assignDurch X K₀ mm ht hp f hg hw hL (exOk_sound X K₀ i ci hi)
            (exOk_sound X K₀ e ce he)
      | storeNamed tn ci n ss off τc ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K₀ hs
          subst hn hss hoff hτ
          exact scorr_assignDurch X K₀ mm ht hp f hg hw hL (exOk_sound X K₀ i ci hi)
            (exOk_sound X K₀ e ce he)
      | _ => exact absurd h (by simp [stOk0])
  | assignSlot t f i e hw hL =>
      cases r with
      | storeSlot kp ci n ss off τc ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K₀ hs
          subst hn hss hoff hτ
          exact scorr_assignSlotVia X mm K₀ hp f hg hw hL (exOk_sound X K₀ i ci hi)
            (exOk_sound X K₀ e ce he)
      | storeNamed tn ci n ss off τc ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨hs, hi⟩, he⟩ := h
          obtain ⟨hp, hn, hss, hoff, hτ, hg⟩ := slotOk_sound X K₀ hs
          subst hn hss hoff hτ
          exact scorr_assignSlotVia X mm K₀ hp f hg hw hL (exOk_sound X K₀ i ci hi)
            (exOk_sound X K₀ e ce he)
      | _ => exact absurd h (by simp [stOk0])
  | assignVar x e =>
      cases r with
      | setVar k τc ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨⟨hK, hk⟩, hd⟩, he⟩ := h
          have hk' : k = K₀.loc x := of_decide_eq_true hk
          subst hk'
          exact scorr_assignVar X mm K₀ hK x (exOk_sound X K₀ e ce he) hd
      | setOp k τc op t ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨⟨hK, hk⟩, hd⟩, he⟩ := h
          have hk' : k = K₀.loc x := of_decide_eq_true hk
          subst hk'
          exact scorr_assignVar X mm K₀ hK x (exOk_sound X K₀ e _ he) hd
      | _ => exact absurd h (by simp [stOk0])
  | assignGlob g e hw hL =>
      cases r with
      | storeGlob gn τc ce =>
          simp only [stOk0, Bool.and_eq_true, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨⟨hn, hτ⟩, hgg⟩, hat⟩, he⟩ := h
          have hn' : gn = X.EL.gnr g := of_decide_eq_true hn
          have hτ' : τc = X.EL.gty g := of_decide_eq_true hτ
          subst hn'
          subst hτ'
          exact scorr_assignGlob X mm K₀ g hgg hat hw hL (exOk_sound X K₀ e ce he)
      | _ => exact absurd h (by simp [stOk0])
  | call g args hp hr =>
      cases r with
      | call fc cargs dst =>
          cases dst with
          | some _ => exact absurd h (by simp [stOk0])
          | none =>
              simp only [stOk0, Bool.and_eq_true] at h
              obtain ⟨hfc, hk⟩ := h
              have hfc' : fc = fnum g := of_decide_eq_true hfc
              subst hfc'
              cases hc : c[fnum g]? with
              | none => rw [hc] at hk; exact absurd hk (by simp)
              | some k =>
                  rw [hc] at hk
                  simp only [Bool.and_eq_true] at hk
                  obtain ⟨hmap, ha⟩ := hk
                  simp only [callMapOk, Bool.and_eq_true, List.isEmpty_iff] at hmap
                  obtain ⟨⟨⟨hvm, hpp⟩, hks⟩, hnd⟩ := hmap
                  have hlay : (k.lay : CEnvLay D (D.params g)) = ⟨k.params.map Prod.fst, [], []⟩ := by
                    simp only [KFun.lay, of_decide_eq_true hvm, hpp, hks]
                  have hFk := hF g k hc
                  rw [hlay] at hFk
                  exact scorr_call X K₀ mm g args hp hr hFk
                    (argsTo_of X K₀ args cargs k.params ha (of_decide_eq_true hnd))
      | _ => exact absurd h (by simp [stOk0])
  | _ => exact absurd h (by simp [stOk0])

/-- **Soundness of the two staged checks, in one induction.** The two
    halves are proved at the SAME fuel, but not symmetrically: the
    statement half at `n + 1` uses only the block half at `n` (an `if`
    row is strictly heavier than its arms), and the block half at `n + 1`
    then uses the statement half at `n + 1` for its head row and itself
    at `n` for the tail. Nothing new is assumed: an `if` row ends in
    `scorr_ite`, a loop header in `scorr_traverse`, a call with a
    destination in `bsem_bindCall`, every other row in `stOk0_sound`. -/
theorem stOkBl_sound (hF : AlleRufe X fnum c) : ∀ (n : Nat),
    (∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n →
        stOk X.EL fnum c K₀ s r = true → StmtCorr X mm K₀ s (growRow r)) ∧
    (∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (b : Block D V l Γ₀ Λ₀ Λ₁) (rs : List GRow), rowsSize rs ≤ n →
        blOk X.EL fnum c K₀ b rs = true → BlockCorr X mm K₀ b (growsCS rs .skip)) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro mm V l Γ₀ Λ₀ Λ₁ K₀ s r hn _
        have := rowSize_pos r
        omega
      · intro mm V l Γ₀ Λ₀ Λ₁ K₀ b rs hn h
        have hrs : rs = [] := rowsSize_nil rs (by omega)
        subst hrs
        cases b with
        | nil => exact BlockCorr.nil
        | _ => exact absurd h (by simp [blOk])
  | succ n ih =>
      have h1 : ∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
          (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n + 1 →
          stOk X.EL fnum c K₀ s r = true → StmtCorr X mm K₀ s (growRow r) := by
        intro mm V l Γ₀ Λ₀ Λ₁ K₀ s r hn h
        cases r with
        | ite cc tRows eRows =>
            cases s with
            | ite cnd t e =>
                simp only [stOk, Bool.and_eq_true] at h
                obtain ⟨⟨hc, hT⟩, hE⟩ := h
                simp only [rowSize] at hn
                exact scorr_ite X mm K₀ (exOk_sound X K₀ cnd cc hc)
                  (cCorr_block X mm (ih.2 mm K₀ t tRows (by omega) hT))
                  (cCorr_block X mm (ih.2 mm K₀ e eRows (by omega) hE))
            | _ => exact absurd h (by simp [stOk])
        | forTrav x ti hiC bodyRows m' =>
            cases s with
            | traverse tb inv body =>
                cases hiC with
                | lit v =>
                    simp only [stOk, Bool.and_eq_true] at h
                    obtain ⟨⟨⟨⟨⟨⟨hK, hf⟩, hv⟩, hN0⟩, hN⟩, hwb⟩, hb⟩ := h
                    simp only [rowSize] at hn
                    have hv' : v = D.count tb := of_decide_eq_true hv
                    subst hv'
                    exact scorr_traverse X mm m' K₀ hK hf tb ti (of_decide_eq_true hN0)
                      (of_decide_eq_true hN) (.lit (D.count tb)) (fun _ _ => rfl) inv body
                      (growsCS bodyRows .skip)
                      (cCorr_block X m' (ih.2 m' _ body bodyRows (by omega) hb))
                      (of_decide_eq_true hwb)
                | _ => exact absurd h (by simp [stOk])
            | _ => exact absurd h (by simp [stOk])
        | _ => exact stOk0_sound X fnum c hF mm K₀ s _ h
      refine ⟨h1, ?_⟩
      intro mm V l Γ₀ Λ₀ Λ₁ K₀ b rs hn h
      cases rs with
      | nil =>
          cases b with
          | nil => exact BlockCorr.nil
          | _ => exact absurd h (by simp [blOk])
      | cons r rs' =>
          simp only [rowsSize] at hn
          have hpos := rowSize_pos r
          have hrs : rowsSize rs' ≤ n := by omega
          cases r with
          | void x =>
              simp only [blOk, Bool.and_eq_true] at h
              obtain ⟨hv, hrest⟩ := h
              obtain ⟨⟨τ, v⟩, -, hl⟩ := List.any_eq_true.mp hv
              have hl' : K₀.loc v = x := of_decide_eq_true hl
              subst hl'
              exact BlockCorr.pre (ecorr_var X K₀ (Λ := Λ₀) v) (ih.2 mm K₀ b rs' hrs hrest)
          | bindLet y τc ce =>
              cases b with
              | bind e rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  obtain ⟨⟨⟨⟨hK, hf⟩, hd⟩, he⟩, hrest⟩ := h
                  exact BlockCorr.bind hK hf (exOk_sound X K₀ e ce he) hd
                    (ih.2 mm _ rest rs' hrs hrest)
              | _ => exact absurd h (by simp [blOk])
          | call fc cargs dst =>
              cases dst with
              | none =>
                  cases b with
                  | cons s rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      exact BlockCorr.cons (h1 mm K₀ s _ (by omega) h.1)
                        (ih.2 mm K₀ rest rs' hrs h.2)
                  | _ => exact absurd h (by simp [blOk])
              | some q =>
                  obtain ⟨y, τc⟩ := q
                  cases b with
                  | bindCall g args heq hp hrp rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      obtain ⟨⟨⟨⟨⟨hfc, hK⟩, hf⟩, hd⟩, hk⟩, hrest⟩ := h
                      have hfc' : fc = fnum g := of_decide_eq_true hfc
                      subst hfc'
                      cases hc : c[fnum g]? with
                      | none => rw [hc] at hk; exact absurd hk (by simp)
                      | some k =>
                          rw [hc] at hk
                          simp only [Bool.and_eq_true] at hk
                          obtain ⟨hmap, ha⟩ := hk
                          simp only [callMapOk, Bool.and_eq_true, List.isEmpty_iff] at hmap
                          obtain ⟨⟨⟨hvm, hpp⟩, hks⟩, hnd⟩ := hmap
                          have hlay : (k.lay : CEnvLay D (D.params g)) =
                              ⟨k.params.map Prod.fst, [], []⟩ := by
                            simp only [KFun.lay, of_decide_eq_true hvm, hpp, hks]
                          have hFk := hF g k hc
                          rw [hlay] at hFk
                          exact BlockCorr.sem (bsem_bindCall X K₀ mm g args heq hp hrp rest hFk
                            (argsTo_of X K₀ args cargs k.params ha (of_decide_eq_true hnd))
                            hK hf hd (cCorr_block X mm (ih.2 mm _ rest rs' hrs hrest)))
                  | _ => exact absurd h (by simp [blOk])
          | _ =>
              cases b with
              | cons s rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  exact BlockCorr.cons (h1 mm K₀ s _ (by omega) h.1)
                    (ih.2 mm K₀ rest rs' hrs h.2)
              | _ => exact absurd h (by simp [blOk])

/-- **Soundness of the statement check** -- the statement it had before the
    block rows entered, unchanged. -/
theorem stOk_sound (hF : AlleRufe X fnum c) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ') (r : GRow), stOk X.EL fnum c K s r = true →
      StmtCorr X m K s (growRow r) :=
  fun s r h => (stOkBl_sound X fnum c hF (rowSize r)).1 m K s r (Nat.le_refl _) h

/-- **Soundness of the block check.** -/
theorem blOk_sound (hF : AlleRufe X fnum c) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} :
    ∀ (b : Block D V l Γ Λ Λ') (rs : List GRow), blOk X.EL fnum c K b rs = true →
      BlockCorr X m K b (growsCS rs .skip) :=
  fun b rs h => (stOkBl_sound X fnum c hF (rowsSize rs)).2 m K b rs (Nat.le_refl _) h

/-- **Soundness of the body check**: the rows elaborate to C that the Gabbro
    body corresponds to (`EndCorr`). -/
theorem enOk_sound (hF : AlleRufe X fnum c) (top : Bool) {V : Vertrag D} {l : Bool} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ),
      enOk X.EL fnum c top rs K b = true → EndCorr X m top K b (endCS rs) := by
  intro rs
  induction rs with
  | nil =>
      intro Γ Λ K b h
      cases b with
      | ret r hΛ =>
          simp only [enOk, Bool.and_eq_true] at h
          exact EndCorr.retEnd hΛ h.1 (of_decide_eq_true h.2)
      | _ => exact absurd h (by simp [enOk])
  | cons r rs ih =>
      intro Γ Λ K b h
      cases r with
      | void x =>
          simp only [enOk, Bool.and_eq_true] at h
          obtain ⟨hv, hrest⟩ := h
          obtain ⟨⟨τ, v⟩, -, hl⟩ := List.any_eq_true.mp hv
          have hl' : K.loc v = x := of_decide_eq_true hl
          subst hl'
          exact EndCorr.pre (ecorr_var X K (Λ := Λ) v) (ih K b hrest)
      | ret cr =>
          simp only [enOk, Bool.and_eq_true, List.isEmpty_iff] at h
          obtain ⟨hnil, hb⟩ := h
          subst hnil
          cases b with
          | ret e hΛ => exact EndCorr.ret hΛ (ergOk_sound X K e cr hb)
          | _ => exact absurd hb (by simp)
      | bindLet x τc ce =>
          cases b with
          | bind e rest =>
              simp only [enOk, Bool.and_eq_true] at h
              obtain ⟨⟨⟨⟨hK, hf⟩, hd⟩, he⟩, hrest⟩ := h
              exact EndCorr.bind hK hf (exOk_sound X K e ce he) hd (ih _ rest hrest)
          | _ => exact absurd h (by simp [enOk])
      | _ =>
          cases b with
          | cons s rest =>
              simp only [enOk, Bool.and_eq_true] at h
              exact EndCorr.cons (stOk_sound X m K fnum c hF s _ h.1) (ih K rest h.2)
          | _ => exact absurd h (by simp [enOk])

end SoundS

/-! ## 4. Every call depth: the callee relation of every certified function -/

section Tiefe

theorem korrOk_fn {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true)
    (g : D.Fn) : ∃ k, c[fnum g]? = some k ∧ enOk EL fnum c true k.rows k.lay (P.rumpf g) = true := by
  have h := List.all_eq_true.mp hc g (hvoll g)
  cases hk : c[fnum g]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k => rw [hk] at h; exact ⟨k, rfl, h⟩

/-- **THE SOUNDNESS OF THE CHECK, AT EVERY DEPTH**: a certificate that
    checks gives, for every function, every call depth `n` and every budget,
    the callee relation between Gabbro's call `rufAt P O passes n` and the
    C call `CallAt … (kProg c) n` of the unit it elaborates to -- whatever
    the device oracle `orc` and the foreign-call meaning `XR`. -/
theorem korrOk_fnCorr {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true)
    (orc : DevOrc) (XR : CCallR) (O : Orakel D) (passes : Nat) :
    ∀ (n : Nat) (g : D.Fn) (k : KFun D), c[fnum g]? = some k →
      FnCorr EL (rufAt P O passes n) (CallAt EL.lay orc XR (kProg c) n) g (fnum g) k.params k.lay := by
  intro n
  induction n with
  | zero =>
      intro g k _ σ st ρG vs ρ0 _ _ _ hnf
      exact absurd hnf (by simp [rufAt, RufAusgang.istFehler])
  | succ n ih =>
      intro g k hk
      obtain ⟨k', hk', hok⟩ := korrOk_fn hvoll hc g
      rw [hk] at hk'
      cases hk'
      let X : TVCtx D := ⟨EL, orc, n + 1, CallAt EL.lay orc XR (kProg c) n, XR, O, passes,
        rufAt P O passes n⟩
      have hF : AlleRufe X fnum c := fun g' k'' hk'' => ih g' k'' hk''
      have hPr : kProg c (fnum g) = some { params := k.params, locals := k.locals, body := endCS k.rows } := by
        simp only [kProg, hk, Option.map_some]
      exact cCorr_ruf EL orc XR P O passes n (kProg c) g (fnum g) _ hPr k.lay 0
        (cCorr_end X 0 true (enOk_sound X 0 fnum c hF true k.rows k.lay (P.rumpf g) hok))

/-- **EVERY RUN**: under a checking certificate, from a C state related to
    the Gabbro world and C arguments related to the Gabbro arguments, when the
    Gabbro call at depth `n` ends in no model error, the C call has a run, and
    -- the C semantics being deterministic -- EVERY run of it ends related to
    the Gabbro outcome. -/
theorem korrOk_jeder_lauf {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true)
    (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional) (O : Orakel D) (passes n : Nat)
    (g : D.Fn) (k : KFun D) (hk : c[fnum g]? = some k) (σ : World D) (st : CSt)
    (ρG : Env D (D.params g)) (vs : List CVal) (ρ0 : CLok) (hw : corrW EL σ st)
    (hb : bindParams k.params vs = some ρ0) (hr : EnvRel EL k.lay ρG ρ0)
    (hnf : (rufAt P O passes n g σ ρG).istFehler = false) :
    (∃ st' rv, CallAt EL.lay orc XR (kProg c) n (fnum g) st vs st' rv) ∧
      ∀ st' rv, CallAt EL.lay orc XR (kProg c) n (fnum g) st vs st' rv →
        RufOut EL (rufAt P O passes n g σ ρG) st' rv := by
  obtain ⟨st1, rv1, hC1, hO1⟩ := korrOk_fnCorr hvoll hc orc XR O passes n g k hk σ st ρG vs ρ0 hw hb hr hnf
  refine ⟨⟨st1, rv1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional EL.lay orc XR hXR (kProg c) n (fnum g) st vs st1 rv1 st' rv hC1 hC
  subst e1
  subst e2
  exact hO1

end Tiefe

/-
CUTS -- what this file does not do, by name.
- COVERED FORMS: the statement and expression families listed in the header.
  Not covered (the Bool is `false`, a refusal), with the reason for each:
  * `traverse` (`GRow.forTrav`) is in, but only with a CONSTANT bound:
    `scorr_traverse` wants `ev hiC = D.count tb` at EVERY C state, and
    the only C expression this file can decide that of is a literal.
    A header that computes its bound is a refusal, not an admission.
    The loop's own budget `m'` is data of the row and not checked: it is
    the `forC` step count of the C semantics, and the correspondence
    holds at whatever it is.
  * `retry`, `forever` and the other block statements (`locks`,
    `breaking`, `onOption`, `onTag`, `onGrund`) have rows in neither
    `GRow` nor the printer, so `blOk` never meets them; `stOk0` refuses
    their statements.
  * `let x = f(…)` (`bindCall`) is a `Block` constructor and NOT an
    `Endblock` one, so it is checked in `blOk` and nowhere else: a body
    whose TOP level binds a call's answer is not expressible in the model
    at all, and inside an `if` arm or a loop body it is. The arm ends in
    `bsem_bindCall`.
  * `!=` (`.cmp .ne`): Gabbro's `Zucker.ne a b` is `nicht (eq a b)`, so the
    arm would have to look THROUGH the negation at its operands, and the
    soundness proof would need the induction hypotheses of those operands
    in an arm whose pattern is only `nicht a`. `>` and `>=` need no such
    step (`Zucker.gt`/`ge` are `lt`/`le` with the operands swapped, and the
    swapped C operator is the arm's second row shape). The printer refuses
    `!=` today, so no certificate can carry the row either.
  * `(T)(e)` (`CX.cast`) as a wrapper around an accepted expression: the
    recursion would shrink the C side while the Gabbro side stands still,
    which is neither argument's structural descent. `ecorr_cast` is proved.
  * An `_Atomic` global, read (`CX.ald`) or stored (`CS.astore`): both are
    observations, and `GRow` has no atomic row. `ecorr_globAtomar` and
    `scorr_assignGlobAtomar` are proved.
  * `neg`, `leseBytes`, floats, sums, options, reasons, quantifiers,
    `locks`, `forever`, `retry`, device and foreign forms: no arm, and for
    the floats no `ecorr_*` at all (`CX` has no float operand a `GRow`
    could carry).
- A call's callee map must be its C parameter list (`callMapOk`): the
  exporter's map. The index-fixed `refD` maps (`ks`) of lanes 164/165 are
  not accepted at call sites; they still check as top-level maps.
- The Gabbro call is allowed to end in a model error (a failed `requires`,
  `ensures`, invariant, the call-depth bound `abstieg`, a hardware answer):
  the correspondence then claims nothing (`FnCorr` is conditional on
  `istFehler = false`). That the model's call ends without error is the
  model judgement's business (the goal theorem), not the certificate's.
-/

#print axioms Gabbro.Grammatik.ptrOk_sound
#print axioms Gabbro.Grammatik.ecorr_geSwap
#print axioms Gabbro.Grammatik.exOk_sound
#print axioms Gabbro.Grammatik.argsTo_of
#print axioms Gabbro.Grammatik.stOk0_sound
#print axioms Gabbro.Grammatik.stOkBl_sound
#print axioms Gabbro.Grammatik.stOk_sound
#print axioms Gabbro.Grammatik.blOk_sound
#print axioms Gabbro.Grammatik.enOk_sound
#print axioms Gabbro.Grammatik.korrOk_fnCorr
#print axioms Gabbro.Grammatik.korrOk_jeder_lauf

end Gabbro.Grammatik
