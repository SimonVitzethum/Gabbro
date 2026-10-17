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

  THE DEVICE 2026-09-16 (`OPUS-BERICHT-GERAET.md`). Gabbro exists for an
  operating system, and until this day the certificate refused every form
  that can end a call in the model's `Hardware` class -- which is why no
  driver-shaped program could be certified. THREE of the five are carried
  now: the register STORE (`GRow.storeReg`, `R = e;`), the register READ
  (`GRow.loadReg`, `let x = R;`) and the CHECKED read (`GRow.loadRegElse`,
  `let x = R else (c) { return e; }`), whose `requires … else` channel is the
  interesting one: **a broken device promise becomes a BRANCH in the program
  rather than a stop**, and that branch has to correspond like any other row.
  What no certificate can decide stands in ONE named premise, `GerAnnahme`
  (§1c), and what a device chain then claims is exactly this: *if the profile
  holds and the register answers inside its declared type, every run of the
  emitted C corresponds.* NOTHING about the device is claimed.

  The device rows need to know WHICH register an address belongs to, and that
  is the emitter's layout and not the program text, so `korrOk` carries a LAST
  parameter `GT : GerTafel D` -- plain data, no proof field, with a default of
  the EMPTY table under which every device row is refused. Every call written
  before this day is unchanged, character for character, and decides what it
  decided before. `awaits`, the axiom call and `forever` stay REFUSED, by name
  (CUTS).

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
import Grammatik.Korrespondenz.Allgemein.Korrespondenz
import Grammatik.CBackend.Formen.CFormenDet
import Grammatik.Logik.Ruf.RufOhneHardware

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0a. The device table -- what the emitter put where at a register

    The three device rows (`GRow.storeReg`, `.loadReg`, `.loadRegElse`) are
    the ONLY rows whose meaning the check cannot read off the row alone: a
    volatile access needs to know WHICH register it is, and that is the
    emitter's layout, not the program text. The table below is that layout as
    PLAIN DATA -- no proof field, nothing the check has to trust. What must be
    TRUE of it is the hardware profile `GerAnnahme` (§6), a PREMISE of the
    soundness theorem and never part of the Bool.

    **The empty table is the default**, and it has `ein := false`: every device
    row is refused under it. A certificate that names no device is therefore
    checked by exactly the `korrOk` of before, character for character, and the
    two closed chains pass `GT` at all. -/
structure GerTafel (D : Deklaration) where
  /-- Are device rows admitted at all? `false` in the empty table. -/
  ein : Bool := false
  /-- The C block number of the device window the register lives in. -/
  dnr : D.Reg → Nat := fun _ => 0
  /-- The window's declared base address -- the `(volatile uint8_t
      *)(uintptr_t)BASE` spelling of the handle. -/
  basis : D.Reg → Int := fun _ => 0
  /-- The register's byte offset inside the window (`@0x102`). -/
  off : D.Reg → Nat := fun _ => 0
  /-- The width of the register cell (`uint16_t` …). -/
  wid : D.Reg → CWidth := fun _ => .w8
  /-- The C local holding the device HANDLE, for the emitter's own spelling
      `d->basis + K` (`geraetelesung`, emit.rs). -/
  hdl : D.Reg → Nat := fun _ => 0
  /-- The byte offset of the handle's `basis` member. -/
  hoff : D.Reg → Nat := fun _ => 0
  /-- Is the HANDLE spelling `d->basis + K` admitted? It is the one the
      emitter writes (`geraetelesung`, emit.rs), and it costs a premise the
      direct-base spelling does not: that the handle local carries the
      window's base (`GerAnnahme.adr`, whose direct-base half is the theorem
      `gerAdr_devH`). Default: no. -/
  griff : Bool := false

/-- **THE REGISTER'S ADDRESS, decided.** Two spellings are admitted, and they
    are the two the emitter writes:

    * `(volatile uint8_t *)(uintptr_t)BASE + K` -- the window's declared base
      (`CX.devH`), whose evaluation is a THEOREM (`ev_devReg`, CFormenH.lean);
    * `d->basis + K` -- the handle the emitter actually prints at a `device`
      access (`geraetelesung`), whose evaluation is the NAMED assumption
      `GerAnnahme.adr`: that the handle local holds the window's base.

    Every other C expression is a refusal. -/
def regAdrOk (GT : GerTafel D) (cp : CX) (r : D.Reg) : Bool :=
  GT.ein &&
    (decide (cp = .padd (.devH (GT.dnr r) (GT.basis r)) (.lit (GT.off r))) ||
      (GT.griff &&
        decide (cp = .padd (.ld (.fld (.var (GT.hdl r)) (GT.hoff r)) .ptr) (.lit (GT.off r)))))

/-- An accepted address means the device table is SWITCHED ON. -/
theorem regAdrOk_ein {GT : GerTafel D} {cp : CX} {r : D.Reg}
    (h : regAdrOk GT cp r = true) : GT.ein = true := by
  simp only [regAdrOk, Bool.and_eq_true] at h
  exact h.1

/-- **WITHOUT THE HANDLE SPELLING, THE ADDRESS IS FIXED.** `GerAnnahme.adr`
    is then a THEOREM (`gerAdr_devH`) and not an assumption: the accepted
    address is the direct-base one, and `ev_devReg` settles it. -/
theorem regAdrOk_devH {GT : GerTafel D} (hg : GT.griff = false) {cp : CX} {r : D.Reg}
    (h : regAdrOk GT cp r = true) :
    cp = .padd (.devH (GT.dnr r) (GT.basis r)) (.lit (GT.off r)) := by
  simp only [regAdrOk, hg, Bool.false_and, Bool.or_false, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h.2

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
  | τ :: Γ => ⟨τ, .here⟩ :: (varsOf Γ).map fun p => ⟨p.1, .there p.2⟩

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
  -- A range widening has no C text of its own (`exOk e c`), or the emitter wrote it out as the
  -- explicit conversion `(T)(e)` (`u64(a)`, the implicit one made explicit): then `T` must hold the
  -- operand's range, so the cast keeps the number (`ecorr_cast`). The recursion is on the Gabbro
  -- operand `e`, a subterm, so the check stays structural.
  | .widen (lo := lo) (hi := hi) _ _ e, c =>
      exOk e c || (match c with
        | .cast t c' => decide (t.holds lo hi) && exOk e c'
        | _ => false)
  | .slot t f i _, c => match c with
    | .ld (.slotA b ci n ss off) τc => slotOk EL K b n ss off τc t f && exOk i ci
    | _ => false
  | .thru _ t _ f i _, c => match c with
    | .ld (.slotA b ci n ss off) τc => slotOk EL K b n ss off τc t f && exOk i ci
    | _ => false
  | .ptrOf t _ _ _, c => ptrOk EL K c t
  | .tru, c => match c with
    | .lit m => decide (m = 1)
    | _ => false
  | .fls, c => match c with
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
  | .and a b, c => match c with
    | .land ca cb => exOk a ca && exOk b cb
    | _ => false
  | .or a b, c => match c with
    | .lor ca cb => exOk a ca && exOk b cb
    | _ => false
  | .not a, c => match c with
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
  | _, .empty, none => true
  | some τ, .val e, some (τc, ce) => declOk τ τc && exOk EL K e ce
  | _, _, _ => false

/-- **THE `else` OF A CHECKED REGISTER READ**: a `return`, and nothing else.
    `Block.regLiesElse`'s `sonst` is a whole `Endblock`, and a row that
    carried one would need the terminal-block check inside the block check --
    a second recursion through a second type. The narrowing is NAMED: the
    admitted `else` is the driver's `return Geraetelug::ZuTief;`, the shape
    the one corpus instance writes (`beispiele/44-register-einmal-lesen.gab`).
    Any other `else` is a refusal. -/
def sonstOk {V : Vertrag D} {l : Bool} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Option (CTy × CX) → Bool
  | .ret e _, cr => ergOk EL K e cr
  | _, _ => false

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
def stOk0 {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ)
    (s0 : Stmt D V l Γ Λ Λ') (r0 : GRow) (GT : GerTafel D := {}) : Bool :=
  match s0, r0 with
  | .assignThru _ t _ f i e _ _, r => match r with
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
  -- `R = e;` -- THE DEVICE STORE (H10). The row's address must be the
  -- emitter's for THIS register and the cell width the declared one; the
  -- value is any covered expression. `Stmt.regSchreib` is `hardwareFrei`
  -- already (a write has no answer that can fail), so this arm costs the
  -- `hardwareFrei` reading of the check NOTHING.
  | .regWrite rg _ e, r => match r with
    | .storeReg cp w ce =>
        regAdrOk GT cp rg && decide (w = GT.wid rg) && exOk EL K e ce
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
    (s : Stmt D V l Γ Λ Λ') (r0 : GRow) (GT : GerTafel D := {}) : Bool :=
  match r0 with
  | .ite cc tRows eRows => (match s with
      | .ite cnd t e => exOk EL K cnd cc && blOk K t tRows GT && blOk K e eRows GT
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
            blOk (K.push (.index (D.count tb)) x) body bodyRows GT
      | _, _ => false)
  | r => stOk0 EL fnum c K s r GT

/-- **BLOCKS** (`Block`: an `if` arm or a loop body): row by row, the same
    reading `enOk` gives a terminal block -- `(void)x;`, `let`, `let` of a
    call, and every other row against the block's head statement. A block
    does not end in a `return`, so there is no `ret` row here; the list
    ends with the block (`Block.nil`). -/
def blOk {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (K : CEnvLay D Γ)
    (b : Block D V l Γ Λ Λ') (rs0 : List GRow) (GT : GerTafel D := {}) : Bool :=
  match rs0 with
  | [] => (match b with
      | .nil => true
      | _ => false)
  | r :: rs => match r with
      | .void x => voidOk K x && blOk K b rs GT
      | .bindLet y τc ce => (match b with
          | .bind (τ := τ) e rest =>
              K.okB && K.freshB y && declOk τ τc && exOk EL K e ce &&
                blOk (K.push τ y) rest rs GT
          | _ => false)
      -- `T x = (*(volatile T *)(cp));` -- THE DEVICE READ (H9). The answer
      -- is bound to a fresh C local of a type the register's fits.
      | .loadReg y τc cp w => (match b with
          | .regRead (r := rg) _ rest =>
              GT.ein && K.okB && K.freshB y && tyFits (D.rtyp rg) τc &&
                regAdrOk GT cp rg && decide (w = GT.wid rg) &&
                blOk (K.push (D.rtyp rg) y) rest rs GT
          | _ => false)
      -- `T x = (*(volatile T *)(cp)); if (!(c)) { return e; }` -- THE
      -- CHECKED device read. The declared promise is a CONDITION of the
      -- program, and its failure a BRANCH: `sonstOk` decides that branch
      -- against the emitted `return`.
      | .loadRegElse y τc cp w cc cr => (match b with
          | .regReadElse (r := rg) _ zusage sonst rest =>
              GT.ein && K.okB && K.freshB y && tyFits (D.rtyp rg) τc &&
                regAdrOk GT cp rg && decide (w = GT.wid rg) &&
                exOk EL (K.push (D.rtyp rg) y) zusage cc &&
                sonstOk EL K sonst cr &&
                blOk (K.push (D.rtyp rg) y) rest rs GT
          | _ => false)
      -- `T y = g(a, b);` -- the call whose ANSWER is bound. `Endblock` has
      -- no such constructor, so this row can only ever stand in a block.
      | .call fc cargs (some (y, τc)) => (match b with
          | .bindCall (τ := τ) g args _ _ _ rest =>
              decide (fc = fnum g) && K.okB && K.freshB y && declOk τ τc &&
                (match c[fnum g]? with
                  | some k => callMapOk k && argsOk EL K args cargs k.params
                  | none => false) &&
                blOk (K.push τ y) rest rs GT
          | _ => false)
      | r => (match b with
          | .cons s rest => stOk K s r GT && blOk K rest rs GT
          | _ => false)

end

/-- TERMINAL BLOCKS (a function body): row by row. `top` says the block is
    the whole body (a `void` body may fall off its end). -/
def enOk (top : Bool) {V : Vertrag D} {l : Bool} (rs0 : List GRow) {Γ : Ctx}
    {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ)
    (GT : GerTafel D := {}) : Bool :=
  match rs0, b with
  | [], b => match b with
    | .ret _ _ => top && decide (V.erg = none)
    | _ => false
  | r :: rs, b => match r with
    | .void x => voidOk K x && enOk top rs K b GT
    | .ret cr => rs.isEmpty && (match b with
        | .ret e _ => ergOk EL K e cr
        | _ => false)
    | .bindLet x τc ce => (match b with
        | .bind (τ := τ) e rest =>
            K.okB && K.freshB x && declOk τ τc && exOk EL K e ce &&
              enOk top rs (K.push τ x) rest GT
        | _ => false)
    | r => (match b with
        | .cons s rest => stOk EL fnum c K s r GT && enOk top rs K rest GT
        | _ => false)

/-- **THE CHECK**: every function of `fs` has a certified C function (number
    `fnum f`), whose rows are the emitted form of its body under its map.
    `GT` is the certificate's DEVICE TABLE; the default is the empty one, and
    under it no device row is admitted -- the check of before 2026-09-16. -/
def korrOk (P : Programm D) (fs : List D.Fn) (GT : GerTafel D := {}) : Bool :=
  fs.all fun f => match c[fnum f]? with
    | some k => enOk EL fnum c true k.rows k.lay (P.rumpf f) GT
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
  | .storeReg .. => 1
  | .loadReg .. => 1
  | .loadRegElse .. => 1
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


end Gabbro.Grammatik
