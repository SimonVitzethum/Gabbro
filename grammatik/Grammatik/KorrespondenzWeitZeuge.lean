/-
  File:      Grammatik/KorrespondenzWeitZeuge.lean
  Subject:   PROBES for the arms `korrOk` gained on 2026-09-15
             (KorrespondenzAllg.lean §1: the arithmetic, bitwise, comparison,
             boolean and global expression families, and the statements
             `x op= e;` and `g = e;`).

  WHY THIS FILE EXISTS. A sieve nobody has seen fail is a decoration, and
  every widening of a certificate is a chance to admit a wrong row. So each
  new arm gets BOTH probes over one fixture:
  * a POSITIVE probe -- the emitted form the arm is meant to accept;
  * a PLANTED DEFECT -- a row that differs from the emitted form in exactly
    the way that arm could have let through: the wrong C operator, a
    computation type too narrow for the result (the `M104` condition that
    makes C's conversions keep the Gabbro number), operands in the wrong
    order at a `>`/`>=` (where the C text says the opposite comparison),
    `INT_MIN / -1` not excluded, the wrong local, the wrong global block,
    the wrong cell type, and an `_Atomic` global taken for a plain one.

  THE FIXTURE `wD`: one table `T` of four `u32` slots, two globals -- `G`
  plain and `A` atomic, of the same C type and adjacent block numbers, so
  that "which global" and "plain or atomic" are two separate probes -- and
  one function of two `u32` parameters. The locals map is the exporter's
  (`vm = [0, 1]`).

  Everything here is `decide`: the check is a Bool, and a probe that needed
  a proof would be probing something else.
-/
import Grammatik.KorrespondenzAllg

namespace Gabbro.Grammatik.WeitZeuge

open Gabbro.Grammatik

/-! ## 1. The fixture -/

abbrev wU32 : Ty := .int 0 4294967295

/-- One table of four `u32` slots, a plain global `G` and an `_Atomic` `A`,
    one function `f(a : u32, b : u32)`. -/
def wD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 4
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => wU32
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Bool
  decGlob := inferInstance
  gtyp := fun _ => wU32
  nutzlast := fun _ => []
  atomar := fun g => g
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => nomatch m
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Empty
  sig := fun f => nomatch f
  sigNr := fun _ =>
    { params := [wU32, wU32], erg := none, gruende := 0, haelt := [],
      schreibt := fun _ => true, gschreibt := fun _ => true, konsumiert := [],
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => by simp at h

/-- `typedef struct { uint32_t v; } T_slot; static T_slot T_speicher[4];` -/
def wRec : RecLay := natLay 4 [.int false .w32]

/-- `T` is table block 0, `G` global block 0, `A` global block 1. -/
def wLay : CLayout := fun b =>
  match b with
  | .tab 0 => some { lay := wRec, kind := .plain, base := 0 }
  | .glob 0 => some { lay := scalarRec (.int false .w32), kind := .plain, base := 0 }
  | .glob 1 => some { lay := scalarRec (.int false .w32), kind := .atomic, base := 0 }
  | _ => none

def wEL : EmitLay wD where
  lay := wLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => wRec
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun _ => rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun _ f f' _ => by cases f; cases f'; rfl
  fnr_fits := fun _ _ => rfl
  gnr := fun g => cond g 1 0
  gnr_inj := fun g g' h => by
    cases g
    · cases g'
      · rfl
      · exact absurd h (by decide)
    · cases g'
      · exact absurd h (by decide)
      · rfl
  gty := fun _ => .int false .w32
  lay_glob := fun g => by cases g <;> rfl
  gty_fits := fun _ => rfl

/-- The context of `f`'s body, and the EXPORTER'S map: parameter `j` is C
    local `j`. -/
abbrev wCtx : Ctx := [wU32, wU32]

def wK : CEnvLay wD wCtx := ⟨[0, 1], [], []⟩

def x0 : Expr wD wCtx [] wU32 := .var .hier
def x1 : Expr wD wCtx [] wU32 := .var (.dort .hier)

theorem wGdarf (g : Bool) : gdarf wD g [] := fun _ hw => absurd hw List.not_mem_nil

/-- The plain global `G`. -/
abbrev wG : wD.Glob := false
/-- The `_Atomic` global `A`. -/
abbrev wA : wD.Glob := true

/-! ## 2. Expressions: every new arm, accepted and refused

    Read each pair as one sentence: the first row IS the emitted C of the
    Gabbro expression, the second differs in the one way the arm is there to
    catch. -/

/-- `true` / `false`. -/
theorem probe_wahr :
    exOk wEL wK (Expr.wahr (D := wD) (Γ := wCtx) (Λ := [])) (.lit 1) = true ∧
    exOk wEL wK (Expr.wahr (D := wD) (Γ := wCtx) (Λ := [])) (.lit 0) = false ∧
    exOk wEL wK (Expr.falsch (D := wD) (Γ := wCtx) (Λ := [])) (.lit 0) = true ∧
    exOk wEL wK (Expr.falsch (D := wD) (Γ := wCtx) (Λ := [])) (.lit 1) = false := by
  decide

/-- `a + b`: the sum of two `u32` needs a 64-bit computation type; `uint32_t`
    would wrap where the Gabbro value does not, and the arm refuses it. -/
theorem probe_add :
    exOk wEL wK (Expr.add x0 x1) (.bin .add CIT.u64 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.add x0 x1) (.bin .add CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.add x0 x1) (.bin .sub CIT.u64 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.add x0 x1) (.bin .add CIT.u64 (.var 1) (.var 0)) = false := by
  decide

/-- `a - b`: the difference is negative for some operands, so the type must
    be signed. -/
theorem probe_sub :
    exOk wEL wK (Expr.sub x0 x1) (.bin .sub CIT.i64 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.sub x0 x1) (.bin .sub CIT.u64 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.sub x0 x1) (.bin .add CIT.i64 (.var 0) (.var 1)) = false := by
  decide

/-- `a * b`. -/
theorem probe_mul :
    exOk wEL wK (Expr.mul x0 x1) (.bin .mul CIT.u64 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.mul x0 x1) (.bin .mul CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.mul x0 x1) (.bin .add CIT.u64 (.var 0) (.var 1)) = false := by
  decide

/-- `a / 3` and `a % 3` over a non-negative dividend: C's truncation is
    Gabbro's, and `/` and `%` are two different C operators. -/
theorem probe_div_rem :
    exOk wEL wK (Expr.div (by decide) (by decide) x0 (.lit 3))
      (.bin .div CIT.u32 (.var 0) (.lit 3)) = true ∧
    exOk wEL wK (Expr.div (by decide) (by decide) x0 (.lit 3))
      (.bin .mod CIT.u32 (.var 0) (.lit 3)) = false ∧
    exOk wEL wK (Expr.div (by decide) (by decide) x0 (.lit 3))
      (.bin .div CIT.u8 (.var 0) (.lit 3)) = false ∧
    exOk wEL wK (Expr.rem (by decide) (by decide) x0 (.lit 3))
      (.bin .mod CIT.u32 (.var 0) (.lit 3)) = true ∧
    exOk wEL wK (Expr.rem (by decide) (by decide) x0 (.lit 3))
      (.bin .div CIT.u32 (.var 0) (.lit 3)) = false := by
  decide

/-- A full-range `int64_t` dividend: `INT_MIN / -1` is undefined in C11
    (6.5.5p6), and the arm refuses the signed division that would reach it
    -- it accepts the same expression at a dividend that cannot be
    `INT64_MIN`. -/
def i64Voll : Expr wD wCtx [] (.int (-9223372036854775808) 9223372036854775807) :=
  .weiter (by decide) (by decide) (Expr.lit 0)

def i64Eng : Expr wD wCtx [] (.int (-9223372036854775807) 9223372036854775807) :=
  .weiter (by decide) (by decide) (Expr.lit 0)

theorem probe_sdiv_srem :
    exOk wEL wK (Expr.sdiv (Or.inr (by decide)) i64Eng (.lit (-1)))
      (.bin .div CIT.i64 (.lit 0) (.lit (-1))) = true ∧
    exOk wEL wK (Expr.sdiv (Or.inr (by decide)) i64Voll (.lit (-1)))
      (.bin .div CIT.i64 (.lit 0) (.lit (-1))) = false ∧
    exOk wEL wK (Expr.sdiv (Or.inr (by decide)) i64Eng (.lit (-1)))
      (.bin .mod CIT.i64 (.lit 0) (.lit (-1))) = false ∧
    exOk wEL wK (Expr.srem (Or.inr (by decide)) i64Eng (.lit (-1)))
      (.bin .mod CIT.i64 (.lit 0) (.lit (-1))) = true ∧
    exOk wEL wK (Expr.srem (Or.inr (by decide)) i64Voll (.lit (-1)))
      (.bin .mod CIT.i64 (.lit 0) (.lit (-1))) = false := by
  decide

/-- `a & b`, `a | b`, `a ^ b` over `0 ..` (`M137`). -/
theorem probe_bit :
    exOk wEL wK (Expr.band (by decide) (by decide) x0 x1)
      (.bin .band CIT.u32 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.band (by decide) (by decide) x0 x1)
      (.bin .bor CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.bor 32 (by decide) (by decide) (by decide) (by decide) x0 x1)
      (.bin .bor CIT.u32 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.bor 32 (by decide) (by decide) (by decide) (by decide) x0 x1)
      (.bin .bxor CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.bxor 32 (by decide) (by decide) (by decide) (by decide) x0 x1)
      (.bin .bxor CIT.u32 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.bxor 32 (by decide) (by decide) (by decide) (by decide) x0 x1)
      (.bin .band CIT.u32 (.var 0) (.var 1)) = false := by
  decide

/-- `1 << 3` and `1 >> 3`: the shift count below the computation width, and
    the shifted result inside it. -/
theorem probe_shift :
    exOk wEL wK
      (Expr.shl (D := wD) (Γ := wCtx) (Λ := []) 8 (by decide) (by decide) (by decide)
        (by decide) (.lit 1) (.lit 3))
      (.bin .shl CIT.u32 (.lit 1) (.lit 3)) = true ∧
    exOk wEL wK
      (Expr.shl (D := wD) (Γ := wCtx) (Λ := []) 8 (by decide) (by decide) (by decide)
        (by decide) (.lit 1) (.lit 3))
      (.bin .shr CIT.u32 (.lit 1) (.lit 3)) = false ∧
    exOk wEL wK
      (Expr.shr (D := wD) (Γ := wCtx) (Λ := []) 8 (by decide) (by decide) (by decide)
        (by decide) (.lit 1) (.lit 3))
      (.bin .shr CIT.u32 (.lit 1) (.lit 3)) = true ∧
    exOk wEL wK
      (Expr.shr (D := wD) (Γ := wCtx) (Λ := []) 8 (by decide) (by decide) (by decide)
        (by decide) (.lit 1) (.lit 3))
      (.bin .shl CIT.u32 (.lit 1) (.lit 3)) = false := by
  decide

/-- `a < b` and `a <= b`, each in the two C spellings Gabbro's `Zucker`
    produces (`gt a b = lt b a`, `ge a b = le b a`). The PLANTED DEFECT is
    the swap left out: `a > b` where the Gabbro expression says `a < b` is
    the opposite comparison, and the arm refuses it. -/
theorem probe_cmp :
    exOk wEL wK (Expr.lt x0 x1) (.cmp .lt CIT.u32 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.lt x0 x1) (.cmp .gt CIT.u32 (.var 1) (.var 0)) = true ∧
    exOk wEL wK (Expr.lt x0 x1) (.cmp .gt CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.lt x0 x1) (.cmp .le CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.le x0 x1) (.cmp .le CIT.u32 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.le x0 x1) (.cmp .ge CIT.u32 (.var 1) (.var 0)) = true ∧
    exOk wEL wK (Expr.le x0 x1) (.cmp .ge CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.eq x0 x1) (.cmp .eq CIT.u32 (.var 0) (.var 1)) = true ∧
    exOk wEL wK (Expr.eq x0 x1) (.cmp .ne CIT.u32 (.var 0) (.var 1)) = false := by
  decide

/-- A comparison type that does not hold both operand ranges is refused --
    this is the signed/unsigned pitfall (`-1 < 1u`) as a sieve. -/
theorem probe_cmp_typ :
    exOk wEL wK (Expr.lt x0 x1) (.cmp .lt CIT.i32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.lt x0 x1) (.cmp .lt CIT.i64 (.var 0) (.var 1)) = true := by
  decide

/-- `a && b`, `a || b`, `!a`. -/
theorem probe_bool :
    exOk wEL wK (Expr.und (Expr.lt x0 x1) (Expr.eq x0 x1))
      (.land (.cmp .lt CIT.u32 (.var 0) (.var 1)) (.cmp .eq CIT.u32 (.var 0) (.var 1)))
      = true ∧
    exOk wEL wK (Expr.und (Expr.lt x0 x1) (Expr.eq x0 x1))
      (.lor (.cmp .lt CIT.u32 (.var 0) (.var 1)) (.cmp .eq CIT.u32 (.var 0) (.var 1)))
      = false ∧
    exOk wEL wK (Expr.oder (Expr.lt x0 x1) (Expr.eq x0 x1))
      (.lor (.cmp .lt CIT.u32 (.var 0) (.var 1)) (.cmp .eq CIT.u32 (.var 0) (.var 1)))
      = true ∧
    exOk wEL wK (Expr.oder (Expr.lt x0 x1) (Expr.eq x0 x1))
      (.land (.cmp .lt CIT.u32 (.var 0) (.var 1)) (.cmp .eq CIT.u32 (.var 0) (.var 1)))
      = false ∧
    exOk wEL wK (Expr.nicht (Expr.lt x0 x1)) (.lnot (.cmp .lt CIT.u32 (.var 0) (.var 1)))
      = true ∧
    exOk wEL wK (Expr.nicht (Expr.lt x0 x1)) (.cmp .lt CIT.u32 (.var 0) (.var 1)) = false ∧
    exOk wEL wK (Expr.nicht (Expr.lt x0 x1)) (.cmp .ge CIT.u32 (.var 0) (.var 1)) = false := by
  decide

/-- A plain file-scope scalar `G`: its own block number and its own cell
    type. `A` is `_Atomic`, so its bare name is a `seq_cst` LOAD and not the
    plain one this arm proves -- refused, in BOTH spellings. -/
theorem probe_glob :
    exOk wEL wK (Expr.glob (Γ := wCtx) wG (wGdarf wG))
      (.ld (.addr (.glob 0)) (.int false .w32)) = true ∧
    exOk wEL wK (Expr.glob (Γ := wCtx) wG (wGdarf wG))
      (.ld (.addr (.glob 1)) (.int false .w32)) = false ∧
    exOk wEL wK (Expr.glob (Γ := wCtx) wG (wGdarf wG))
      (.ld (.addr (.glob 0)) (.int false .w16)) = false ∧
    exOk wEL wK (Expr.glob (Γ := wCtx) wA (wGdarf wA))
      (.ld (.addr (.glob 1)) (.int false .w32)) = false ∧
    exOk wEL wK (Expr.glob (Γ := wCtx) wA (wGdarf wA))
      (.ald (.addr (.glob 1)) (.int false .w32) .seqCst) = false := by
  decide

/-! ## 3. Statements -/

/-- The fixture's one signature, as a contract: it writes everything and
    holds nothing. -/
abbrev wV : Vertrag wD := Vertrag.vonSig wD (wD.sigNr 0)

/-- No callee is needed for these two statements. -/
def wFnum : wD.Fn → Nat := fun f => nomatch f
def wZert : KCert wD := []

/-- `x += 0;` -- `Zucker.plusGleich`, whose C is `x = x + 0;` and whose row
    is `GRow.setOp`. PLANTED DEFECTS: the wrong local, the wrong C operator,
    a computation type too narrow for the sum. -/
theorem probe_setOp :
    stOk wEL wFnum wZert wK
      (Stmt.plusGleich (V := wV) (l := false) (Λ := []) .hier (.lit 0) (by decide) (by decide))
      (.setOp 0 (.int false .w32) .add CIT.u32 (.lit 0)) = true ∧
    stOk wEL wFnum wZert wK
      (Stmt.plusGleich (V := wV) (l := false) (Λ := []) .hier (.lit 0) (by decide) (by decide))
      (.setOp 1 (.int false .w32) .add CIT.u32 (.lit 0)) = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.plusGleich (V := wV) (l := false) (Λ := []) .hier (.lit 0) (by decide) (by decide))
      (.setOp 0 (.int false .w32) .sub CIT.u32 (.lit 0)) = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.plusGleich (V := wV) (l := false) (Λ := []) .hier (.lit 0) (by decide) (by decide))
      (.setOp 0 (.int false .w32) .add CIT.u8 (.lit 0)) = false := by
  decide

/-- `G = a;` -- the store to a plain file-scope scalar. PLANTED DEFECTS: the
    wrong global block, the wrong cell type, the stored value taken from the
    other parameter, and the SAME statement on the `_Atomic` global `A`,
    whose C is an atomic store and not this row. -/
theorem probe_assignGlob :
    stOk wEL wFnum wZert wK
      (Stmt.assignGlob (V := wV) (l := false) wG x0 (by decide) (wGdarf wG))
      (.storeGlob 0 (.int false .w32) (.var 0)) = true ∧
    stOk wEL wFnum wZert wK
      (Stmt.assignGlob (V := wV) (l := false) wG x0 (by decide) (wGdarf wG))
      (.storeGlob 1 (.int false .w32) (.var 0)) = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.assignGlob (V := wV) (l := false) wG x0 (by decide) (wGdarf wG))
      (.storeGlob 0 (.int false .w16) (.var 0)) = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.assignGlob (V := wV) (l := false) wG x0 (by decide) (wGdarf wG))
      (.storeGlob 0 (.int false .w32) (.var 1)) = false ∧
    stOk wEL wFnum wZert wK
      (Stmt.assignGlob (V := wV) (l := false) wA x0 (by decide) (wGdarf wA))
      (.storeGlob 1 (.int false .w32) (.var 0)) = false := by
  decide

/-! ## 4. WITNESS of `ecorr_geSwap` -- the one lemma this widening adds

    Rule 13: a theorem with a universally quantified syntax premise needs a
    witness on a NON-DEGENERATE fixture. `ecorr_geSwap` speaks about every
    pair of expressions; here it is instantiated, THROUGH `exOk_sound`, on a
    C state whose two locals differ, at BOTH answers -- `a <= b` with
    `5 <= 9` and with `9 <= 5`. A witness that showed only the `true` case
    would not distinguish the lemma from one that always answers `1`. -/

def wO : Orakel wD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => true

/-- The whole memory at zero -- the witness is about the LOCALS, and the
    comparison reads no carrier. -/
def wW : World wD where
  slots := fun _ _ _ => (⟨0, by decide, by decide⟩ : Zahl 0 4294967295)
  globs := fun _ => (⟨0, by decide, by decide⟩ : Zahl 0 4294967295)
  spur := []

def wSt : CSt := { mem := fun _ _ => .int 0, live := fun _ => true, obs := [] }

theorem wCorr : corrW wEL wW wSt :=
  ⟨fun _ _ => ⟨rfl, fun _ _ _ _ => rfl⟩, And.intro (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)⟩

def wX : TVCtx wD := ⟨wEL, tvOrc, 1, tvXR, tvXR, wO, 0, fun f => nomatch f⟩

/-- A pair of `u32` values in the Gabbro environment. -/
def wEnv (a b : Nat) (ha : a ≤ 4294967295) (hb : b ≤ 4294967295) : Env wD wCtx :=
  .cons (⟨(a : Int), by omega, by omega⟩ : Zahl 0 4294967295)
    (.cons (⟨(b : Int), by omega, by omega⟩ : Zahl 0 4294967295) .nil)

/-- The same pair in the C locals `0` and `1`. -/
def wRho (a b : Nat) : CLok := fun x => if x = 0 then .int (a : Int) else .int (b : Int)

theorem wEnvRel (a b : Nat) (ha : a ≤ 4294967295) (hb : b ≤ 4294967295) :
    EnvRel wEL wK (wEnv a b ha hb) (wRho a b) := by
  refine ⟨?_, fun q hq => absurd hq List.not_mem_nil, fun q hq => absurd hq List.not_mem_nil⟩
  intro τ x
  cases x with
  | hier => rfl
  | dort y =>
      cases y with
      | hier => rfl
      | dort z => exact nomatch z

/-- **WITNESS**: the C text `b >= a` IS the emitted form of Gabbro's
    `a <= b` (`Zucker.ge b a`), and it answers `1` where the Gabbro
    comparison holds and `0` where it does not -- the same C node, two
    states, two answers. -/
theorem ecorr_geSwap_zeuge :
    exOk wEL wK (Expr.le x0 x1) (.cmp .ge CIT.u32 (.var 1) (.var 0)) = true ∧
    (∃ st', ev wEL.lay tvOrc 1 (.cmp .ge CIT.u32 (.var 1) (.var 0)) wSt (wRho 5 9)
      = some (.int 1, st')) ∧
    (∃ st', ev wEL.lay tvOrc 1 (.cmp .ge CIT.u32 (.var 1) (.var 0)) wSt (wRho 9 5)
      = some (.int 0, st')) := by
  refine ⟨by decide, ?_, ?_⟩
  · obtain ⟨v, st', hev, hvc⟩ :=
      exOk_sound wX wK (Expr.le x0 x1) (.cmp .ge CIT.u32 (.var 1) (.var 0)) (by decide)
        wW wSt (wEnv 5 9 (by decide) (by decide)) (wRho 5 9) wCorr
        (wEnvRel 5 9 (by decide) (by decide))
    have hv : v = .int 1 := hvc
    exact ⟨st', by rw [← hv]; exact hev⟩
  · obtain ⟨v, st', hev, hvc⟩ :=
      exOk_sound wX wK (Expr.le x0 x1) (.cmp .ge CIT.u32 (.var 1) (.var 0)) (by decide)
        wW wSt (wEnv 9 5 (by decide) (by decide)) (wRho 9 5) wCorr
        (wEnvRel 9 5 (by decide) (by decide))
    have hv : v = .int 0 := hvc
    exact ⟨st', by rw [← hv]; exact hev⟩

#print axioms Gabbro.Grammatik.WeitZeuge.ecorr_geSwap_zeuge
#print axioms Gabbro.Grammatik.WeitZeuge.probe_wahr
#print axioms Gabbro.Grammatik.WeitZeuge.probe_add
#print axioms Gabbro.Grammatik.WeitZeuge.probe_sub
#print axioms Gabbro.Grammatik.WeitZeuge.probe_mul
#print axioms Gabbro.Grammatik.WeitZeuge.probe_div_rem
#print axioms Gabbro.Grammatik.WeitZeuge.probe_sdiv_srem
#print axioms Gabbro.Grammatik.WeitZeuge.probe_bit
#print axioms Gabbro.Grammatik.WeitZeuge.probe_shift
#print axioms Gabbro.Grammatik.WeitZeuge.probe_cmp
#print axioms Gabbro.Grammatik.WeitZeuge.probe_cmp_typ
#print axioms Gabbro.Grammatik.WeitZeuge.probe_bool
#print axioms Gabbro.Grammatik.WeitZeuge.probe_glob
#print axioms Gabbro.Grammatik.WeitZeuge.probe_setOp
#print axioms Gabbro.Grammatik.WeitZeuge.probe_assignGlob

end Gabbro.Grammatik.WeitZeuge
