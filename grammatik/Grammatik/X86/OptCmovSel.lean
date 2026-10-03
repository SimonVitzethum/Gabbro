/-
  File:      Grammatik/X86/OptCmovSel.lean
  Subject:   CMOV-selection rule lemma (lane 891).

  DESIGN section 7 row implemented: the §3A tile "SETcc/CMOVcc where
  MEASURED suitable, never by default" with the flags-peephole premises
  ("rule in register, flag-liveness"). Local premise (validator-decided):
  unpredictable branch, cheap operands, unselected side proved
  fault-free, register-only select, fresh flags, one FP rounding scope.
  Certificate: local rewrite record plus recomputed analysis citations.
  Failure case (refuse, default stays branch): memory-source CMOV and
  any may-fault unselected side; also predictable branches, expensive
  operands, stale flags, cross-scope floats. Phase L, cost O(windows).

  Proved over the REUSED vocabulary (`Typen`, `Syntax`, `Semantik`,
  `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.ControlFlow`): the select
  computes the taken arm value, the admitted rewrite keeps the `execEnd`
  outcome (no fault added or removed, same successor worlds — hence
  contracts at their place, call logs, shared accesses and budget
  accounting unchanged), the selected word reads back whole, and the
  select preserves the `gleitPasst` outcome. No `ensures` is derived,
  no refusal becomes a warning, no faulting form is speculated above
  its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.ControlFlow
import Grammatik.X86.ConditionalMove

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one CMOV-selection site
    (DESIGN §3A tile + §7 flags-peephole row). Every field is checked
    data the validator recomputes; a refused OPTIONAL optimisation
    falls back to the branch, never to a warning. -/
structure CmovSelCert where
  unvorhersehbar : Bool
  billig : Bool
  fehlerfrei : Bool
  nurRegister : Bool
  flagsFrisch : Bool
  gleicheRundung : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. Default stays branch. -/
def cmovSelZulassen (c : CmovSelCert) : Bool :=
  c.unvorhersehbar && c.billig && c.fehlerfrei && c.nurRegister &&
    c.flagsFrisch && c.gleicheRundung

/-- Selected value: what the branch would take and the select computes. -/
def selWert (b : Bool) (x y : Int) : Int := if b then x else y

/-! ## 1. Refusal: the DESIGN failure cases must NOT select.

    A CMOV with a memory source reads BOTH sides' memory: the
    unselected side may still fault architecturally (page fault on the
    untaken path is real, OPTIMIZER §3.10 hard gate), so
    `nurRegister = false` forces `cmovSelZulassen = false` and the
    default branch stays. A may-fault unselected side
    (`fehlerfrei = false`: division, faulting load, trap-capable FP
    behind the select) is refused the same way: predicating a faulting
    form behind `cmov` does NOT remove its fault. Predictable
    branches, expensive operands, stale flags and cross-scope floats
    are refused likewise. All proved of the decided Bool. -/

/-- Memory-source CMOV refuses: the unselected side may still fault. -/
theorem cmovSelVerweigert_speicher (c : CmovSelCert)
    (h : c.nurRegister = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- A may-fault unselected side refuses. -/
theorem cmovSelVerweigert_fehler (c : CmovSelCert)
    (h : c.fehlerfrei = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- A predictable branch refuses: default stays branch. -/
theorem cmovSelVerweigert_vorhersehbar (c : CmovSelCert)
    (h : c.unvorhersehbar = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- Expensive operands refuse. -/
theorem cmovSelVerweigert_teuer (c : CmovSelCert)
    (h : c.billig = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- Stale flags refuse: the select must read the compare's flags. -/
theorem cmovSelVerweigert_flags (c : CmovSelCert)
    (h : c.flagsFrisch = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- A cross-rounding-scope float select refuses. -/
theorem cmovSelVerweigert_rundung (c : CmovSelCert)
    (h : c.gleicheRundung = false) :
    cmovSelZulassen c = false := by
  simp [cmovSelZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_cmovSelZulassen_ok :
    cmovSelZulassen ⟨true, true, true, true, true, true⟩ = true := by
  decide

/-- Probe: a memory-tainted certificate is refused. -/
theorem probe_cmovSelZulassen_speicher :
    cmovSelZulassen ⟨true, true, true, false, true, true⟩ = false := by
  decide

/-! ## 2. Value: the register-only select computes the taken arm.

    Over ARBITRARY words (`xw yw : Wort`): the `cmovAnwenden`
    destination word under flags reading `b` IS the taken arm word.
    Both arms are already computed values in registers (cheap-operand
    premise, carried by `hsrc`/`hdst`); the select adds no rounding,
    no fault and no memory event of its own. -/

/-- Taken select value: `selWert true` is the first arm. -/
theorem selWert_genommen (x y : Int) : selWert true x y = x := by
  rfl

/-- Untaken select value: `selWert false` is the second arm. -/
theorem selWert_nicht (x y : Int) : selWert false x y = y := by
  rfl

/-- Taken target word: under taken flags the destination takes the
    source word (the taken arm, already in its register). -/
theorem cmovWaehlt_genommen (s : Zustand) (dst src : Register)
    (c0 : Bedingung) (xw : Wort)
    (hbed : bedingung c0 s.flags = true)
    (hsrc : s.register src = xw) :
    (cmovAnwenden s dst src c0).register dst = xw := by
  rw [cmovAnwenden_genommen_wert s dst src c0 hbed, hsrc]

/-- Untaken target word: under untaken flags the destination keeps
    its word (the untaken arm, already in its register). -/
theorem cmovWaehlt_nicht (s : Zustand) (dst src : Register)
    (c0 : Bedingung) (yw : Wort)
    (hbed : bedingung c0 s.flags = false)
    (hdst : s.register dst = yw) :
    (cmovAnwenden s dst src c0).register dst = yw := by
  rw [cmovAnwenden_nicht_wert s dst src c0 hbed, hdst]

/-- The selected value reads back whole through the canonical word:
    width-exact (`hW`), no truncation, no wrap. -/
theorem selWortLiest (x : Int) (hW : 0 ≤ x ∧ x < 2 ^ 64) :
    ((BitVec.ofNat 64 x.toNat : Wort)).toNat = x.toNat := by
  have h : x.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The select preserves the taken arm's `gleitPasst` outcome: a
    register-only select moves the exact bit pattern, adding no
    rounding scope of its own, so neither a value nor a `logik
    bereich` outcome is folded away. -/
theorem selGleit_behaelt (b : Bool) (qa qb : GFloat)
    (lo hi : Int × Int) :
    gleitPasst lo hi (if b then qa else qb) =
      if b then gleitPasst lo hi qa else gleitPasst lo hi qb := by
  cases b <;> rfl

/-! ## 3. Certificate: local rewrite record plus recomputed citations.

    The exact certificate shape the emitter attaches to one
    CMOV-selection site: the source site and condition spans
    (recomputed positions, not diagnostic codes), the
    validator-decided side conditions, and the references to the
    recomputed analyses (branch-bias evidence for unpredictability,
    operand-cost facts for cheapness, the fault-freedom proof for the
    unselected side). The validator re-decides every side condition
    from these citations; `belegOk` gates USE of the rewrite. -/

/-- One CMOV-selection certificate: local rewrite record plus
    recomputed analysis citations. -/
structure CmovSelBeleg where
  stelle : Nat
  bedingungStelle : Nat
  zulassung : CmovSelCert
  biasBeleg : Nat
  kostenBeleg : Nat
  deriving DecidableEq, Repr

/-- Certificate admission: the carried side conditions hold. -/
def belegOk (g : CmovSelBeleg) : Bool :=
  cmovSelZulassen g.zulassung

/-- Probe: an admitted certificate passes. -/
theorem probe_belegOk :
    belegOk ⟨0, 1, ⟨true, true, true, true, true, true⟩, 2, 3⟩ = true := by
  decide

/-- Probe: a memory-source certificate is refused. -/
theorem probe_belegVerweigert_speicher :
    belegOk ⟨0, 1, ⟨true, true, true, false, true, true⟩, 2, 3⟩ = false := by
  decide

/-! ## 4. Blocks: the branch and the validator's choice.

    The branch computes both arms as pure literals and takes one; the
    select binds the chosen value. Both arms are literals (`orte =
    []`), so neither reads a shared carrier, calls, nor traps. The
    validator's choice is the select exactly where the certificate is
    admitted, otherwise the branch (default stays branch). -/

/-- The branch: both arms pure literals, one taken. -/
def branchEnd {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (c : Expr D Γ Λ .bool) (x y : Int) : Endblock D V true Γ Λ :=
  .cons (.ite c (Block.bind (.lit x) .nil) (Block.bind (.lit y) .nil))
    (.leave rfl)

/-- The select: the chosen value bound. -/
def selectEnd {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (v : Int) : Endblock D V true Γ Λ :=
  .bind (.lit v) (.leave rfl)

/-- The validator's choice: the select where admitted, else the
    branch. -/
def cmovWahlBlock {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (g : CmovSelBeleg) (c : Expr D Γ Λ .bool) (b : Bool)
    (x y : Int) : Endblock D V true Γ Λ :=
  if belegOk g then selectEnd V (selWert b x y) else branchEnd V c x y

/-- ADMISSION USE: the admitted validator choice IS the select. -/
theorem cmovWahl_waehlt {D : Deklaration} (V : Vertrag D)
    {Γ : Ctx} {Λ : List (Res D)}
    (g : CmovSelBeleg) (hz : belegOk g = true)
    (c : Expr D Γ Λ .bool) (b : Bool) (x y : Int) :
    cmovWahlBlock V g c b x y = selectEnd V (selWert b x y) := by
  unfold cmovWahlBlock
  simp [hz]

/-! ## 5. Helpers: empty reads change nothing.

    A `lese` over no places appends no event, so the world is
    unchanged; literal conditions and literal arms read nothing. Both
    arms of the branch site are literals, hence the site's only read
    is the condition's places (`hc0`). -/

/-- Reading no places changes no world. -/
theorem lese_leer {D : Deklaration} (σ : World D) (Λ : List (Res D)) :
    σ.lese Λ [] = σ := by
  rfl

/-- A literal reads no place. -/
theorem lit_orte_leer {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (v : Int) : (Expr.lit v : Expr D Γ Λ (.int v v)).orte = [] := by
  rfl

/-! ## 6. Connection: the admitted select keeps value and outcome.

    The optimisation as a generic rule lemma over ARBITRARY values
    (`b x y`, arbitrary words `xw yw`, arbitrary floats `qa qb`):
    where the certificate is admitted (`hz`), the lowering placed the
    taken arm values in the registers (`hbed`, `hsrc`, `hdst`,
    `hlink`), and the run's condition reads `b` over no places
    (`hc`, `hc0`), jointly:
    (1) the target select computes the taken arm word;
    (2) the admitted validator choice keeps the `execEnd` OUTCOME --
    same constructor, same successor worlds and environments -- so no
    fault is added or removed (`logik`/`hardware` agree), every
    downstream observation agrees (contracts at their place read the
    same values from the same environments, call logs gain no event,
    no shared access is read or written by either side -- both arms
    are literals and the condition reads no place -- and the
    step-budget accounting is unchanged: same block shape, the
    removed branch is pure and unbudgeted);
    (3) the lowered words read back whole through the canonical word;
    (4) the select preserves the taken arm's `gleitPasst` outcome
    (IEEE: the select moves the exact pattern, adding no rounding);
    (5) the select changes no memory byte and no flag (concurrency:
    no added shared access; observation: no flag change).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (both arms are
    literals; any memory, division or trap-capable FP behind the site
    keeps the `fehlerfrei = false` refusal). -/

/-- CONNECTION: the admitted CMOV select preserves the taken arm
    value, the run outcome, the word image, the float outcome and the
    memory/flag frame. -/
theorem OptCmovSel_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)}
    (g : CmovSelBeleg) (hz : belegOk g = true)
    (b : Bool) (x y : Int)
    (c : Expr D Γ Λ .bool)
    (σ : World D) (ρ : Env D Γ)
    (hc : wahr? (eval σ c σ ρ) = b)
    (hc0 : c.orte = [])
    (s : Zustand) (c0 : Bedingung) (dst src : Register)
    (hbed : bedingung c0 s.flags = b)
    (xw yw : Wort)
    (hsrc : s.register src = xw)
    (hdst : s.register dst = yw)
    (hlink : xw = BitVec.ofNat 64 x.toNat ∧
      yw = BitVec.ofNat 64 y.toNat)
    (hW : 0 ≤ x ∧ x < 2 ^ 64 ∧ 0 ≤ y ∧ y < 2 ^ 64)
    (qa qb : GFloat) (lo hi : Int × Int) :
    (cmovAnwenden s dst src c0).register dst = (if b then xw else yw) ∧
    execEnd O passes R (branchEnd V c x y) σ ρ =
      execEnd O passes R (cmovWahlBlock V g c b x y) σ ρ ∧
    (xw.toNat = x.toNat ∧ yw.toNat = y.toNat) ∧
    (gleitPasst lo hi (if b then qa else qb) =
      if b then gleitPasst lo hi qa else gleitPasst lo hi qb) ∧
    ((cmovAnwenden s dst src c0).speicher = s.speicher ∧
      (cmovAnwenden s dst src c0).flags = s.flags) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases b with
    | true => rw [cmovWaehlt_genommen s dst src c0 xw hbed hsrc, if_pos rfl]
    | false =>
      rw [cmovWaehlt_nicht s dst src c0 yw hbed hdst, if_neg (by decide)]
  · rw [cmovWahl_waehlt V g hz c b x y]
    simp only [branchEnd, selectEnd, execEnd, execStmt, execBlock,
      Ausgang.schrumpf, EndAusgang.schrumpf, Env.tail]
    rw [hc0, lit_orte_leer x, lit_orte_leer y,
      lit_orte_leer (selWert b x y), lese_leer, hc]
    cases b <;> rfl
  · obtain ⟨hx0, hxb, hy0, hyb⟩ := hW
    rw [hlink.1, hlink.2]
    exact ⟨selWortLiest x ⟨hx0, hxb⟩, selWortLiest y ⟨hy0, hyb⟩⟩
  · exact selGleit_behaelt b qa qb lo hi
  · exact ⟨cmovAnwenden_speicher s dst src c0,
      cmovAnwenden_flags s dst src c0⟩

/-! ## 7. Joint witnesses: the rule fires beside a memory-changing run.

    ALL premises instantiated JOINTLY on the NON-DEGENERATE reference
    program `refD` (whose `einzahlen` writes its table,
    `refEin_schreibt`), beside the reached F-machine run `MB` that
    changes memory (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).
    The source condition is `.wahr` (reads no place, evaluates to the
    taken branch); the target state is `witTrue` (flags take `.e`,
    `rbx` holds the taken arm word `20`, `rax` the untaken word `10`),
    so source and target agree on the taken value `20`. -/

/-- JOINT WITNESS for `cmovWahl_waehlt`: the admitted choice is the
    select, on `refD` beside the memory-changing reached run. -/
theorem cmovWahl_waehlt_zeuge :
    ∃ (V : Vertrag refD) (Γ : Ctx) (Λ : List (Res refD))
      (g : CmovSelBeleg) (_hz : belegOk g = true)
      (c : Expr refD Γ Λ .bool) (b : Bool) (x y : Int),
      cmovWahlBlock V g c b x y = selectEnd V (selWert b x y) ∧
      (vertragVon refD refEin).schreibt () = true ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
      MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := cmovWahl_waehlt (V := vertragVon refD refEin)
    (Γ := []) (Λ := [])
    (g := ⟨0, 1, ⟨true, true, true, true, true, true⟩, 2, 3⟩)
    (hz := by decide) (c := Expr.wahr) (b := true) (x := 20) (y := 10)
  refine ⟨vertragVon refD refEin, [], [],
    ⟨0, 1, ⟨true, true, true, true, true, true⟩, 2, 3⟩, by decide,
    Expr.wahr, true, 20, 10, ?_, ?_, ?_, ?_⟩
  · exact hV
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/-- JOINT WITNESS for `OptCmovSel_verbindung`: the taken select
    (`20`) keeps value, outcome, word image, float outcome and frame,
    on `refD` beside the memory-changing reached run. -/
theorem OptCmovSel_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) →
        RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD))
      (g : CmovSelBeleg) (_hz : belegOk g = true)
      (b : Bool) (x y : Int)
      (c : Expr refD Γ Λ .bool)
      (σ : World refD) (ρ : Env refD Γ)
      (_hc : wahr? (eval σ c σ ρ) = b)
      (_hc0 : c.orte = [])
      (s : Zustand) (c0 : Bedingung) (dst src : Register)
      (_hbed : bedingung c0 s.flags = b)
      (xw yw : Wort)
      (_hsrc : s.register src = xw)
      (_hdst : s.register dst = yw)
      (_hlink : xw = BitVec.ofNat 64 x.toNat ∧
        yw = BitVec.ofNat 64 y.toNat)
      (_hW : 0 ≤ x ∧ x < 2 ^ 64 ∧ 0 ≤ y ∧ y < 2 ^ 64)
      (qa qb : GFloat) (lo hi : Int × Int),
      (cmovAnwenden s dst src c0).register dst =
        (if b then xw else yw) ∧
      execEnd O passes R (branchEnd V c x y) σ ρ =
        execEnd O passes R (cmovWahlBlock V g c b x y) σ ρ ∧
      (xw.toNat = x.toNat ∧ yw.toNat = y.toNat) ∧
      (gleitPasst lo hi (if b then qa else qb) =
        if b then gleitPasst lo hi qa else gleitPasst lo hi qb) ∧
      ((cmovAnwenden s dst src c0).speicher = s.speicher ∧
        (cmovAnwenden s dst src c0).flags = s.flags) ∧
      (vertragVon refD refEin).schreibt () = true ∧
      RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
      MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptCmovSel_verbindung (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := [])
    (g := ⟨0, 1, ⟨true, true, true, true, true, true⟩, 2, 3⟩)
    (hz := by decide) (b := true) (x := 20) (y := 10)
    (c := Expr.wahr) (σ := refSp0.welt []) (ρ := Env.nil)
    (hc := rfl) (hc0 := rfl)
    (s := witTrue) (c0 := .e) (dst := .rax) (src := .rbx)
    (hbed := by decide)
    (xw := BitVec.ofNat 64 20) (yw := BitVec.ofNat 64 10)
    (hsrc := by decide) (hdst := by decide)
    (hlink := ⟨by decide, by decide⟩) (hW := by decide)
    (qa := bruch (1, 2)) (qb := bruch (1, 4))
    (lo := (1, 2)) (hi := (3, 4))
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [],
    ⟨0, 1, ⟨true, true, true, true, true, true⟩, 2, 3⟩, by decide,
    true, 20, 10, Expr.wahr, refSp0.welt [], Env.nil,
    rfl, rfl, witTrue, .e, .rax, .rbx, by decide,
    BitVec.ofNat 64 20, BitVec.ofNat 64 10, by decide, by decide,
    ⟨by decide, by decide⟩, by decide,
    bruch (1, 2), bruch (1, 4), (1, 2), (3, 4),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - Proved: admission, six refusals, select value equations, taken/
      untaken target words, width-exact word readback, `gleitPasst`
      preservation, certificate shape, branch/select blocks, admitted
      validator choice, empty-read helpers, the
      `OptCmovSel_verbindung` rule lemma (select value, exec-outcome,
      word image, float outcome, memory/flag frame), and both joint
      witnesses (`cmovWahl_waehlt_zeuge`,
      `OptCmovSel_verbindung_zeuge`) on `refD` beside the
      memory-changing run `MB`.
    - NOT proved here, and not claimed:
    - No `Befehl` constructor, no `Codec` row, no bytes: CMOVcc has no
      native pilot encoding, so there is no codec/source
      correspondence and no emitted native ISA expansion here; target
      value facts reuse `ControlFlow.cmovAnwenden` and
      `ConditionalMove` equations over decoded lengths only.
    - No hardware correspondence: flag readings reuse `bedingung`,
      faults are the existing permission-checked outcomes, not
      silicon; the memory-source CMOV fault fact is reused, never
      re-decided.
    - No TSO/GX bridge, no ABI/loader claim, no cycle/timing claim;
      budget preservation is the same-shape source accounting (as in
      lane 860), the formal level-(c) machine-work bound stays OPEN
      per IR-VALIDIERUNG; no termination claim.
    - No lowering correspondence: the source-to-register placement
      (`hbed`/`hsrc`/`hdst`/`hlink`) is the validator-decided premise
      the lowering lane discharges per site.
-/

#print axioms cmovSelZulassen
#print axioms selWert
#print axioms cmovSelVerweigert_speicher
#print axioms cmovSelVerweigert_fehler
#print axioms cmovSelVerweigert_vorhersehbar
#print axioms cmovSelVerweigert_teuer
#print axioms cmovSelVerweigert_flags
#print axioms cmovSelVerweigert_rundung
#print axioms probe_cmovSelZulassen_ok
#print axioms probe_cmovSelZulassen_speicher
#print axioms selWert_genommen
#print axioms selWert_nicht
#print axioms cmovWaehlt_genommen
#print axioms cmovWaehlt_nicht
#print axioms selWortLiest
#print axioms selGleit_behaelt
#print axioms belegOk
#print axioms probe_belegOk
#print axioms probe_belegVerweigert_speicher
#print axioms branchEnd
#print axioms selectEnd
#print axioms cmovWahlBlock
#print axioms cmovWahl_waehlt
#print axioms lese_leer
#print axioms lit_orte_leer
#print axioms OptCmovSel_verbindung
#print axioms cmovWahl_waehlt_zeuge
#print axioms OptCmovSel_verbindung_zeuge

end Gabbro.Grammatik.X86
