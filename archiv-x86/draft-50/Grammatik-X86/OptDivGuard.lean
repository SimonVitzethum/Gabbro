/-
  File:      Grammatik/X86/OptDivGuard.lean
  Subject:   Division-guard optimiser rule lemma (lane 889).

  DESIGN section 7 row (LICM): local premise "invariance recomputed
  (exact-value, not rounded-value), non-faulting over hoisted inputs from
  rechecked source facts", certificate "B+C", failure case "hoist `x/n`
  above `n!=0`; hoist token op on shared access on local evidence",
  phase M. DESIGN section 3 row: divide-error (#DE on zero/overflow) is
  a `hardware`-stop preserved exactly; LICM/DCE may never speculate it.
  DESIGN section 3A + example 3 (CE-2): `IDIV`/`DIV` are never
  speculated, never hoisted above their divisor check; hoisting `x/n`
  above `wenn n != 0` turns the untaken path into a `hardware` stop.

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `Gleitkomma` kernel via `Semantik`, `ReferenzB`,
  `X86.Typen`, `X86.Wort`, `X86.MulDiv`, `X86.Ganzzahl` via `MulDiv`):
  the validator-decided admission `divGuardZulassen` with its four
  refusal legs; source value/fault preservation for the guarded
  division window; target divide-error preservation (zero divisor and
  quotient overflow trap exactly, flags kept, divisions never pure);
  and the connection `OptDivGuard_verbindung` with its joint witness.
  No `ensures` is derived, no refusal becomes a warning, no faulting
  form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.MulDiv

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one division site
    (DESIGN section 7 LICM row + section 3 row): the divisor is
    recomputed nonzero from source range facts (`nichtNullOk`), the
    quotient fits 64 bits (`keinUeberlaufOk`), invariance/dominance is
    recomputed and the duty/effect binding forbids shared-token motion
    on local evidence alone (`unveraendertOk`, certificate layers B+C),
    and no float substitution is admitted (`keinGleitErsatz`: no
    RCPSS-for-DIV, no reassociation, float division never pure). -/
structure DivGuardCert where
  nichtNullOk : Bool
  keinUeberlaufOk : Bool
  unveraendertOk : Bool
  keinGleitErsatz : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL motion
    falls back to another certified translation, never to a warning. -/
def divGuardZulassen (c : DivGuardCert) : Bool :=
  c.nichtNullOk && c.keinUeberlaufOk && c.unveraendertOk && c.keinGleitErsatz

/-! ## 1. Refusal: speculation and hoisting above the check must NOT fire.

    Hoisting `x/n` above `n!=0` without recomputed nonzero evidence
    turns the untaken path into a `hardware` stop (DESIGN example 3,
    CE-2): `nichtNullOk = false` forces `divGuardZulassen = false`.
    A quotient that may need 65 bits (`keinUeberlaufOk = false`) keeps
    the #DE-overflow stop. Motion without recomputed invariance or on
    shared-token local evidence alone (`unveraendertOk = false`) is
    refused: reuse across unlock and hoisting above a publishing
    acquire stay refused. Any float substitution (`keinGleitErsatz =
    false`: RCPSS-for-DIV, reassociation, float division treated as
    pure) is refused. All four are proved of the decided Bool, so the
    validator cannot silently skip them. -/

/-- Hoisting without recomputed divisor-nonzero evidence refuses. -/
theorem divGuardVerweigert_ohneNachweis (c : DivGuardCert)
    (h : c.nichtNullOk = false) :
    divGuardZulassen c = false := by
  simp [divGuardZulassen, h]

/-- A possibly overflowing quotient refuses. -/
theorem divGuardVerweigert_ueberlauf (c : DivGuardCert)
    (h : c.keinUeberlaufOk = false) :
    divGuardZulassen c = false := by
  simp [divGuardZulassen, h]

/-- Motion without recomputed invariance refuses. -/
theorem divGuardVerweigert_veraendert (c : DivGuardCert)
    (h : c.unveraendertOk = false) :
    divGuardZulassen c = false := by
  simp [divGuardZulassen, h]

/-- Any float substitution refuses. -/
theorem divGuardVerweigert_gleit (c : DivGuardCert)
    (h : c.keinGleitErsatz = false) :
    divGuardZulassen c = false := by
  simp [divGuardZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_divGuardZulassen_ok :
    divGuardZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: speculation without nonzero evidence is refused. -/
theorem probe_divGuardZulassen_ohneNachweis :
    divGuardZulassen ⟨false, true, true, true⟩ = false := by
  decide

/-- Probe: a possibly overflowing quotient is refused. -/
theorem probe_divGuardZulassen_ueberlauf :
    divGuardZulassen ⟨true, false, true, true⟩ = false := by
  decide

/-- Probe: motion without invariance is refused. -/
theorem probe_divGuardZulassen_veraendert :
    divGuardZulassen ⟨true, true, false, true⟩ = false := by
  decide

/-- Probe: a float substitution is refused. -/
theorem probe_divGuardZulassen_gleit :
    divGuardZulassen ⟨true, true, true, false⟩ = false := by
  decide

/-- DIV is never pure, hence never DCE/motion-eligible: the REUSED
    never-pure policy, applied. -/
theorem divGuard_nieRein_div (src : Register) :
    rein (.divRax src) = false :=
  falle_nie_rein _ src (Or.inl rfl)

/-- IDIV is never pure either. -/
theorem divGuard_nieRein_idiv (src : Register) :
    rein (.idivRax src) = false :=
  falle_nie_rein _ src (Or.inr rfl)

/-! ## 2. Source value: the guarded division computes exactly.

    Each lemma is over ARBITRARY values (`x y : Int`) with the `M102`
    side conditions (`h0`, `h1'`) as validator-decided premises,
    forwarded unchanged from rechecked source facts: truncation toward
    zero (`tdiv`/`tmod`), never SAR floor, never a folded-away fault.
    A zero divisor never reaches the rule: without `h1'` there is no
    well-typed division at all. -/

/-- `x / y` computes `x.tdiv y` under the `M102` premises. -/
theorem divGuard_quotient_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.div h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tdiv y := by
  rfl

/-- `x % y` computes `x.tmod y` under the `M102` premises (the
    remainder half of the DESIGN section 3 row). -/
theorem divGuard_rest_wert (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y) :
    (Zahl.rem h0 h1' (⟨x, Int.le_refl x, Int.le_refl x⟩ : Zahl x x)
      (⟨y, Int.le_refl y, Int.le_refl y⟩ : Zahl y y)).n = x.tmod y := by
  rfl

/-- Probe: `7 / 2` truncates to `3` (never SAR floor). -/
theorem probe_divGuard_7durch2 : (Zahl.div (by decide : (0 : Int) ≤ 7) (by decide : (1 : Int) ≤ 2)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)
    (⟨2, by decide, by decide⟩ : Zahl 2 2)).n = 3 := by
  decide

/-- Probe: `7 % 2` is `1`. -/
theorem probe_divGuard_rest_7durch2 : (Zahl.rem (by decide : (0 : Int) ≤ 7) (by decide : (1 : Int) ≤ 2)
    (⟨7, by decide, by decide⟩ : Zahl 7 7)
    (⟨2, by decide, by decide⟩ : Zahl 2 2)).n = 1 := by
  decide

/-! ## 3. Target: the divide-error stop is preserved exactly.

    Both #DE causes of the DESIGN section 3 row trap in the REUSED
    step: a zero divisor and a quotient that needs 65 bits each halt,
    for DIV and (zero divisor) for IDIV. A speculated division above
    its guard therefore introduces a `hardware` stop on paths that had
    none -- which is why the rule refuses it. The admitted division
    keeps the flags (DIV flags are undefined, never clobbered into an
    FP-visible state), pinning the no-FP-effect half of
    `keinGleitErsatz` at the machine level. -/

/-- A DIV over a zero divisor halts: guard refusal and trap agree. -/
theorem divGuard_null_halt (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hnull : (s.register src).toNat = 0) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitU_verweigert_bei_null (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hnull
  exact md_div_halt d s src hok h hnone

/-- A DIV whose quotient needs 65 bits halts (the overflow half). -/
theorem divGuard_ueberlauf_halt (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hpos : (s.register src).toNat ≠ 0)
    (hgross : ¬ u128 (s.register Register.rdx) (s.register Register.rax) /
      (s.register src).toNat < 2 ^ 64) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitU_verweigert_bei_ueberlauf (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hpos hgross
  exact md_div_halt d s src hok h hnone

/-- An IDIV over a zero divisor halts. -/
theorem divGuard_idiv_null_halt (d : MulDivDecodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .idivRax src)
    (hnull : sVal .b64 (s.register src) = 0) :
    mulDivSchritt d s = .hardwareHalt := by
  have hnone := divWeitS_verweigert_bei_null (s.register Register.rdx)
    (s.register Register.rax) (s.register src) hnull
  exact md_idiv_halt d s src hok h hnone

/-- An admitted DIV keeps the flags: no FP-visible effect. -/
theorem divGuard_div_flags_bleiben (d : MulDivDecodiert) (s s' : Zustand)
    (src : Register) (q r : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .divRax src)
    (hqr : divWeitU (s.register Register.rdx) (s.register Register.rax)
      (s.register src) = some (q, r))
    (hstep : mulDivSchritt d s = .ok s') :
    s'.flags = s.flags := by
  rw [md_div_erfolg d s src q r hok h hqr] at hstep
  cases hstep
  rfl

/-- Probe: the planted zero-divisor image traps. -/
theorem probe_divGuard_null_halt :
    istHalt (mulDivSchritt ⟨.divRax .rcx, 3⟩ mdZustandNull) = true := by
  decide

/-- Probe: the planted zero-divisor image is refused by the guard. -/
theorem probe_divGuard_guard_null :
    zugelassen (.divRax .rcx) mdZustandNull = false := by
  decide

/-! ## 4. Connection: the guarded division window is preserved.

    The rewrite is stated at an `Endblock.bind` window with an ARBITRARY
    continuation `rest`, so the conclusion covers every downstream
    observation at once. The admitted shape keeps the `M102` divisor
    check at its site (`h0`, `h1'`, forwarded unchanged) and narrows
    the admitted quotient into the site range through `weiter` with the
    validator-recomputed range facts (`hEq hz`: DESIGN "source extent
    proof AT the site"). Conclusion, jointly:
    (1) the evaluated bound VALUE is preserved (truncation, exact);
    (2) the `execEnd` OUTCOME is equal -- same constructor, same
    successor worlds and environments -- so no fault is added or
    removed (`logik`/`hardware` agree), every downstream observation
    agrees (contracts at their place read the same values from the same
    environments, call logs gain no event, the step-budget accounting is
    unchanged: same block shape, the check stays where it was);
    (3) no shared access is added or removed for concurrency -- both
    windows read `orte = []`;
    (4) the admitted quotient reads back whole through the canonical
    word (width-exact, `hW`);
    (5) an unrelated admitted float-division site keeps its
    `gleitPasst` outcome: the integer motion never becomes a float
    substitution and never disturbs the single rounding scope.
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard. -/

/-- The admitted quotient reads back whole through the canonical word. -/
theorem divGuardWort (x y : Int) (hW : 0 ≤ x.tdiv y ∧ x.tdiv y < 2 ^ 64) :
    ((BitVec.ofNat 64 (x.tdiv y).toNat : Wort)).toNat = (x.tdiv y).toNat := by
  have h : (x.tdiv y).toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- CONNECTION: the admitted guarded division preserves value,
    outcome, footprints, word image and float observations. -/
theorem OptDivGuard_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y)
    (cert : DivGuardCert) (hz : divGuardZulassen cert = true)
    (hEq : divGuardZulassen cert = true → (0 ≤ x.tdiv y ∧ x.tdiv y ≤ x))
    (rest : Endblock D V l ((.int 0 x) :: Γ) Λ)
    (hW : 0 ≤ x.tdiv y ∧ x.tdiv y < 2 ^ 64)
    (qa qb qf lo hi : Int × Int)
    (eF : bruch qf = gleitRechne .div (bruch qa) (bruch qb))
    (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (.weiter (hEq hz).1 (hEq hz).2 (.lit (x.tdiv y)) :
      Expr D Γ Λ (.int 0 x)) σ ρ).n
      = (eval σ₀ (.div h0 h1' (.lit x) (.lit y) :
        Expr D Γ Λ (.int 0 x)) σ ρ).n
    ∧ execEnd O passes R
        (Endblock.bind (.weiter (hEq hz).1 (hEq hz).2 (.lit (x.tdiv y)) :
          Expr D Γ Λ (.int 0 x)) rest) σ ρ
      = execEnd O passes R
        (Endblock.bind (.div h0 h1' (.lit x) (.lit y) :
          Expr D Γ Λ (.int 0 x)) rest) σ ρ
    ∧ (.weiter (hEq hz).1 (hEq hz).2 (.lit (x.tdiv y)) :
        Expr D Γ Λ (.int 0 x)).orte
      = (.div h0 h1' (.lit x) (.lit y) : Expr D Γ Λ (.int 0 x)).orte
    ∧ ((BitVec.ofNat 64 (x.tdiv y).toNat : Wort)).toNat = (x.tdiv y).toNat
    ∧ gleitPasst lo hi (bruch qf) =
        gleitPasst lo hi (gleitRechne .div (bruch qa) (bruch qb)) := by
  exact ⟨rfl, rfl, rfl, divGuardWort x y hW, by rw [eF]⟩

/-! ## 5. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptDivGuard_verbindung` instantiated JOINTLY:
    `7 / 2` admits to `3` under a `bind` with a `leave` continuation,
    beside the admitted float-division site `(3/4) / 1 = 3/4` in one
    rounding scope, in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside the
    reached F-machine run `MB` that changes memory (`refB_erreicht`,
    `refB_schreibt`: slot `0 -> 100`). Every conjunct group is used. -/

/-- JOINT WITNESS for `OptDivGuard_verbindung`: `7 / 2` admits to `3`
    on `refD`, beside the memory-changing reached run. -/
theorem OptDivGuard_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ : List (Res refD)) (l : Bool)
      (x y : Int) (h0 : 0 ≤ x) (h1' : 1 ≤ y)
      (cert : DivGuardCert) (hz : divGuardZulassen cert = true)
      (hEq : divGuardZulassen cert = true → (0 ≤ x.tdiv y ∧ x.tdiv y ≤ x))
      (rest : Endblock refD V l ((.int 0 x) :: Γ) Λ)
      (_hW : 0 ≤ x.tdiv y ∧ x.tdiv y < 2 ^ 64)
      (qa qb qf lo hi : Int × Int)
      (_eF : bruch qf = gleitRechne .div (bruch qa) (bruch qb))
      (σ₀ σ : World refD) (ρ : Env refD Γ),
      (eval σ₀ (.weiter (hEq hz).1 (hEq hz).2 (.lit (x.tdiv y)) :
        Expr refD Γ Λ (.int 0 x)) σ ρ).n
        = (eval σ₀ (.div h0 h1' (.lit x) (.lit y) :
          Expr refD Γ Λ (.int 0 x)) σ ρ).n
      ∧ execEnd O passes R
          (Endblock.bind (.weiter (hEq hz).1 (hEq hz).2 (.lit (x.tdiv y)) :
            Expr refD Γ Λ (.int 0 x)) rest) σ ρ
        = execEnd O passes R
          (Endblock.bind (.div h0 h1' (.lit x) (.lit y) :
            Expr refD Γ Λ (.int 0 x)) rest) σ ρ
      ∧ (.weiter (hEq hz).1 (hEq hz).2 (.lit (x.tdiv y)) :
          Expr refD Γ Λ (.int 0 x)).orte
        = (.div h0 h1' (.lit x) (.lit y) : Expr refD Γ Λ (.int 0 x)).orte
      ∧ ((BitVec.ofNat 64 (x.tdiv y).toNat : Wort)).toNat = (x.tdiv y).toNat
      ∧ gleitPasst lo hi (bruch qf) =
          gleitPasst lo hi (gleitRechne .div (bruch qa) (bruch qb))
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptDivGuard_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (l := true)
    (x := 7) (y := 2) (h0 := by decide) (h1' := by decide)
    (cert := ⟨true, true, true, true⟩) (hz := by decide) (hEq := by decide)
    (rest := Endblock.leave rfl) (hW := by decide)
    (qa := (3, 4)) (qb := (1, 1)) (qf := (3, 4)) (lo := (0, 0)) (hi := (1, 1))
    (eF := by decide)
    (σ₀ := refSp0.welt []) (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], true, 7, 2,
    by decide, by decide, ⟨true, true, true, true⟩, by decide, by decide,
    Endblock.leave rfl, by decide,
    (3, 4), (1, 1), (3, 4), (0, 0), (1, 1), by decide,
    refSp0.welt [], refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No signed-division window: `sdiv`/`srem` values are not connected
      here; only unsigned `div`/`rem` values (section 2) and the `div`
      `Endblock` connection (section 4).
    - No hoisted-above-branch syntax motion: the admitted motion is the
      value-preserving window of section 4 with the check kept at its
      site; a branch-hoist equation with `Stmt`/branch semantics stays
      with the lowering lane.
    - No totalCost inequality: the admitted window is the same block
      shape with the check kept at its site, so step-budget accounting
      is unchanged; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at canonical words, `gleitRechne` values and
      the REUSED `mulDivSchritt` outcomes.
-/

#print axioms divGuardZulassen
#print axioms divGuardVerweigert_ohneNachweis
#print axioms divGuardVerweigert_ueberlauf
#print axioms divGuardVerweigert_veraendert
#print axioms divGuardVerweigert_gleit
#print axioms probe_divGuardZulassen_ok
#print axioms probe_divGuardZulassen_ohneNachweis
#print axioms probe_divGuardZulassen_ueberlauf
#print axioms probe_divGuardZulassen_veraendert
#print axioms probe_divGuardZulassen_gleit
#print axioms divGuard_nieRein_div
#print axioms divGuard_nieRein_idiv
#print axioms divGuard_quotient_wert
#print axioms divGuard_rest_wert
#print axioms probe_divGuard_7durch2
#print axioms probe_divGuard_rest_7durch2
#print axioms divGuard_null_halt
#print axioms divGuard_ueberlauf_halt
#print axioms divGuard_idiv_null_halt
#print axioms divGuard_div_flags_bleiben
#print axioms probe_divGuard_null_halt
#print axioms probe_divGuard_guard_null
#print axioms divGuardWort
#print axioms OptDivGuard_verbindung
#print axioms OptDivGuard_verbindung_zeuge

end Gabbro.Grammatik.X86
