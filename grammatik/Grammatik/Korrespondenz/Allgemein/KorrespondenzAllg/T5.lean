/- Part 5 of 5 of `KorrespondenzAllg` (split by instrumente/teile/lean-teilen.py; the umbrella `KorrespondenzAllg.lean` imports all parts). -/
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}

section OhneOrakel

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D)

/-- The flat statement check admits no axiom call and no `forever`. -/
theorem stOk0_hardwareFrei (GT : GerTafel D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (K : CEnvLay D Γ) (s : Stmt D V l Γ Λ Λ') (r : GRow)
    (h : stOk0 EL fnum c K s r GT = true) : s.hardwareFrei = true := by
  cases s <;> first | rfl | (exact absurd h (by simp [stOk0]))

/-- **The two staged checks refuse every source of a `hardware` outcome**,
    in one induction on the nesting weight of the rows. -/
theorem stOkBl_hardwareFrei (GT : GerTafel D) (hein : GT.ein = false) : ∀ (n : Nat),
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n →
        stOk EL fnum c K₀ s r GT = true → s.hardwareFrei = true) ∧
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (b : Block D V l Γ₀ Λ₀ Λ₁) (rs : List GRow), rowsSize rs ≤ n →
        blOk EL fnum c K₀ b rs GT = true → b.hardwareFrei = true) := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro V l Γ₀ Λ₀ Λ₁ K₀ s r hn _
        have := rowSize_pos r
        omega
      · intro V l Γ₀ Λ₀ Λ₁ K₀ b rs hn h
        have hrs : rs = [] := rowsSize_nil rs (by omega)
        subst hrs
        cases b with
        | nil => rfl
        | _ => exact absurd h (by simp [blOk])
  | succ n ih =>
      have h1 : ∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
          (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n + 1 →
          stOk EL fnum c K₀ s r GT = true → s.hardwareFrei = true := by
        intro V l Γ₀ Λ₀ Λ₁ K₀ s r hn h
        cases r with
        | ite cc tRows eRows =>
            cases s with
            | ite cnd t e =>
                simp only [stOk, Bool.and_eq_true] at h
                obtain ⟨⟨_, hT⟩, hE⟩ := h
                simp only [rowSize] at hn
                simp only [Stmt.hardwareFrei, Bool.and_eq_true]
                exact ⟨ih.2 K₀ t tRows (by omega) hT, ih.2 K₀ e eRows (by omega) hE⟩
            | _ => exact absurd h (by simp [stOk])
        | forTrav x ti hiC bodyRows m' =>
            cases s with
            | traverse tb inv body =>
                cases hiC with
                | lit v =>
                    simp only [stOk, Bool.and_eq_true] at h
                    obtain ⟨-, hb⟩ := h
                    simp only [rowSize] at hn
                    exact ih.2 _ body bodyRows (by omega) hb
                | _ => exact absurd h (by simp [stOk])
            | _ => exact absurd h (by simp [stOk])
        | _ => exact stOk0_hardwareFrei EL fnum c GT K₀ s _ h
      refine ⟨h1, ?_⟩
      intro V l Γ₀ Λ₀ Λ₁ K₀ b rs hn h
      cases rs with
      | nil =>
          cases b with
          | nil => rfl
          | _ => exact absurd h (by simp [blOk])
      | cons r rs' =>
          simp only [rowsSize] at hn
          have hpos := rowSize_pos r
          have hrs : rowsSize rs' ≤ n := by omega
          cases r with
          | void x =>
              simp only [blOk, Bool.and_eq_true] at h
              exact ih.2 K₀ b rs' hrs h.2
          | bindLet y τc ce =>
              cases b with
              | bind e rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  exact ih.2 _ rest rs' hrs h.2
              | _ => exact absurd h (by simp [blOk])
          -- THE DEVICE READS. Under the EMPTY device table (`ein = false`)
          -- the check refuses both rows outright, and the reading of before
          -- stands untouched -- which is what the two closed chains need.
          | loadReg y τc cp w =>
              cases b with
              | regRead rg hkl rest => exact absurd h (by simp [blOk, hein])
              | _ => exact absurd h (by simp [blOk])
          | loadRegElse y τc cp w cc crr =>
              cases b with
              | regReadElse rg hkl zusage sonst rest => exact absurd h (by simp [blOk, hein])
              | _ => exact absurd h (by simp [blOk])
          | call fc cargs dst =>
              cases dst with
              | none =>
                  cases b with
                  | cons s rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      simp only [Block.hardwareFrei, Bool.and_eq_true]
                      exact ⟨h1 K₀ s _ (by omega) h.1, ih.2 K₀ rest rs' hrs h.2⟩
                  | _ => exact absurd h (by simp [blOk])
              | some p =>
                  cases b with
                  | bindCall g args heq hp hrp rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      exact ih.2 _ rest rs' hrs h.2
                  | _ => exact absurd h (by simp [blOk])
          | _ =>
              cases b with
              | cons s rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  simp only [Block.hardwareFrei, Bool.and_eq_true]
                  exact ⟨h1 K₀ s _ (by omega) h.1, ih.2 K₀ rest rs' hrs h.2⟩
              | _ => exact absurd h (by simp [blOk])

/-- **A certified body carries no oracle form.** -/
theorem enOk_hardwareFrei (GT : GerTafel D) (hein : GT.ein = false) (top : Bool)
    {V : Vertrag D} {l : Bool} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ),
      enOk EL fnum c top rs K b GT = true → b.hardwareFrei = true := by
  intro rs
  induction rs with
  | nil =>
      intro Γ Λ K b h
      cases b with
      | ret r hΛ => rfl
      | _ => exact absurd h (by simp [enOk])
  | cons r rs ih =>
      intro Γ Λ K b h
      cases r with
      | void x =>
          simp only [enOk, Bool.and_eq_true] at h
          exact ih K b h.2
      | ret cr =>
          simp only [enOk, Bool.and_eq_true, List.isEmpty_iff] at h
          obtain ⟨-, hb⟩ := h
          cases b with
          | ret e hΛ => rfl
          | _ => exact absurd hb (by simp)
      | bindLet x τc ce =>
          cases b with
          | bind e rest =>
              simp only [enOk, Bool.and_eq_true] at h
              exact ih _ rest h.2
          | _ => exact absurd h (by simp [enOk])
      | _ =>
          cases b with
          | cons s rest =>
              simp only [enOk, Bool.and_eq_true] at h
              simp only [Endblock.hardwareFrei, Bool.and_eq_true]
              exact ⟨(stOkBl_hardwareFrei EL fnum c GT hein (rowSize _)).1 K s _
                  (Nat.le_refl _) h.1,
                ih K rest h.2⟩
          | _ => exact absurd h (by simp [enOk])

/-- **THE READING FOR THE CLOSING THEOREM**: a program with a correspondence
    certificate that checks carries no source of a `hardware` outcome in any
    of its bodies -- so its calls never end in one, at any depth, against any
    oracle (`rufAt_ohneHardware`). -/
theorem korrOk_hardwareFrei {P : Programm D} {fs : List D.Fn} {GT : GerTafel D}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs GT = true)
    (hein : GT.ein = false) (g : D.Fn) :
    (P.rumpf g).hardwareFrei = true := by
  obtain ⟨k, hk, hok⟩ := korrOk_fn hvoll hc g
  exact enOk_hardwareFrei EL fnum c GT hein true k.rows k.lay (P.rumpf g) hok

/-- **NO CALL OF A CERTIFIED PROGRAM ENDS IN A HARDWARE OUTCOME** -- for a
    certificate that names NO DEVICE (`GT.ein = false`, the default table).
    The premise is not decoration: a certificate that carries a register READ
    row carries `Block.regLies`/`.regReadElse`, and those are two of the five
    sources of a hardware outcome. What the device chain buys is paid for
    HERE, and the price stands in the premise list. -/
theorem korrOk_rufAt_ohneHardware {P : Programm D} {fs : List D.Fn} {GT : GerTafel D}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs GT = true)
    (hein : GT.ein = false) (O : Orakel D)
    (passes n : Nat) : OhneHardware (rufAt P O passes n) :=
  rufAt_ohneHardware P O passes (korrOk_hardwareFrei EL fnum c hvoll hc hein) n

end OhneOrakel

/-
CUTS -- what this file does not do, by name.
- WHERE THE BLOCK FORMS STAND, so that the list below is read right:
  * `traverse` (`GRow.forTrav`) is IN, but only with a CONSTANT bound:
    `scorr_traverse` wants `ev hiC = D.count tb` at EVERY C state, and
    the only C expression this file can decide that of is a literal.
    A header that computes its bound is a refusal, not an admission.
    The loop's own budget `m'` is data of the row and not checked: it is
    the `forC` step count of the C semantics, and the correspondence
    holds at whatever it is.
  * `let x = f(…)` (`bindCall`) is IN, and in `blOk` ONLY: it is a
    `Block` constructor and not an `Endblock` one, so a body whose TOP
    level binds a call's answer is not expressible in the model at all,
    and inside an `if` arm or a loop body it is. The arm ends in
    `bsem_bindCall`.
- COVERED FORMS: the statement and expression families listed in the header.
  Not covered (the Bool is `false`, a refusal), with the reason for each:
  * The remaining block statements -- `retry`, `forever`, `locks`,
    `breaking`, `onOption`, `onTag`, `onGrund` -- have rows in neither
    `GRow` nor the printer, so `blOk` never meets them; `stOk0` refuses
    their statements. Same for the other thirteen `Block` constructors
    (`bindCallInd`, `bindCallElse`, `bindAxiom`, `regLies`,
    `regLiesElse`, `awaits`, `exchange`, `narrow`, `pruefung` and the
    four float binders): each needs its own row shape, and none is one
    line.
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
    device and foreign forms: no arm, and for the floats no `ecorr_*` at
    all (`CX` has no float operand a `GRow` could carry).
- THE DEVICE FORMS THAT ARE NOT CARRIED, each with what it would take:
  * `Block.awaits` (`Hardware.sichtbarkeit`, A10) -- `GRow` has no ATOMIC row
    at all, neither for `CX.ald` nor for `CS.astore`; `bsem_awaits` and
    `scorr_publish` are proved (H2/H3) and the rows are what is missing.
  * `Stmt.axiomCall`/`Block.bindAxiom` (`Hardware.annahme`) -- a foreign-call
    row plus the per-axiom `AxCorr` premise (CFormenH.lean H5), an assumption
    boundary no certificate can decide. *And the corpus has ZERO axiom calls*,
    so nothing would be gained today.
  * `Stmt.forever` (`Hardware.fortschritt`, H2) -- a loop row whose body may
    be left only through `goto m_ende`, with the watchdog line before it.
  * An `else` branch that is not a `return`: `Block.regLiesElse`'s `sonst` is
    a whole `Endblock`, and a row carrying one needs the TERMINAL-block check
    inside the BLOCK check -- a second recursion through a second type, while
    this one has to stay structural for `decide`.
  * `transition`, the bank accessors and port I/O (`inb`/`outb`): no T4 lemma.
  * A `bool` register cannot meet `GerAnnahme.rund` (`einpassen .bool` maps
    every non-zero word to `true` and `encW .bool` gives back `1`), so its
    profile is unmeetable -- a refusal by name, not a silent admission.
- THE TWO PREMISES THIS WIDENING COST, both `GT.ein = false` and both
  discharged by `rfl` at every existing call site:
  `korrOk_rufAt_ohneHardware` (§5 -- a register READ is two of the five
  sources of a hardware outcome, so the reading CANNOT hold for a device
  certificate) and `korrOk_endR` (KorrOkAdaequat.lean -- `BlockR` has both
  device constructors, but `BlockR.regReadElse` is stated at `l = false`
  while that induction runs at every `l`). `hardwareFrei` itself is
  UNTOUCHED, and `rufAt_ohneHardware` holds exactly as before for every
  program that avoids the five forms.
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
#print axioms Gabbro.Grammatik.stOkBl_hardwareFrei
#print axioms Gabbro.Grammatik.enOk_hardwareFrei
#print axioms Gabbro.Grammatik.korrOk_hardwareFrei
#print axioms Gabbro.Grammatik.korrOk_rufAt_ohneHardware
#print axioms Gabbro.Grammatik.regAdrOk_devH
#print axioms Gabbro.Grammatik.gerAnn_leer
#print axioms Gabbro.Grammatik.gerAdr_devH
#print axioms Gabbro.Grammatik.gerRund_int
#print axioms Gabbro.Grammatik.gerAcc
#print axioms Gabbro.Grammatik.gerLies_step
#print axioms Gabbro.Grammatik.gerSchreib_step
#print axioms Gabbro.Grammatik.bsem_regLies
#print axioms Gabbro.Grammatik.bsem_regLiesElse


end Gabbro.Grammatik
