/- Part 4 of 5 of `KorrespondenzAllg` (split by instrumente/teile/lean-teilen.py; the umbrella `KorrespondenzAllg.lean` imports all parts). -/
import Grammatik.Korrespondenz.Allgemein.KorrespondenzAllg.T3

namespace Gabbro.Grammatik

variable {D : Deklaration}

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
theorem stOk0_sound (hF : AlleRufe X fnum c) (GT : GerTafel D)
    (hP : GerAnnahme X.EL X.orc X.O GT) :
    ∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
      (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow),
      stOk0 X.EL fnum c K₀ s r GT = true → StmtCorr X mm K₀ s (growRow r) := by
  intro mm V l Γ₀ Λ₀ Λ₁ K₀ s r h
  cases s with
  | assignThru p t ht f i e hw hL =>
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
  | regWrite rg hkl e =>
      cases r with
      | storeReg cp w ce =>
          simp only [stOk0, Bool.and_eq_true] at h
          obtain ⟨⟨hadr, hw⟩, he⟩ := h
          have hw' : w = GT.wid rg := of_decide_eq_true hw
          subst hw'
          exact gerSchreib_step X hP mm K₀ rg hkl hadr (exOk_sound X K₀ e ce he)
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
theorem stOkBl_sound (hF : AlleRufe X fnum c) (GT : GerTafel D)
    (hP : GerAnnahme X.EL X.orc X.O GT) : ∀ (n : Nat),
    (∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n →
        stOk X.EL fnum c K₀ s r GT = true → StmtCorr X mm K₀ s (growRow r)) ∧
    (∀ (mm : Nat) {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (b : Block D V l Γ₀ Λ₀ Λ₁) (rs : List GRow), rowsSize rs ≤ n →
        blOk X.EL fnum c K₀ b rs GT = true → BlockCorr X mm K₀ b (growsCS rs .skip)) := by
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
          stOk X.EL fnum c K₀ s r GT = true → StmtCorr X mm K₀ s (growRow r) := by
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
        | _ => exact stOk0_sound X fnum c hF GT hP mm K₀ s _ h
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
          | loadReg y τc cp w =>
              cases b with
              | regRead rg hkl rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  obtain ⟨⟨⟨⟨⟨⟨-, hK⟩, hfr⟩, hfit⟩, hadr⟩, hw⟩, hrest⟩ := h
                  have hw' : w = GT.wid rg := of_decide_eq_true hw
                  subst hw'
                  exact BlockCorr.sem (bsem_regLies X hP mm K₀ rg hkl rest hadr hfit hK hfr
                    (cCorr_block X mm (ih.2 mm _ rest rs' hrs hrest)))
              | _ => exact absurd h (by simp [blOk])
          | loadRegElse y τc cp w cc crr =>
              cases b with
              | regReadElse rg hkl zusage sonst rest =>
                  cases sonst with
                  | ret e0 hΛ =>
                      simp only [blOk, sonstOk, Bool.and_eq_true] at h
                      obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hK⟩, hfr⟩, hfit⟩, hadr⟩, hw⟩, hzus⟩, herg⟩, hrest⟩ := h
                      have hw' : w = GT.wid rg := of_decide_eq_true hw
                      subst hw'
                      exact BlockCorr.sem (bsem_regLiesElse X hP mm K₀ rg hkl zusage e0 hΛ rest
                        hadr hfit hK hfr (exOk_sound X _ zusage cc hzus)
                        (ergOk_sound X K₀ e0 crr herg)
                        (cCorr_block X mm (ih.2 mm _ rest rs' hrs hrest)))
                  | _ => exact absurd h (by simp [blOk, sonstOk])
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
theorem stOk_sound (hF : AlleRufe X fnum c) (GT : GerTafel D)
    (hP : GerAnnahme X.EL X.orc X.O GT) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} :
    ∀ (s : Stmt D V l Γ Λ Λ') (r : GRow), stOk X.EL fnum c K s r GT = true →
      StmtCorr X m K s (growRow r) :=
  fun s r h => (stOkBl_sound X fnum c hF GT hP (rowSize r)).1 m K s r (Nat.le_refl _) h

/-- **Soundness of the block check.** -/
theorem blOk_sound (hF : AlleRufe X fnum c) (GT : GerTafel D)
    (hP : GerAnnahme X.EL X.orc X.O GT) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)} :
    ∀ (b : Block D V l Γ Λ Λ') (rs : List GRow), blOk X.EL fnum c K b rs GT = true →
      BlockCorr X m K b (growsCS rs .skip) :=
  fun b rs h => (stOkBl_sound X fnum c hF GT hP (rowsSize rs)).2 m K b rs (Nat.le_refl _) h

/-- **Soundness of the body check**: the rows elaborate to C that the Gabbro
    body corresponds to (`EndCorr`). -/
theorem enOk_sound (hF : AlleRufe X fnum c) (GT : GerTafel D)
    (hP : GerAnnahme X.EL X.orc X.O GT) (top : Bool) {V : Vertrag D} {l : Bool} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ),
      enOk X.EL fnum c top rs K b GT = true → EndCorr X m top K b (endCS rs) := by
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
              exact EndCorr.cons (stOk_sound X m K fnum c hF GT hP s _ h.1) (ih K rest h.2)
          | _ => exact absurd h (by simp [enOk])

end SoundS
/-! ## 4. Every call depth: the callee relation of every certified function -/

section Tiefe

theorem korrOk_fn {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} {GT : GerTafel D} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hc : korrOk EL fnum c P fs GT = true) (g : D.Fn) :
    ∃ k, c[fnum g]? = some k ∧ enOk EL fnum c true k.rows k.lay (P.rumpf g) GT = true := by
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
    {fs : List D.Fn} {GT : GerTafel D} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hc : korrOk EL fnum c P fs GT = true)
    (orc : DevOrc) (XR : CCallR) (O : Orakel D) (passes : Nat)
    (hP : GerAnnahme EL orc O GT) :
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
        (cCorr_end X 0 true (enOk_sound X 0 fnum c hF GT hP true k.rows k.lay (P.rumpf g) hok))

/-- **EVERY RUN**: under a checking certificate, from a C state related to
    the Gabbro world and C arguments related to the Gabbro arguments, when the
    Gabbro call at depth `n` ends in no model error, the C call has a run, and
    -- the C semantics being deterministic -- EVERY run of it ends related to
    the Gabbro outcome. -/
theorem korrOk_jeder_lauf {EL : EmitLay D} {fnum : D.Fn → Nat} {c : KCert D} {P : Programm D}
    {fs : List D.Fn} {GT : GerTafel D} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hc : korrOk EL fnum c P fs GT = true)
    (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional) (O : Orakel D) (passes n : Nat)
    (hP : GerAnnahme EL orc O GT)
    (g : D.Fn) (k : KFun D) (hk : c[fnum g]? = some k) (σ : World D) (st : CSt)
    (ρG : Env D (D.params g)) (vs : List CVal) (ρ0 : CLok) (hw : corrW EL σ st)
    (hb : bindParams k.params vs = some ρ0) (hr : EnvRel EL k.lay ρG ρ0)
    (hnf : (rufAt P O passes n g σ ρG).istFehler = false) :
    (∃ st' rv, CallAt EL.lay orc XR (kProg c) n (fnum g) st vs st' rv) ∧
      ∀ st' rv, CallAt EL.lay orc XR (kProg c) n (fnum g) st vs st' rv →
        RufOut EL (rufAt P O passes n g σ ρG) st' rv := by
  obtain ⟨st1, rv1, hC1, hO1⟩ := korrOk_fnCorr hvoll hc orc XR O passes hP n g k hk σ st ρG vs ρ0 hw hb hr hnf
  refine ⟨⟨st1, rv1, hC1⟩, fun st' rv hC => ?_⟩
  obtain ⟨e1, e2⟩ := callAt_funktional EL.lay orc XR hXR (kProg c) n (fnum g) st vs st1 rv1 st' rv hC1 hC
  subst e1
  subst e2
  exact hO1

end Tiefe
/-! ## 5. What the check ALSO decides: no oracle form in any certified body

    The check was written to decide the C correspondence, and it decides a
    second thing on the way, which the closing theorem needs: a certified
    body carries NONE of the five forms whose outcome is `hardware`
    (`RufOhneHardware.lean`). That is not a new argument -- every one of
    them is outside the covered set, so `stOk0`/`blOk` answer `false` --
    but it has to be read off the check, and the reading is the induction
    below, on the same measure `stOkBl_sound` runs on. -/


end Gabbro.Grammatik
