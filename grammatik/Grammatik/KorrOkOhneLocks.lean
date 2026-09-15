/-
  File:      Grammatik/KorrOkOhneLocks.lean
  Subject:   **A CERTIFIED BODY CARRIES NO `locks` BLOCK** -- read off the
             correspondence check, by the same induction as
             `korrOk_hardwareFrei` (KorrespondenzAllg.lean section 5).

  WHY IT IS NEEDED. The user obligation `KoerperGutS` (SperreFuss.lean) is
  stated over `execEndH`, the body semantics WITH acquire moves and release
  checks, quantified over every environment move in `HavocOk S`. `rufAt` runs
  `execEnd`, which has neither. The two agree on a body without `locks`
  (`Endblock.execH_ohne`, SperreSem.lean), and a body a correspondence
  certificate accepts is such a body: `GRow` has no row for an acquire, so
  `stOk0` answers `false` on `Stmt.locks` -- the same reading as for the five
  oracle forms.

  THE DEVICE ROWS (2026-09-16, `OPUS-BERICHT-GERAET.md`). `korrOk` carries
  three rows for a device since that day, and the reading below holds for ALL
  of them and for EVERY device table `GT` -- it is NOT guarded, and it must
  not be, because each of the three genuinely carries no `locks` block and for
  its own reason:

  * `GRow.storeReg` (`R = e;`) meets `Stmt.regSchreib`, a LEAF statement that
    carries no block at all (`Stmt.ohneLocks`'s catch-all);
  * `GRow.loadReg` (`T x = (*(volatile T *)(cp));`) meets `Block.regLies`,
    a BINDER that continues: `Block.ohneLocks (.regLies …) = rest.ohneLocks`,
    so the question is handed to the rows after it and answered there;
  * `GRow.loadRegElse` meets `Block.regLiesElse`, which owes TWO --
    `sonst.ohneLocks && rest.ohneLocks`. The `rest` half is the binder's
    again; the `sonst` half is free because the check admits only
    `Endblock.ret` there (`sonstOk`, KorrespondenzAllg.lean section 1), and a
    `return` carries no block. *If the `else` channel is ever widened past a
    `return`, THIS is the line that has to be re-read* -- a widened `sonst`
    could hold a `locks`, and the theorem would then be false, not merely
    unproved.

  That is why the three rows get three explicit branches below and not a
  catch-all: a catch-all would have to answer for a form it cannot see, and
  when the rows arrived it did exactly that -- it read `h.1` off a `false`.

  This is NOT a new argument, it is the check read twice. The file is separate
  from `KorrespondenzAllg.lean` so that the reading and the check stay in
  different hands.
-/
import Grammatik.KorrespondenzAllg
import Grammatik.RufLogik

namespace Gabbro.Grammatik

variable {D : Deklaration}

section OhneLocksLesen

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D)

/-- The flat check admits no `locks`: `GRow` has no row for an acquire, and
    the one flat DEVICE row it does have (`storeReg`) meets `Stmt.regSchreib`,
    a leaf that carries no block -- so that arm answers `rfl`, not `absurd`. -/
theorem stOk0_ohneLocks (GT : GerTafel D) {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (K : CEnvLay D Γ) (s : Stmt D V l Γ Λ Λ') (r : GRow)
    (h : stOk0 EL fnum c K s r GT = true) : s.ohneLocks = true := by
  cases s <;> first | rfl | (exact absurd h (by simp [stOk0]))

/-- **The two staged checks refuse every `locks` block**,
    in one induction on the nesting weight of the rows. -/
theorem stOkBl_ohneLocks (GT : GerTafel D) : ∀ (n : Nat),
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n →
        stOk EL fnum c K₀ s r GT = true → s.ohneLocks = true) ∧
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (b : Block D V l Γ₀ Λ₀ Λ₁) (rs : List GRow), rowsSize rs ≤ n →
        blOk EL fnum c K₀ b rs GT = true → b.ohneLocks = true) := by
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
          stOk EL fnum c K₀ s r GT = true → s.ohneLocks = true := by
        intro V l Γ₀ Λ₀ Λ₁ K₀ s r hn h
        cases r with
        | ite cc tRows eRows =>
            cases s with
            | ite cnd t e =>
                simp only [stOk, Bool.and_eq_true] at h
                obtain ⟨⟨_, hT⟩, hE⟩ := h
                simp only [rowSize] at hn
                simp only [Stmt.ohneLocks, Bool.and_eq_true]
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
        | _ => exact stOk0_ohneLocks EL fnum c GT K₀ s _ h
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
          -- `T x = (*(volatile T *)(cp));` -- A DEVICE READ CARRIES NO BLOCK.
          -- `Block.regLies` binds the machine's answer and CONTINUES, and
          -- `Block.ohneLocks (.regLies …) = rest.ohneLocks`: the question is
          -- handed to the rows after it, exactly as at a `let`.
          | loadReg y τc cp w =>
              cases b with
              | regLies rg hkl rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  exact ih.2 _ rest rs' hrs h.2
              | _ => exact absurd h (by simp [blOk])
          -- `T x = (*(volatile T *)(cp)); if (!(c)) { return e; }` -- THE
          -- CHECKED device read owes TWO: `sonst.ohneLocks && rest.ohneLocks`.
          -- `rest` is the binder's again; `sonst` is free because the check
          -- admits only `Endblock.ret` there (`sonstOk`), and a `return`
          -- carries no block. *A widened `else` channel would have to be read
          -- here again* -- it could hold a `locks`, and then this branch is
          -- false and not merely unproved.
          | loadRegElse y τc cp w cc crr =>
              cases b with
              | regLiesElse rg hkl zusage sonst rest =>
                  cases sonst with
                  | ret e0 hΛ =>
                      simp only [blOk, sonstOk, Bool.and_eq_true] at h
                      have hrest := ih.2 _ rest rs' hrs h.2
                      simp [Block.ohneLocks, Endblock.ohneLocks, hrest]
                  | _ => exact absurd h (by simp [blOk, sonstOk])
              | _ => exact absurd h (by simp [blOk])
          | call fc cargs dst =>
              cases dst with
              | none =>
                  cases b with
                  | cons s rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      simp only [Block.ohneLocks, Bool.and_eq_true]
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
                  simp only [Block.ohneLocks, Bool.and_eq_true]
                  exact ⟨h1 K₀ s _ (by omega) h.1, ih.2 K₀ rest rs' hrs h.2⟩
              | _ => exact absurd h (by simp [blOk])

/-- **A certified body carries no `locks` block.** -/
theorem enOk_ohneLocks (GT : GerTafel D) (top : Bool) {V : Vertrag D} {l : Bool} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ),
      enOk EL fnum c top rs K b GT = true → b.ohneLocks = true := by
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
              simp only [Endblock.ohneLocks, Bool.and_eq_true]
              exact ⟨(stOkBl_ohneLocks EL fnum c GT (rowSize _)).1 K s _ (Nat.le_refl _) h.1,
                ih K rest h.2⟩
          | _ => exact absurd h (by simp [enOk])


/-- **THE READING FOR THE CLOSING THEOREM**: every body of a program with a
    correspondence certificate that checks carries no `locks` block -- so its
    `execEndH` semantics IS its `execEnd` semantics, for every environment
    move, and the user obligation applies to the run `rufAt` makes. -/
theorem korrOk_ohneLocks {P : Programm D} {fs : List D.Fn} {GT : GerTafel D}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs GT = true) (g : D.Fn) :
    (P.rumpf g).ohneLocks = true := by
  obtain ⟨k, hk, hok⟩ := korrOk_fn hvoll hc g
  exact enOk_ohneLocks EL fnum c GT true k.rows k.lay (P.rumpf g) hok

end OhneLocksLesen

#print axioms Gabbro.Grammatik.stOk0_ohneLocks
#print axioms Gabbro.Grammatik.stOkBl_ohneLocks
#print axioms Gabbro.Grammatik.enOk_ohneLocks
#print axioms Gabbro.Grammatik.korrOk_ohneLocks

end Gabbro.Grammatik
