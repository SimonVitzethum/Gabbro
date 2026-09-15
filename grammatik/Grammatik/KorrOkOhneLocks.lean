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

theorem stOk0_ohneLocks {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (K : CEnvLay D Γ) (s : Stmt D V l Γ Λ Λ') (r : GRow)
    (h : stOk0 EL fnum c K s r = true) : s.ohneLocks = true := by
  cases s <;> first | rfl | (exact absurd h (by simp [stOk0]))

/-- **The two staged checks refuse every `locks` block**,
    in one induction on the nesting weight of the rows. -/
theorem stOkBl_ohneLocks : ∀ (n : Nat),
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n →
        stOk EL fnum c K₀ s r = true → s.ohneLocks = true) ∧
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (b : Block D V l Γ₀ Λ₀ Λ₁) (rs : List GRow), rowsSize rs ≤ n →
        blOk EL fnum c K₀ b rs = true → b.ohneLocks = true) := by
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
          stOk EL fnum c K₀ s r = true → s.ohneLocks = true := by
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
        | _ => exact stOk0_ohneLocks EL fnum c K₀ s _ h
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
theorem enOk_ohneLocks (top : Bool) {V : Vertrag D} {l : Bool} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ) (b : Endblock D V l Γ Λ),
      enOk EL fnum c top rs K b = true → b.ohneLocks = true := by
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
              exact ⟨(stOkBl_ohneLocks EL fnum c (rowSize _)).1 K s _ (Nat.le_refl _) h.1,
                ih K rest h.2⟩
          | _ => exact absurd h (by simp [enOk])


/-- **THE READING FOR THE CLOSING THEOREM**: every body of a program with a
    correspondence certificate that checks carries no `locks` block -- so its
    `execEndH` semantics IS its `execEnd` semantics, for every environment
    move, and the user obligation applies to the run `rufAt` makes. -/
theorem korrOk_ohneLocks {P : Programm D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true) (g : D.Fn) :
    (P.rumpf g).ohneLocks = true := by
  obtain ⟨k, hk, hok⟩ := korrOk_fn hvoll hc g
  exact enOk_ohneLocks EL fnum c true k.rows k.lay (P.rumpf g) hok

end OhneLocksLesen

#print axioms Gabbro.Grammatik.enOk_ohneLocks
#print axioms Gabbro.Grammatik.korrOk_ohneLocks

end Gabbro.Grammatik
