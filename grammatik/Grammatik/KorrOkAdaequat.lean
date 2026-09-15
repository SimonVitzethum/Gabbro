/-
  File:      Grammatik/KorrOkAdaequat.lean
  Subject:   THE CERTIFICATE'S FRAGMENT IS INSIDE THE ADEQUACY FRAGMENT --
             measured, not eyeballed.

  Plan `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.4/§6.5 keeps one item open:
  "Part 4 speaks about `rufAt`, part 5 about machine G; their agreement for
  one active thread is the adequacy chain, not re-instantiated in the
  theorem." Four things stand between the two, and only ONE of them is the
  covered fragment. This file settles that one, in the direction that helps:

      korrOk EL fnum c P fs = true  →  ∀ g, EndR A (fun _ => True) (P.rumpf g)

  Every body a correspondence certificate accepts is a body the adequacy
  theorem's fragment `EndR`/`BlockR`/`StmtR` (`RufAdaequatRufG.lean`)
  accepts -- for EVERY lock class `A` and with the callee predicate taken
  as `True`. So the fragment is NOT the obstacle, and the report of a lane
  that wants to bring the adequacy chain into the closing theorem may say
  so with a theorem instead of a reading.

  WHAT IS STILL IN THE WAY, and none of it is this file's business:

  1. `rufG_adaequat_ruf` realises `rufRumpf`, NOT `rufAt`. `rufRumpf` runs
     the callee's body; `rufAt` also tests `requires`, `ensures` and the
     owed invariants AND READS THEIR CARRIERS -- `σ.lese … (P.requires f).orte`
     at entry, `σ'.lese … (P.ensures f).orte` at the return, one `lese` per
     owed invariant (`Semantik.lean`, `rufAt`). Machine G records none of
     those reads. So the two outcomes cannot be made EQUAL wherever a
     contract reads a carrier; they agree on memory and differ on the
     TRACE, and the trace is what `SpurInv` and race freedom are about.
     `RufAdaequatRufG.lean` §13 books this as `befund_vertrag`.
  2. `Tief P A n` admits callees BY DEPTH; a recursion deeper than `n` is
     `logik (abstieg f)` sequentially, and no claim is made. That is the
     same residue part 4's condition still carries.
  3. The adequacy is EXISTENTIAL (SOME thread-`f` run realises the outcome).
     Part 5 is universal over reachable machines.
  4. `rufG_adaequat_ruf` is stated about a machine whose thread `f` ALREADY
     stands on the body with a non-waiting caller frame
     (`hM`, `hnw`, `hΛ`, `hfrei`). Nothing in a chain says a machine
     reachable from the single-threaded start has that shape.
-/
import Grammatik.KorrespondenzAllg
import Grammatik.RufAdaequatRufG

namespace Gabbro.Grammatik

variable {D : Deklaration}

section Bruecke

variable (EL : EmitLay D) (fnum : D.Fn → Nat) (c : KCert D) (A : D.Lock → Prop)

/-- The flat statement check admits only leaves and direct calls. -/
theorem stOk0_stmtR {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (K : CEnvLay D Γ) (s : Stmt D V l Γ Λ Λ') (r : GRow)
    (h : stOk0 EL fnum c K s r = true) : StmtR A (fun _ => True) true s := by
  cases s <;> first
    | exact StmtR.blatt _ (by constructor)
    | exact StmtR.call _ _ rfl trivial
    | exact absurd h (by simp [stOk0])

/-- **The two staged checks land in the adequacy fragment**, in one
    induction on the nesting weight of the rows. -/
theorem stOkBl_stmtR : ∀ (n : Nat),
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n →
        stOk EL fnum c K₀ s r = true → StmtR A (fun _ => True) true s) ∧
    (∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
        (K₀ : CEnvLay D Γ₀) (b : Block D V l Γ₀ Λ₀ Λ₁) (rs : List GRow), rowsSize rs ≤ n →
        blOk EL fnum c K₀ b rs = true → BlockR A (fun _ => True) true b) := by
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
        | nil => exact BlockR.nil
        | _ => exact absurd h (by simp [blOk])
  | succ n ih =>
      have h1 : ∀ {V : Vertrag D} {l : Bool} {Γ₀ : Ctx} {Λ₀ Λ₁ : List (Res D)}
          (K₀ : CEnvLay D Γ₀) (s : Stmt D V l Γ₀ Λ₀ Λ₁) (r : GRow), rowSize r ≤ n + 1 →
          stOk EL fnum c K₀ s r = true → StmtR A (fun _ => True) true s := by
        intro V l Γ₀ Λ₀ Λ₁ K₀ s r hn h
        cases r with
        | ite cc tRows eRows =>
            cases s with
            | ite cnd t e =>
                simp only [stOk, Bool.and_eq_true] at h
                obtain ⟨⟨_, hT⟩, hE⟩ := h
                simp only [rowSize] at hn
                exact StmtR.ite cnd t e (ih.2 K₀ t tRows (by omega) hT)
                  (ih.2 K₀ e eRows (by omega) hE)
            | _ => exact absurd h (by simp [stOk])
        | forTrav x ti hiC bodyRows m' =>
            cases s with
            | traverse tb inv body =>
                cases hiC with
                | lit v =>
                    simp only [stOk, Bool.and_eq_true] at h
                    obtain ⟨-, hb⟩ := h
                    simp only [rowSize] at hn
                    exact StmtR.traverse tb inv body (ih.2 _ body bodyRows (by omega) hb)
                | _ => exact absurd h (by simp [stOk])
            | _ => exact absurd h (by simp [stOk])
        | _ => exact stOk0_stmtR EL fnum c A K₀ s _ h
      refine ⟨h1, ?_⟩
      intro V l Γ₀ Λ₀ Λ₁ K₀ b rs hn h
      cases rs with
      | nil =>
          cases b with
          | nil => exact BlockR.nil
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
                  exact BlockR.bind e rest (ih.2 _ rest rs' hrs h.2)
              | _ => exact absurd h (by simp [blOk])
          | call fc cargs dst =>
              cases dst with
              | none =>
                  cases b with
                  | cons s rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      exact BlockR.cons s rest (h1 K₀ s _ (by omega) h.1)
                        (ih.2 K₀ rest rs' hrs h.2)
                  | _ => exact absurd h (by simp [blOk])
              | some p =>
                  cases b with
                  | bindCall g args heq hp hrp rest =>
                      simp only [blOk, Bool.and_eq_true] at h
                      exact BlockR.bindCall g args heq hp hrp rest trivial
                        (ih.2 _ rest rs' hrs h.2)
                  | _ => exact absurd h (by simp [blOk])
          | _ =>
              cases b with
              | cons s rest =>
                  simp only [blOk, Bool.and_eq_true] at h
                  exact BlockR.cons s rest (h1 K₀ s _ (by omega) h.1)
                    (ih.2 K₀ rest rs' hrs h.2)
              | _ => exact absurd h (by simp [blOk])

/-- **A certified body is in the adequacy fragment.** -/
theorem enOk_endR (top : Bool) {V : Vertrag D} :
    ∀ (rs : List GRow) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)
      (b : Endblock D V false Γ Λ),
      enOk EL fnum c top rs K b = true → EndR A (fun _ => True) b := by
  intro rs
  induction rs with
  | nil =>
      intro Γ Λ K b h
      cases b with
      | ret e hΛ => exact EndR.ret e hΛ
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
          | ret e hΛ => exact EndR.ret e hΛ
          | _ => exact absurd hb (by simp)
      | bindLet x τc ce =>
          cases b with
          | bind e rest =>
              simp only [enOk, Bool.and_eq_true] at h
              exact EndR.bind e rest (ih _ rest h.2)
          | _ => exact absurd h (by simp [enOk])
      | _ =>
          cases b with
          | cons s rest =>
              simp only [enOk, Bool.and_eq_true] at h
              exact EndR.cons s rest
                ((stOkBl_stmtR EL fnum c A (rowSize _)).1 K s _ (Nat.le_refl _) h.1)
                (ih K rest h.2)
          | _ => exact absurd h (by simp [enOk])

/-- **THE READING**: every body of a program with a correspondence
    certificate is in the adequacy theorem's covered fragment, for every
    lock class and with the callee predicate taken as `True`. What the
    adequacy chain still needs beyond this is the DEPTH (`Tief`), and what
    it realises is `rufRumpf`, not `rufAt` (file header, 1 and 2). -/
theorem korrOk_endR {P : Programm D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hc : korrOk EL fnum c P fs = true) (g : D.Fn) :
    EndR A (fun _ => True) (P.rumpf g) := by
  obtain ⟨k, hk, hok⟩ := korrOk_fn hvoll hc g
  exact enOk_endR EL fnum c A true k.rows k.lay (P.rumpf g) hok

end Bruecke

#print axioms Gabbro.Grammatik.stOk0_stmtR
#print axioms Gabbro.Grammatik.stOkBl_stmtR
#print axioms Gabbro.Grammatik.enOk_endR
#print axioms Gabbro.Grammatik.korrOk_endR

end Gabbro.Grammatik
