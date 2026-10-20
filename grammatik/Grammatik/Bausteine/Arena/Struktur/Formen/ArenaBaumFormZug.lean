/-
  File:      Grammatik/ArenaBaumFormZug.lean
  Subject:   THE GUARDED TREE FORMS ON EXECUTED BLOCKS (PLAN-DYNAMIC.md section 8a.1, third pass): what the executed
             `abschneiden`, `wurzelSetze` and `wurzelAus` of `ArenaBaumFormG.lean` leave, and that they keep `BaumOk`.

  The guard of a form (`check`, `narrow`) is taken apart by the recognizer's soundness proof (`execBlock_check_wahr`),
  so what is proved here is about the world after the guard has passed: the store facts (`*_ausfuehren`, valid for every
  continuation) and the invariant on them (`baum_*_zug`), with the frame (`LinkRahmen`) and the membership facts the
  list/tree combination needs (a slot that leaves the tree was in it, the new members are among the old ones).
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaBaumFormG

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D} (G : LinkKopf A)

/-! ## 1. The store facts -/

/-- **`abschneiden` leaves** (the guard passed: `i = C[p]` is a slot and a leaf): the binder holds `i`, the `C` place of `p`
    is empty, no other place moves, the head stays, the allocator's views stay. Valid for every continuation. -/
theorem abschneiden_ausfuehren (Lf Rf C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hi : C.wert σ (ρ.get p).n < D.count A.tab)
    (hl : Lf.wert σ (C.wert σ (ρ.get p).n) = D.count A.tab)
    (hr : Rf.wert σ (C.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.abschneiden Lf Rf C p hwT hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [C.f] [] σ σ' ∧
      k.n = C.wert σ (ρ.get p).n ∧ C.wert σ' (ρ.get p).n = D.count A.tab ∧
      (∀ j, j ≠ (ρ.get p).n → C.wert σ' j = C.wert σ j) ∧
      (∀ C' : LinkFeld A, C'.f ≠ C.f → ∀ j, C'.wert σ' j = C'.wert σ j) ∧ G.st σ' = G.st σ ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ C.wert σ (ρ.get p).n ∧ C.wert σ (ρ.get p).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp C.hf (σ.slots A.tab (ρ.get p).n C.f)).lo_le, by omega⟩
  simp only [Block.abschneiden, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  rw [if_pos ((blattTest_wahr Lf Rf Var.here hLT _ _).mpr ⟨?_, ?_⟩)]
  · refine ⟨?s, ?k, ?e, ?rh, ?n, ?r⟩
    case e => rfl
    case rh =>
      refine ⟨fun C' hC' => funext fun j => ?_, fun G' _ => rfl⟩
      have h1 : C'.f ≠ C.f := fun e => hC' (by simp [e])
      simp [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h1]
    case n => rfl
    case r =>
      simp only [eval, Block.linkNil, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
        LinkKopf.st_schreibSlot, LinkKopf.st_lese, LinkFeld.wert_lese, A.kopfSt_schreibSlot, FreiForm.naechst_lese,
        FreiForm.kopfSt_lese, ArenaForm.stand_lese, ArenaForm.stand_schreibSlot,
        A.naechst_schreibSlot_ne _ _ _ _ _ C.h2, Env.get_cons_there, Env.get_cons_here]
      refine ⟨?_, fun j hj => ?_, fun C' hC' j => ?_, trivial, trivial, fun _ => trivial, trivial⟩
      · exact (C.wert_schreibSlot_selbst _ _ _ _).trans (umTyp_rund_n C.hf _)
      · exact C.wert_schreibSlot_anderer _ _ _ _ _ hj
      · exact C.wert_schreibSlot_feld C' hC' _ _ _ _ _
  · exact hl
  · exact hr

/-- **`wurzelSetze` leaves:** the root is `x`, both child places of `x` are empty, no other place moves, the allocator's
    views stay. Valid for every continuation. -/
theorem wurzelSetze_ausfuehren (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (hd : Lf.f ≠ Rf.f)
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.wurzelSetze Lf Rf Wz x hwT hLT hwG hLG rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [Lf.f, Rf.f] [Wz.g] σ σ' ∧
      Wz.st σ' = (ρ.get x).n ∧ Lf.wert σ' (ρ.get x).n = D.count A.tab ∧ Rf.wert σ' (ρ.get x).n = D.count A.tab ∧
      (∀ j, j ≠ (ρ.get x).n → Lf.wert σ' j = Lf.wert σ j) ∧ (∀ j, j ≠ (ρ.get x).n → Rf.wert σ' j = Rf.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  refine ⟨_, rfl, ?_, ?_⟩
  · refine ⟨fun C hC => funext fun j => ?_, fun G' hG' => ?_⟩
    · have h1 : C.f ≠ Lf.f := fun e => hC (by simp [e])
      have h2 : C.f ≠ Rf.f := fun e => hC (by simp [e])
      simp [LinkFeld.wert, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h1, World.slots_schreibSlot_ne _ _ _ _ _ _ _ _ h2]
    · have hne : G'.g ≠ Wz.g := fun e => hG' (by simp [e])
      simp [LinkKopf.st, World.globs_schreibGlob_ne _ _ _ _ _ hne]
  simp only [eval, Block.wurzelSetze, Block.linkNil, Block.linkIdxAlsKopf, eval_umTyp, Expr.orte, orte_umTyp,
    List.nil_append, LinkKopf.st_schreibSlot, LinkKopf.st_lese, LinkKopf.st_schreibGlob_selbst,
    LinkFeld.wert_schreibGlob, LinkFeld.wert_lese,
    A.kopfSt_schreibGlob_ne _ _ _ _ (Ne.symm Wz.h2), A.stand_schreibGlob_ne _ _ _ _ (Ne.symm Wz.h1),
    FreiForm.naechst_schreibGlob, A.naechst_schreibSlot_ne _ _ _ _ _ Lf.h2, A.naechst_schreibSlot_ne _ _ _ _ _ Rf.h2,
    FreiForm.naechst_lese, FreiForm.kopfSt_schreibSlot, FreiForm.kopfSt_lese, ArenaForm.stand_lese,
    ArenaForm.stand_schreibSlot]
  refine ⟨umTyp_rund_n Wz.hg _, ?_, ?_, fun j hj => ?_, fun j hj => ?_, trivial, fun _ => trivial, trivial⟩
  · simp only [LinkFeld.wert_lese, LinkFeld.wert_schreibGlob, Rf.wert_schreibSlot_feld Lf hd,
      Lf.wert_schreibSlot_selbst]
    exact umTyp_rund_n Lf.hf _
  · simp only [LinkFeld.wert_lese, LinkFeld.wert_schreibGlob, Rf.wert_schreibSlot_selbst]
    exact umTyp_rund_n Rf.hf _
  · simp only [LinkFeld.wert_lese, LinkFeld.wert_schreibGlob, Rf.wert_schreibSlot_feld Lf hd,
      Lf.wert_schreibSlot_anderer _ _ _ _ _ hj]
  · simp only [LinkFeld.wert_lese, LinkFeld.wert_schreibGlob, Rf.wert_schreibSlot_anderer _ _ _ _ _ hj,
      Lf.wert_schreibSlot_feld Rf hd.symm]

/-- **`wurzelAus` leaves** (the guard passed: the root `i` is a slot and a leaf): the binder holds `i`, the root is
    the nil marker, no link moves, the allocator's views stay. Valid for every continuation. -/
theorem wurzelAus_ausfuehren (Lf Rf : LinkFeld A) (Wz : LinkKopf A)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hi : Wz.st σ < D.count A.tab)
    (hl : Lf.wert σ (Wz.st σ) = D.count A.tab) (hr : Rf.wert σ (Wz.st σ) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.wurzelAus Lf Rf Wz hwG hLG hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [] [Wz.g] σ σ' ∧
      k.n = Wz.st σ ∧ Wz.st σ' = D.count A.tab ∧ (∀ C : LinkFeld A, ∀ j, C.wert σ' j = C.wert σ j) ∧
      A.kopfSt σ' = A.kopfSt σ ∧ (∀ j, A.naechst σ' j = A.naechst σ j) ∧ A.stand σ' = A.stand σ := by
  have hk : (0 : Int) ≤ Wz.st σ ∧ Wz.st σ ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp Wz.hg (σ.globs Wz.g)).lo_le, by omega⟩
  simp only [Block.wurzelAus, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  rw [if_pos ((blattTest_wahr Lf Rf Var.here hLT _ _).mpr ⟨?_, ?_⟩)]
  · refine ⟨?s, ?k, ?e, ?rh, ?n, ?r⟩
    case e => rfl
    case rh =>
      refine ⟨fun C _ => rfl, fun G' hG' => ?_⟩
      have hne : G'.g ≠ Wz.g := fun e => hG' (by simp [e])
      simp [LinkKopf.st, World.globs_schreibGlob_ne _ _ _ _ _ hne]
    case n => rfl
    case r =>
      simp only [eval, Block.linkNilKopf, eval_umTyp, Expr.orte, orte_umTyp, List.nil_append,
        LinkKopf.st_schreibGlob_selbst, LinkKopf.st_lese, LinkFeld.wert_schreibGlob, LinkFeld.wert_lese,
        A.kopfSt_schreibGlob_ne _ _ _ _ (Ne.symm Wz.h2), A.stand_schreibGlob_ne _ _ _ _ (Ne.symm Wz.h1),
        FreiForm.naechst_schreibGlob, FreiForm.naechst_lese, FreiForm.kopfSt_lese, ArenaForm.stand_lese]
      refine ⟨umTyp_rund_n Wz.hg _, ?_⟩
      simp
  · exact hl
  · exact hr

/-! ## 1b. The guards that fail -/

/-- **`abschneiden` with no child takes the first `else`:** nothing moves but the recorded read. -/
theorem abschneiden_voll (Lf Rf C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hn : ¬ C.wert σ (ρ.get p).n < D.count A.tab) :
    execBlock (V := V) O passes R (Block.abschneiden Lf Rf C p hwT hLT voll voll2 rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inl A.tab]) ρ).zuAusgang := by
  have hn' : ¬ ((0 : Int) ≤ C.wert σ (ρ.get p).n ∧ C.wert σ (ρ.get p).n ≤ D.count A.tab - 1) := by
    intro h; exact hn (by omega)
  simp only [Block.abschneiden, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_neg (by exact hn')]

/-- **`abschneiden` of a child that is no leaf takes the second `else`**, in the world that recorded both reads. -/
theorem abschneiden_nichtblatt (Lf Rf C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hi : C.wert σ (ρ.get p).n < D.count A.tab)
    (hnb : ¬ (Lf.wert σ (C.wert σ (ρ.get p).n) = D.count A.tab ∧ Rf.wert σ (C.wert σ (ρ.get p).n) = D.count A.tab)) :
    ∃ (k : Wert D (Ty.index (D.count A.tab))) (o2 : List (D.Tab ⊕ D.Glob)),
      execBlock (V := V) O passes R (Block.abschneiden Lf Rf C p hwT hLT voll voll2 rest) σ ρ
        = (execEnd O passes R voll2 ((σ.lese Λ [Sum.inl A.tab]).lese Λ o2) (.cons k ρ)).zuAusgang.schrumpf := by
  have hk : (0 : Int) ≤ C.wert σ (ρ.get p).n ∧ C.wert σ (ρ.get p).n ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp C.hf (σ.slots A.tab (ρ.get p).n C.f)).lo_le, by omega⟩
  simp only [Block.abschneiden, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte]
  rw [dif_pos (by exact hk)]
  refine ⟨?k, ?o2, ?eq⟩
  case eq =>
    split
    · rename_i hc
      exact absurd ((blattTest_wahr Lf Rf Var.here hLT _ _).mp hc) hnb
    · rfl

/-- **`wurzelAus` of an empty tree takes the first `else`.** -/
theorem wurzelAus_voll (Lf Rf : LinkFeld A) (Wz : LinkKopf A)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hn : ¬ Wz.st σ < D.count A.tab) :
    execBlock (V := V) O passes R (Block.wurzelAus Lf Rf Wz hwG hLG hLT voll voll2 rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ [Sum.inr Wz.g]) ρ).zuAusgang := by
  have hn' : ¬ ((0 : Int) ≤ Wz.st σ ∧ Wz.st σ ≤ D.count A.tab - 1) := by
    intro h; exact hn (by omega)
  simp only [Block.wurzelAus, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_neg (by exact hn')]

/-- **`wurzelAus` of a root that is no leaf takes the second `else`.** -/
theorem wurzelAus_nichtblatt (Lf Rf : LinkFeld A) (Wz : LinkKopf A)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hi : Wz.st σ < D.count A.tab)
    (hnb : ¬ (Lf.wert σ (Wz.st σ) = D.count A.tab ∧ Rf.wert σ (Wz.st σ) = D.count A.tab)) :
    ∃ (k : Wert D (Ty.index (D.count A.tab))) (o2 : List (D.Tab ⊕ D.Glob)),
      execBlock (V := V) O passes R (Block.wurzelAus Lf Rf Wz hwG hLG hLT voll voll2 rest) σ ρ
        = (execEnd O passes R voll2 ((σ.lese Λ [Sum.inr Wz.g]).lese Λ o2) (.cons k ρ)).zuAusgang.schrumpf := by
  have hk : (0 : Int) ≤ Wz.st σ ∧ Wz.st σ ≤ D.count A.tab - 1 :=
    ⟨(Wert.umTyp Wz.hg (σ.globs Wz.g)).lo_le, by omega⟩
  simp only [Block.wurzelAus, execBlock, eval_umTyp, orte_umTyp, eval, Expr.orte, World.globs_lese]
  rw [dif_pos (by exact hk)]
  refine ⟨?k, ?o2, ?eq⟩
  case eq =>
    split
    · rename_i hc
      exact absurd ((blattTest_wahr Lf Rf Var.here hLT _ _).mp hc) hnb
    · rfl

/-! ## 2. The tree invariant on the guarded forms -/

/-- **Executed `abschneiden` at the left keeps the tree** (the guard passed: `p` is a member, its left child `i` is a
    leaf). The binder holds `i`, live and no longer in the tree; it WAS in the tree; the new members are among the
    old ones. -/
theorem baum_abschneiden_links_zug (Lf Rf : LinkFeld A) (hd : Rf.f ≠ Lf.f)
    (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Lf.wert σ (ρ.get p).n < D.count A.tab)
    (hll : Lf.wert σ (Lf.wert σ (ρ.get p).n) = D.count A.tab)
    (hrl : Rf.wert σ (Lf.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.abschneiden Lf Rf Lf p hwT hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [Lf.f] [] σ σ' ∧
      k.n = Lf.wert σ (ρ.get p).n ∧ BaumOk A Lf Rf G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') k.n ∧ A.Lebt σ' k.n ∧
      InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) k.n ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j →
        InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j) := by
  obtain ⟨σ', k, he, hrm, hkn, hlp, hol, hoth, hg, hk, hn, hs⟩ :=
    abschneiden_ausfuehren O passes R G Lf Rf Lf p hwT hLT voll voll2 rest σ ρ hi hll hrl
  obtain ⟨h1, h2, h3⟩ := baum_blatt_aus_links A Lf Rf G hb _ _ hp rfl hi (hkn ▸ k.lo_le) hll hrl hk hn hs hg hlp hol
    (fun j => hoth Rf hd j)
  have hr : Rf.wert σ' = Rf.wert σ := funext fun j => hoth Rf hd j
  have hmem := blatt_aus_mitglieder hb hp rfl (hkn ▸ k.lo_le) hi hll hrl hlp hol
  have hin : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (Lf.wert σ (ρ.get p).n) := hp.links hi
  refine ⟨σ', k, he, hrm, hkn, h1, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hkn ▸ h2, hkn ▸ h3,
    hkn ▸ hin, fun j hj => ?_⟩
  rw [hr, hg] at hj
  exact (hmem j hj).1

/-- **Executed `abschneiden` at the right keeps the tree** (the mirror). -/
theorem baum_abschneiden_rechts_zug (Lf Rf : LinkFeld A) (hd : Lf.f ≠ Rf.f)
    (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf G σ)
    (hp : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (ρ.get p).n)
    (hi : Rf.wert σ (ρ.get p).n < D.count A.tab)
    (hll : Lf.wert σ (Rf.wert σ (ρ.get p).n) = D.count A.tab)
    (hrl : Rf.wert σ (Rf.wert σ (ρ.get p).n) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.abschneiden Lf Rf Rf p hwT hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [Rf.f] [] σ σ' ∧
      k.n = Rf.wert σ (ρ.get p).n ∧ BaumOk A Lf Rf G σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') k.n ∧ A.Lebt σ' k.n ∧
      InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) k.n ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (G.st σ') j →
        InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) j) := by
  obtain ⟨σ', k, he, hrm, hkn, hrp, hor, hoth, hg, hk, hn, hs⟩ :=
    abschneiden_ausfuehren O passes R G Lf Rf Rf p hwT hLT voll voll2 rest σ ρ hi hll hrl
  obtain ⟨h1, h2, h3⟩ := baum_blatt_aus_rechts A Lf Rf G hb _ _ hp rfl hi (hkn ▸ k.lo_le) hll hrl hk hn hs hg hrp hor
    (fun j => hoth Lf hd j)
  have hl : Lf.wert σ' = Lf.wert σ := funext fun j => hoth Lf hd j
  have hmem := blatt_aus_rechts_mitglieder hb hp rfl (hkn ▸ k.lo_le) hi hll hrl hrp hor
  have hin : InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (G.st σ) (Rf.wert σ (ρ.get p).n) := hp.rechts hi
  refine ⟨σ', k, he, hrm, hkn, h1, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, hkn ▸ h2, hkn ▸ h3,
    hkn ▸ hin, fun j hj => ?_⟩
  rw [hl, hg] at hj
  exact (hmem j hj).1

/-- **Executed `wurzelSetze` keeps the tree:** the tree was empty (`Wz.st σ = count`), `x` is live; the new tree is `{x}`. -/
theorem baum_wurzel_ein_zug (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (hd : Lf.f ≠ Rf.f)
    (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hi : A.Lebt σ (ρ.get x).n) :
    ∃ σ' : World D,
      execBlock (V := V) O passes R (Block.wurzelSetze Lf Rf Wz x hwT hLT hwG hLG rest) σ ρ
          = execBlock (V := V) O passes R rest σ' ρ ∧
      LinkRahmen A [Lf.f, Rf.f] [Wz.g] σ σ' ∧
      BaumOk A Lf Rf Wz σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      (∀ j, InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (Wz.st σ') j ↔ j = (ρ.get x).n) := by
  obtain ⟨σ', he, hrm, hg, hli, hri, -, -, hk, hn, hs⟩ :=
    wurzelSetze_ausfuehren O passes R Lf Rf Wz hd x hwT hLT hwG hLG rest σ ρ
  have hmono : ∀ j, A.Lebt σ j → A.Lebt σ' j := fun j h => (A.lebt_gleich hk hn hs j).mpr h
  have hc : (ρ.get x).n < D.count A.tab := by have := hi.2.1; have := A.stand_le σ; omega
  have key := wurzel_ein_ok (c := D.count A.tab) (l' := Lf.wert σ') (r' := Rf.wert σ') (Live' := A.Lebt σ')
    (i := (ρ.get x).n) hi.1 hc (hmono _ hi) hli hri
  refine ⟨σ', he, hrm, ?_, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, ?_⟩
  · unfold BaumOk; rw [hg]; exact key.1
  · rw [hg]; exact key.2

/-- **Executed `wurzelAus` keeps the tree** (the guard passed: the root `i` is a slot and a leaf): the tree is empty
    afterwards, the binder holds `i`, live, and it WAS in the tree. -/
theorem baum_wurzel_aus_zug (Lf Rf : LinkFeld A) (Wz : LinkKopf A)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (hLT : darf D A.tab Λ)
    (voll : Endblock D V l Γ Λ) (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ) (hok : A.FreiOk σ) (hb : BaumOk A Lf Rf Wz σ)
    (hi : Wz.st σ < D.count A.tab)
    (hl : Lf.wert σ (Wz.st σ) = D.count A.tab) (hr : Rf.wert σ (Wz.st σ) = D.count A.tab) :
    ∃ (σ' : World D) (k : Wert D (Ty.index (D.count A.tab))),
      execBlock (V := V) O passes R (Block.wurzelAus Lf Rf Wz hwG hLG hLT voll voll2 rest) σ ρ
          = (execBlock (V := V) O passes R rest σ' (.cons k ρ)).schrumpf ∧
      LinkRahmen A [] [Wz.g] σ σ' ∧
      k.n = Wz.st σ ∧ BaumOk A Lf Rf Wz σ' ∧ A.FreiOk σ' ∧ (∀ j, A.Lebt σ' j ↔ A.Lebt σ j) ∧
      (∀ j, ¬ InBaum (D.count A.tab) (Lf.wert σ') (Rf.wert σ') (Wz.st σ') j) ∧ A.Lebt σ' k.n ∧
      InBaum (D.count A.tab) (Lf.wert σ) (Rf.wert σ) (Wz.st σ) k.n := by
  obtain ⟨σ', k, he, hrm, hkn, hg, hol, hk, hn, hs⟩ :=
    wurzelAus_ausfuehren O passes R Lf Rf Wz hwG hLG hLT voll voll2 rest σ ρ hi hl hr
  have hlive : A.Lebt σ k.n := by
    rw [hkn]; exact ArenaKette.BaumOkF.lebt_in hb (InBaum.wurzel hb hi)
  have hl' : Lf.wert σ' = Lf.wert σ := funext (hol Lf)
  have hr' : Rf.wert σ' = Rf.wert σ := funext (hol Rf)
  have key := wurzel_aus_ok (c := D.count A.tab) (l := Lf.wert σ') (r := Rf.wert σ') (Live := A.Lebt σ')
  refine ⟨σ', k, he, hrm, hkn, ?_, A.freiOk_gleich hk hn hs hok, A.lebt_gleich hk hn hs, ?_,
    (A.lebt_gleich hk hn hs _).mpr hlive, by rw [hkn]; exact InBaum.wurzel (Live := A.Lebt σ) hb hi⟩
  · unfold BaumOk; rw [hg]; exact key.1
  · rw [hg]; exact key.2

end Bedeutung

end Gabbro.Grammatik
