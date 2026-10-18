/-
  File:      Grammatik/Gen/Erzeuger/AnweisungVollst.lean
  Subject:   COMPLETENESS of the statement generator, one step: if the statements, blocks and end blocks of
             size at most `m` are all generated (`Vollst V m`), then so are the statements of size at most
             `m + 1`. The proof cases on the statement; a constructor without a clause stops the build.
-/
import Grammatik.Gen.Erzeuger.Block

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] {V : Vertrag D}

/-- The induction hypothesis: everything of size at most `m` is generated at fuel `m`. -/
def Vollst (V : Vertrag D) (m : Nat) : Prop :=
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'),
      groesseStmt s ≤ m → (⟨Λ', s⟩ : SS D V l Γ Λ) ∈ (genRek V m).st l Γ Λ) ∧
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'),
      groesseBlock b ≤ m → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ (genRek V m).bl l Γ Λ) ∧
  (∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (e : Endblock D V l Γ Λ),
      groesseEnd e ≤ m → e ∈ (genRek V m).en l Γ Λ)

/-- Close `x ∈ stmtS ...` from `hc : x ∈ clause`. -/
macro "stm_fin " h:ident : tactic =>
  `(tactic| (unfold stmtS; simp only [List.mem_append]; simp only [$h:ident, or_true, true_or]))

/-- The expressions of size at most `m` are generated at fuel `m`. -/
theorem hx_aus (m : Nat) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (h : groesseExpr e ≤ m) :
    (⟨τ, e⟩ : SE D Γ Λ) ∈ genExpr m Γ Λ := genExpr_vollst m Γ Λ τ e h

set_option maxHeartbeats 8000000 in
theorem stmt_schritt {m : Nat} (ih : Vollst V m) :
    ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'),
      groesseStmt s ≤ m + 1 → (⟨Λ', s⟩ : SS D V l Γ Λ) ∈ (genRek V (m + 1)).st l Γ Λ := by
  obtain ⟨ihS, ihB, ihE⟩ := ih
  intro l Γ Λ Λ' s h
  show _ ∈ stmtS m (genRek V m) l Γ Λ
  have hexa : ∀ {Γ : Ctx} {Λ : List (Res D)} (τs : List Ty) (a : Args D Γ Λ τs), groesseArgs a ≤ m + 1 →
      a ∈ genArgs (genExpr m Γ Λ) τs := fun τs a ha => mem_genArgs (fun τ e he => hx_aus m e he) τs a ha
  cases s with
  | assignSlot t f i e hw hL =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .assignSlot t f i e hw hL⟩ : SS D V l Γ Λ) ∈ sAssignSlot m l Γ Λ :=
      List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f,
        List.mem_flatMap.2 ⟨i, mem_ofTy (hx_aus m i (by omega)), List.mem_flatMap.2 ⟨e,
          mem_ofTy (hx_aus m e (by omega)), by rw [dif_pos hw, dif_pos hL]; simp⟩⟩⟩⟩
    stm_fin hc
  | assignThru p t ht f i e hw hL =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .assignThru p t ht f i e hw hL⟩ : SS D V l Γ Λ) ∈ sAssignThru m l Γ Λ :=
      mem_mitPtrT (hx_aus m p (by omega)) (List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, by
        rw [dif_pos ht]
        exact List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f, List.mem_flatMap.2 ⟨i,
          mem_ofTy (hx_aus m i (by omega)), List.mem_flatMap.2 ⟨e, mem_ofTy (hx_aus m e (by omega)),
            by rw [dif_pos hw, dif_pos hL]; simp⟩⟩⟩⟩)
    stm_fin hc
  | assignGlob g e hw hL =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .assignGlob g e hw hL⟩ : SS D V l Γ Λ) ∈ sAssignGlob m l Γ Λ :=
      List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, List.mem_flatMap.2 ⟨e, mem_ofTy (hx_aus m e (by omega)),
        by rw [dif_pos hw, dif_pos hL]; simp⟩⟩
    stm_fin hc
  | putBytes t f hf n i hlo hhi e hw hL =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .putBytes t f hf n i hlo hhi e hw hL⟩ : SS D V l Γ Λ) ∈ sPutBytes m l Γ Λ :=
      List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f, by
        rw [dif_pos hf]
        exact List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega),
          mem_mitIntR (hx_aus m i (by omega)) (by
            rw [dif_pos hlo, dif_pos hhi]
            exact List.mem_flatMap.2 ⟨e, mem_ofTy (hx_aus m e (by omega)),
              by rw [dif_pos hw, dif_pos hL]; simp⟩)⟩⟩⟩
    stm_fin hc
  | assignVar x e =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .assignVar x e⟩ : SS D V l Γ Λ) ∈ sAssignVar m l Γ Λ :=
      List.mem_flatMap.2 ⟨⟨_, x⟩, genVar_vollst _ _ x,
        List.mem_map.2 ⟨e, mem_ofTy (hx_aus m e (by omega)), rfl⟩⟩
    stm_fin hc
  | shift t f hτ i von nach hn he hw hL =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .shift t f hτ i von nach hn he hw hL⟩ : SS D V l Γ Λ) ∈ sShift m l Γ Λ :=
      List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨f, Aufz.feld_mem t f,
        mem_mitTypInt hτ (List.mem_flatMap.2 ⟨i, mem_ofTy (hx_aus m i (by omega)),
          List.mem_flatMap.2 ⟨von, mem_ints (by omega), List.mem_flatMap.2 ⟨nach, mem_ints (by omega),
            by rw [dif_pos hn, dif_pos he, dif_pos hw, dif_pos hL]; simp⟩⟩⟩)⟩⟩
    stm_fin hc
  | ite c t e =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .ite c t e⟩ : SS D V l Γ Λ) ∈ sIte m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨c, mem_ofTy (hx_aus m c (by omega)),
        List.mem_flatMap.2 ⟨⟨_, t⟩, ihB _ _ _ _ t (by omega),
          List.mem_map.2 ⟨e, mem_ofTy (ihB _ _ _ _ e (by omega)), rfl⟩⟩⟩
    stm_fin hc
  | onOption o p a =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .onOption o p a⟩ : SS D V l Γ Λ) ∈ sOnOption m (genRek V m) l Γ Λ :=
      mem_mitOptR (hx_aus m o (by omega)) (List.mem_flatMap.2 ⟨⟨_, p⟩, ihB _ _ _ _ p (by omega),
        List.mem_map.2 ⟨a, mem_ofTy (ihB _ _ _ _ a (by omega)), rfl⟩⟩)
    stm_fin hc
  | onTag v arms =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .onTag v arms⟩ : SS D V l Γ Λ) ∈ sOnTag m (genRek V m) l Γ Λ :=
      mem_mitSumR (hx_aus m v (by omega)) (List.mem_map.2 ⟨⟨_, arms⟩,
        mem_genArms (fun l Γ Λ Λ' b hb => ihB l Γ Λ Λ' b hb) arms (by omega), rfl⟩)
    stm_fin hc
  | onWhy r arms =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .onWhy r arms⟩ : SS D V l Γ Λ) ∈ sOnWhy m (genRek V m) l Γ Λ :=
      mem_mitWhyR (hx_aus m r (by omega)) (List.mem_map.2 ⟨⟨_, arms⟩,
        mem_genGrundArms (fun l Γ Λ Λ' b hb => ihB l Γ Λ Λ' b hb) arms (by omega), rfl⟩)
    stm_fin hc
  | call f args hp hr =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .call f args hp hr⟩ : SS D V l Γ Λ) ∈ sCall m l Γ Λ :=
      List.mem_flatMap.2 ⟨f, Aufz.fn_mem f, List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        by rw [dif_pos hp, dif_pos hr]; simp⟩⟩
    stm_fin hc
  | callInd p args hp hr =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .callInd p args hp hr⟩ : SS D V l Γ Λ) ∈ sCallInd m l Γ Λ :=
      mem_mitFnptrR (hx_aus m p (by omega)) (List.mem_flatMap.2 ⟨args, hexa _ args (by omega),
        by rw [dif_pos hp, dif_pos hr]; simp⟩)
    stm_fin hc
  | locks L hr body =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .locks L hr body⟩ : SS D V l Γ Λ) ∈ sLocks (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨L, Aufz.lock_mem L, by
        rw [dif_pos hr]
        exact List.mem_map.2 ⟨body, mem_ofTy (ihB _ _ _ _ body (by omega)), rfl⟩⟩
    stm_fin hc
  | breaking i body =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .breaking i body⟩ : SS D V l Γ Λ) ∈ sBreaking (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨i, Aufz.inv_mem i, List.mem_map.2 ⟨⟨_, body⟩, ihB _ _ _ _ body (by omega), rfl⟩⟩
    stm_fin hc
  | traverse t inv body =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .traverse t inv body⟩ : SS D V l Γ Λ) ∈ sTraverse m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨t, Aufz.tab_mem t, List.mem_flatMap.2 ⟨inv, mem_ofTy (hx_aus m inv (by omega)),
        List.mem_map.2 ⟨body, mem_ofTy (ihB _ _ _ _ body (by omega)), rfl⟩⟩⟩
    stm_fin hc
  | retry n bis body ueb =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .retry n bis body ueb⟩ : SS D V l Γ Λ) ∈ sRetry m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨n, List.mem_range.2 (by omega), List.mem_flatMap.2 ⟨bis,
        mem_ofTy (hx_aus m bis (by omega)), List.mem_flatMap.2 ⟨body,
          mem_ofTy (ihB _ _ _ _ body (by omega)), List.mem_map.2 ⟨ueb,
            mem_ofTy (ihB _ _ _ _ ueb (by omega)), rfl⟩⟩⟩⟩
    stm_fin hc
  | forever a inv body =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .forever a inv body⟩ : SS D V l Γ Λ) ∈ sForever m (genRek V m) l Γ Λ :=
      List.mem_flatMap.2 ⟨a, Aufz.annahme_mem a, List.mem_flatMap.2 ⟨inv, mem_ofTy (hx_aus m inv (by omega)),
        List.mem_map.2 ⟨body, mem_ofTy (ihB _ _ _ _ body (by omega)), rfl⟩⟩⟩
    stm_fin hc
  | axiomCall a args hae hw hg hd hgd =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .axiomCall a args hae hw hg hd hgd⟩ : SS D V l Γ Λ) ∈ sAxiomCall m l Γ Λ :=
      List.mem_flatMap.2 ⟨a, Aufz.ax_mem a, List.mem_flatMap.2 ⟨args, hexa _ args (by omega), by
        rw [dif_pos hae, dif_pos hw, dif_pos hg, dif_pos hd, dif_pos hgd]; simp⟩⟩
    stm_fin hc
  | regWrite r hk e =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .regWrite r hk e⟩ : SS D V l Γ Λ) ∈ sRegWrite m l Γ Λ :=
      List.mem_flatMap.2 ⟨r, Aufz.reg_mem r, List.mem_flatMap.2 ⟨e, mem_ofTy (hx_aus m e (by omega)),
        by rw [dif_pos hk]; simp⟩⟩
    stm_fin hc
  | transition r hk m' hm hl maske bits =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .transition r hk m' hm hl maske bits⟩ : SS D V l Γ Λ) ∈ sTransition m l Γ Λ :=
      List.mem_flatMap.2 ⟨r, Aufz.reg_mem r, List.mem_flatMap.2 ⟨m', Aufz.reg_mem m', by
        rw [dif_pos hk, dif_pos hm, dif_pos hl]
        exact List.mem_flatMap.2 ⟨maske, mem_ints (by omega),
          List.mem_map.2 ⟨bits, mem_ints (by omega), rfl⟩⟩⟩⟩
    stm_fin hc
  | publish g e payload hp hw hL =>
    simp only [groesseStmt] at h
    subst hp
    have hc : (⟨_, .publish g e (D.nutzlast g) rfl hw hL⟩ : SS D V l Γ Λ) ∈ sPublish m l Γ Λ :=
      List.mem_flatMap.2 ⟨g, Aufz.glob_mem g, List.mem_flatMap.2 ⟨e, mem_ofTy (hx_aus m e (by omega)),
        by rw [dif_pos hw, dif_pos hL]; simp⟩⟩
    stm_fin hc
  | advances mk a hmem hs =>
    have hc : (⟨_, .advances mk a hmem hs⟩ : SS D V l Γ Λ) ∈ sAdvances l Γ Λ :=
      List.mem_flatMap.2 ⟨.marke mk a, hmem, by
        dsimp only
        rw [dif_pos hmem, dif_pos hs]; simp⟩
    stm_fin hc
  | retires mk s hmem a =>
    have hc : (⟨_, .retires mk s hmem a⟩ : SS D V l Γ Λ) ∈ sRetires l Γ Λ :=
      List.mem_flatMap.2 ⟨.marke mk s, hmem, by
        dsimp only
        rw [dif_pos hmem]
        exact List.mem_map.2 ⟨a, Aufz.annahme_mem a, rfl⟩⟩
    stm_fin hc
  | ret e hΛ =>
    simp only [groesseStmt] at h
    have hc : (⟨_, .ret e hΛ⟩ : SS D V l Γ Λ) ∈ sRet m l Γ Λ :=
      List.mem_flatMap.2 ⟨e, mem_genErg (fun τ e he => hx_aus m e he) _ e (by omega),
        by rw [dif_pos hΛ]; simp⟩
    stm_fin hc
  | retWhy r hΛ =>
    have hc : (⟨_, .retWhy r hΛ⟩ : SS D V l Γ Λ) ∈ sRetWhy l Γ Λ :=
      List.mem_flatMap.2 ⟨r, List.mem_finRange r, by rw [dif_pos hΛ]; simp⟩
    stm_fin hc
  | leave hl =>
    have hc : (⟨_, .leave hl⟩ : SS D V l Γ Λ) ∈ sLeave l Γ Λ := by
      unfold sLeave; rw [dif_pos hl]; simp
    stm_fin hc
  | next hl =>
    have hc : (⟨_, .next hl⟩ : SS D V l Γ Λ) ∈ sNext l Γ Λ := by
      unfold sNext; rw [dif_pos hl]; simp
    stm_fin hc

end Gabbro.Grammatik.Gen
