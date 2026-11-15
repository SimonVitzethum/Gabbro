module
public import Bruecke.Anweisung.Lokal.Speichern
public import Bruecke.Kodierung.GlobSchreiben
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-- A successfully lowered numeric store carries a declared static write right. -/
theorem lowAssignGlob_writes {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {n : String} {v : USide}
    {gst : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ}
    (h : lowAssignGlobL (l := loopMode) u c Γ fn Λ n v = .ok gst)
    (hScalar : ScalarStatics u) : n ∈ (fnAt u c).gputs := by
  unfold lowAssignGlobL at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    next lo hi' ht =>
      split at h
      · cases h
      · split at h
        · rename_i hw
          have hname : (globAt u i).name = n := globIdx_name u.globs n i hi
          unfold writesGAt at hw
          rw [hname] at hw
          exact (by obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hw; exact (eq_of_beq hyx) ▸ hy)
        · cases h
    next heq => cases h
    next a heq =>
      exfalso
      rcases (hScalar i).1 with ⟨_, _, ht⟩ | ht <;> rw [ht] at heq <;> cases heq

/-- A numeric static write reads through the positional scope, updates the Body world,
    and re-establishes the combined relation. The canonical lowering checks write rights
    and guards; neither is reconstructed from the source spelling. -/
theorem lowAssignGlob_sim {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {ns : BodyNames}
    {Λ : List (Res (declOf u))} {n : String} {v : USide}
    {gst : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignGlobL (l := loopMode) u c Γ fn Λ n v = .ok gst)
    (hb : namedStmt u fn ns (.assignGlob n v) = some bst)
    (hScalar : ScalarStatics u) (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ₁ val, execStmt O passes R gst σ ρ = .ok σ₁ ρ ∧
      (∀ ρB, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.global n) val, s.local'⟩) ∧
      WGRel u σ₁ (Gabbro.Body.store s.world (.global n) val) ∧ n ∈ (fnAt u c).gputs := by
  unfold lowAssignGlobL at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    next lo hi' ht =>
      split at h
      · cases h
      · rename_i ev hev
        split at h
        · rename_i hw
          split at h
          · rename_i hd
            cases h
            have hty : (declOf u).gtyp i = .int lo hi' := by
              change (globAt u i).ty.toTy = _
              rw [ht] <;> rfl
            let e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp i) := by rw [hty]; exact ev
            have he2 : HEq e2 ev := mpr_heq _ _
            let σl := σ.lese Λ e2.orte
            obtain ⟨raw, hr, hn⟩ := namedStmt_some hb
            simp only [stmtBody] at hr
            cases hv : sideExprG u fn v with
            | none => rw [hv] at hr; cases hr
            | some ve =>
              rw [hv] at hr
              cases hr
              simp only [renameStep] at hn
              cases he : renameScalar (ns.lookup fn) ve with
              | none => rw [he] at hn; cases hn
              | some ve' =>
                rw [he] at hn
                simp only [Option.map_some, Option.some.injEq] at hn
                subst bst
                have hs : namedSide u fn ns v = some ve' := by
                  simp only [namedSide, hv, Option.bind_some, he]
                have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                have hv' := lowWertAt_named_sim hev hs hU.art hT σl σl ρ s hWl hL
                have hv2 := valOf_eval_heq hty e2 ev he2 σl σl ρ
                refine ⟨σl.schreibGlob i Λ (eval σl e2 σl ρ),
                  valOf ((declOf u).gtyp i) (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                · intro ρB
                  simp only [Gabbro.Body.step, hv', ← hv2]
                · exact wgrel_same u rfl rfl (wgrel_storeGlob u hWl n i hi (eval σl e2 σl ρ))
                · have hname : (globAt u i).name = n := globIdx_name u.globs n i hi
                  unfold writesGAt at hw
                  rw [hname] at hw
                  exact (by obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hw; exact (eq_of_beq hyx) ▸ hy)
          · cases h
        · cases h
    next heq => cases h
    next a heq =>
      exfalso
      rcases (hScalar i).1 with ⟨_, _, ht⟩ | ht <;> rw [ht] at heq <;> cases heq

/-- A successfully lowered `bool` static store carries a declared static write right. -/
theorem lowAssignGlobB_writes {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {n : String} {v : UEns}
    {gst : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ}
    (h : lowAssignGlobBL (l := loopMode) u c Γ fn Λ n v = .ok gst) : n ∈ (fnAt u c).gputs := by
  unfold lowAssignGlobBL at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    next ht =>
      split at h
      · cases h
      · split at h
        · rename_i hw
          have hname : (globAt u i).name = n := globIdx_name u.globs n i hi
          unfold writesGAt at hw
          rw [hname] at hw
          exact (by obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hw; exact (eq_of_beq hyx) ▸ hy)
        · cases h
    next lo hi' heq => cases h
    next a heq => cases h

/-- A `bool` static write: the condition is read through the positional scope like a bool
    local, then stored exactly as a numeric static. No statics premise is needed, since the
    lowering refuses every other static type itself. -/
theorem lowAssignGlobB_sim {loopMode : Bool} (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn}
    {ns : BodyNames} {Λ : List (Res (declOf u))} {n : String} {v : UEns}
    {gst : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ} {bst : Gabbro.Body.Stmt}
    (h : lowAssignGlobBL (l := loopMode) u c Γ fn Λ n v = .ok gst)
    (hb : namedStmt u fn ns (.assignGlobB n v) = some bst)
    (hU : UmfangB Γ fn ns) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WGRel u σ s.world) (hL : PositionalLRel fn ns.active 0 ρ s.local') :
    ∃ σ₁ val, execStmt O passes R gst σ ρ = .ok σ₁ ρ ∧
      (∀ ρB, Gabbro.Body.step ρB bst s =
        .running ⟨Gabbro.Body.store s.world (.global n) val, s.local'⟩) ∧
      WGRel u σ₁ (Gabbro.Body.store s.world (.global n) val) ∧ n ∈ (fnAt u c).gputs := by
  unfold lowAssignGlobBL at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    next ht =>
      split at h
      · cases h
      · rename_i ev hev
        split at h
        · rename_i hw
          split at h
          · rename_i hd
            cases h
            have hty : (declOf u).gtyp i = .bool := by
              change (globAt u i).ty.toTy = _
              rw [ht] <;> rfl
            let e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp i) := by rw [hty]; exact ev
            have he2 : HEq e2 ev := mpr_heq _ _
            let σl := σ.lese Λ e2.orte
            obtain ⟨raw, hr, hn⟩ := namedStmt_some hb
            simp only [stmtBody] at hr
            cases hv : rawCond u fn v with
            | none => rw [hv] at hr; cases hr
            | some ve =>
              rw [hv] at hr
              cases hr
              simp only [renameStep] at hn
              cases he : renameScalar (ns.lookup fn) ve with
              | none => rw [he] at hn; cases hn
              | some ve' =>
                rw [he] at hn
                simp only [Option.map_some, Option.some.injEq] at hn
                subst bst
                have hs : condZ u fn ns v = some ve' := by
                  simp only [condZ, hv, Option.bind_some, he]
                have hWl : WGRel u σl s.world := wgrel_same u rfl rfl hW
                have hv' := lowEns_named_sim hev hs hU.art hT σl σl ρ s hWl hWl hL
                have hv2 := valOf_eval_heq hty e2 ev he2 σl σl ρ
                refine ⟨σl.schreibGlob i Λ (eval σl e2 σl ρ),
                  valOf ((declOf u).gtyp i) (eval σl e2 σl ρ), rfl, ?_, ?_, ?_⟩
                · intro ρB
                  simp only [Gabbro.Body.step, hv', ← hv2]
                · exact wgrel_same u rfl rfl (wgrel_storeGlob u hWl n i hi (eval σl e2 σl ρ))
                · have hname : (globAt u i).name = n := globIdx_name u.globs n i hi
                  unfold writesGAt at hw
                  rw [hname] at hw
                  exact (by obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hw; exact (eq_of_beq hyx) ▸ hy)
          · cases h
        · cases h
    next lo hi' heq => cases h
    next a heq => cases h

end Gabbro.Bruecke
