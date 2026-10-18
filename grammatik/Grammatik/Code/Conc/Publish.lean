import Grammatik.Code.Conc.Lower
import Grammatik.Code.Refine.StmtOk

/-
  File:      Grammatik/Code/Conc/Publish.lean
  Subject:   TRACK L, PHASE L3 (START) -- THE REFINEMENT OF `publish`.

  In machine G `publish g = e` is a write to the global `g` (`Stmt.publish`: `schreibGlob`); its payload
  visibility is the weak memory's business, not a step of G. The lowering is a RELEASE store into the cell of
  `g` (`astor .. rel`). A store does not consult the memory-model interface, so this refinement holds for EVERY
  interface `S`: `publish_ok` is the statement `lowerS_ok` makes for an assignment to a global, with `astor`
  in place of `store`. What the release order MEANS (that every write before it is visible to an acquire load
  that reads it) is the weak-memory model's, linked in `Code/Model/Weak.lean`; it is not re-proved here.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl gdarf)

variable {D : Deklaration} {V : Vertrag D}

theorem wb_ge : 4 ≤ (Conf.wb : Nat) := by
  unfold Conf.wb
  rcases Conf.wide with hc | hc <;> rw [hc] <;> decide

/-- A word-sized memory image is no `bool`. -/
theorem atomicG_nonbool {τ : GTy} (h : atomicG τ = true) : τ ≠ .bool := by
  intro e
  subst e
  have hw := wb_ge
  simp only [atomicG, Bool.and_eq_true] at h
  have h2 : (memTy Gabbro.Grammatik.Ty.bool).store = Conf.wb := of_decide_eq_true h.2
  have h3 : (memTy Gabbro.Grammatik.Ty.bool).store = 1 := rfl
  omega

theorem encM_eq_encR (lay : Layout D) {τ : GTy} (hn : τ ≠ .bool) (v : Wert D τ) :
    encM lay τ v = encR lay τ v := by
  cases τ <;> first | rfl | exact absurd rfl hn

theorem atomicG_supp {τ : GTy} (h : atomicG τ = true) : supp τ = true := by
  simp only [atomicG, Bool.and_eq_true] at h
  exact h.1

theorem atomicG_ok {τ : GTy} (h : atomicG τ = true) : atomicOk (memTy τ) = true := by
  simp only [atomicG, Bool.and_eq_true] at h
  exact h.2

/-- **`publish` refines G's write.** For every interface `S`. -/
theorem publish_ok (lay : Layout D) (hL : LayoutOk lay) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D)
    (passes : Nat) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (g : D.Glob) (e : Gabbro.Grammatik.Expr D Γ Λ (D.gtyp g))
    (payload : List D.Glob) (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hgd : gdarf D g Λ)
    (lb k : Lbl) (st st' : St) (blks : List Block)
    (h : lowerPublish lay cenv g e lb k st = some (blks, st'))
    (M : Modl) (S : Sees) (fn : Nat) (hM : InM M fn blks) (hk : KOk M fn k)
    (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < st.r) :
    OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst
      (execStmt O passes R (Gabbro.Grammatik.Stmt.publish (V := V) (l := l) g e payload hp hw hgd) σ ρ) := by
  unfold lowerPublish at h
  have hat : atomicG (D.gtyp g) = true := by
    apply Classical.byContradiction
    intro hn
    rw [if_neg hn] at h
    simp at h
  rw [if_pos hat] at h
  have hs := atomicG_supp hat
  rcases he : lowerE lay cenv e st.r with _ | ⟨ce, oe, r1⟩
  · simp [he] at h
  simp only [he] at h
  have h' := Option.some.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  have hb := hM _ (List.mem_singleton_self _)
  obtain ⟨bk, hbk, hkp⟩ := hk
  simp only [execStmt, OutOk]
  obtain ⟨σl, hσl⟩ : ∃ σl, σl = σ.lese Λ e.orte := ⟨_, rfl⟩
  try rw [← hσl]
  have hRl : Rep lay σl m := by rw [hσl]; exact hR
  obtain ⟨Fe, _⟩ := lowerE_ok lay hL e cenv st.r (ce, oe, r1) he σl σl ρ m rs hRl hE hc
  obtain ⟨rs1, hs1, hr1, hag1, hlt1, hev1⟩ := Fe
  have hs1' : seqI ce m rs = some (m, rs1) := hs1
  have hnb := atomicG_nonbool hat
  obtain ⟨x, hx⟩ : ∃ x, m.load (lay.ggblk g) 0 (memTy (D.gtyp g)) = some x := (hR.2 g hs).1
  have hty : (encM lay (D.gtyp g) (eval σl e σl ρ)).ty = memTy (D.gtyp g) := encM_ty lay _ hs
  obtain ⟨m', hm'⟩ := store_of_load hx hty
  have hev1' : oe.ev rs1 = some (encM lay (D.gtyp g) (eval σl e σl ρ)) := by
    rw [encM_eq_encR lay hnb]; exact hev1
  have hst : stepI (.astor (memTy (D.gtyp g)) oe (.glob (lay.ggblk g)) .rel) m rs1 = some (m', rs1) := by
    have hgl : (Opd.glob (lay.ggblk g)).ev rs1 = some (.ptr (lay.ggblk g) 0) := rfl
    simp only [stepI, hev1', hgl, atomicG_ok hat, if_true, hm', Option.map_some]
  have hseq : seqI (ce ++ [.astor (memTy (D.gtyp g)) oe (.glob (lay.ggblk g)) .rel]) m rs = some (m', rs1) := by
    rw [seqI_append, hs1']
    simp [seqI, hst]
  have hFr : Fr lay cenv st.r m rs m' rs1 := fr_store hm' (Or.inl (not_fresh_glob g)) hag1
  refine ⟨m', rs1, reach_block_jmp hb rfl hbk hkp hseq, ?_, hFr⟩
  have hRn : Rep lay (σl.schreibGlob g Λ (eval σl e σl ρ)) m' :=
    rep_store_glob hL hRl g _ hs hm'
  refine post_store hRn hE hW hm' (not_fresh_glob g) (fun r hr => hag1 r (hc r hr)) (fun x hx => ?_)
  exact Nat.lt_of_lt_of_le (hc x hx) hr1

end Gabbro.Code.Lower
