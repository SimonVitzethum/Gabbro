import Grammatik.Code.Refine.Traverse
import Grammatik.Code.Refine.CallDef
import Grammatik.Code.Refine.Match.Opt

/-
  File:      Grammatik/Code/Refine/Match/Scope.lean
  Subject:   TRACK L, PHASE L1 -- WHAT THE ARMS OF A `match` NEED: the refinement statement of one
             block as a predicate (`BOk`), and the scope of a value bound for an arm (`scope_ok`).

  The forms `onOption`, `onTag` and `onWhy` pick an arm by a test and run it (`onOption` and `onTag` bind
  the payload as a new local first). `lowerS_ok` is a mutual induction, so each form's case is proved
  here as a theorem that takes the refinement of its arms as hypotheses (`BOk`, `EOk`) and the
  mutual theorem only passes `lowerB_ok` on.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl wahr?)

variable {D : Deklaration} {V : Vertrag D}

/-- **`lowerB_ok` for one block**: what a lowered block does, as a predicate on the block. -/
abbrev BOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Gabbro.Grammatik.Block D V l Γ Λ Λ') : Prop :=
  ∀ (lb k : Lbl) (st st' : St) (blks : List Block), lowerB lay cenv lv b lb k st = some (blks, st') →
    ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → KOk M fn k → LvOk M fn lv → FnOk lay M →
      CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        OutOk lay cenv lv M S fn lb k st.r st'.r m rs ks dst (execBlock O passes R b σ ρ)

/-- **`lowerEnd_ok` for one end block.** -/
abbrev EOk (lay : Layout D) (cenv : List Reg) (lv : Lbl × Lbl) (O : Orakel D) (passes : Nat)
    (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Gabbro.Grammatik.Endblock D V l Γ Λ) : Prop :=
  ∀ (lb : Lbl) (st st' : St) (blks : List Block), lowerEnd lay cenv lv e lb st = some (blks, st') →
    ∀ (M : Modl) (S : Sees) (fn : Nat), InM M fn blks → LvOk M fn lv → FnOk lay M → CallRef lay M S R →
      ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs) (ks : List Frame) (dst : Option Reg),
        Rep lay σ m → EnvRep lay rs m cenv ρ → WfL lay m → (∀ x ∈ cenv, x < st.r) →
        EndOk lay cenv lv M S fn lb st.r st'.r m rs ks dst (execEnd O passes R e σ ρ)

/-- A block whose body runs and whose terminator is a fused compare-and-branch, to a block without phis. -/
theorem reach_block_brc {M : Modl} {S : Sees} {fn : Nat} {lb t e : Lbl} {b bk : Block}
    {m m' : Mem} {rs rs' : Regs} {ks : List Frame} {dst : Option Reg} {p : IPred} {w : Nat} {a c : Opd}
    {x y : Val} {x1 : BitVec 1}
    (hb : M.blk fn lb = some b) (hbt : b.term = .brc p w a c t e) (hs : seqI b.body m rs = some (m', rs'))
    (ha : a.ev rs' = some x) (hc : c.ev rs' = some y) (hi : Val.icmp p w x y = some (.int 1 x1))
    (hk : M.blk fn (if x1 = 1 then t else e) = some bk) (hkp : bk.phis = []) :
    Reach M S (.run m ⟨fn, lb, 0, rs, dst⟩ ks)
      (.run m' ⟨fn, (if x1 = 1 then t else e), 0, rs', dst⟩ ks) := by
  have h1 := reach_seq M S b.body m ⟨fn, lb, 0, rs, dst⟩ ks m' rs'
    ⟨b, hb, fun i h => by simp⟩ hs
  have h2 := reach_brc (S := S) (m := m') (ks := ks)
    (f := ⟨fn, lb, 0 + b.body.length, rs', dst⟩) (blk := b) (blk' := bk)
    ⟨hb, (show b.body.length ≤ 0 + b.body.length by omega), hbt⟩ ha hc hi hk hkp
  exact Reach.trans h1 h2

/-- **The scope of a bound value.** A block `lb1` holds the code `cv` (the value moved to the width of
    its type, `Fv`) and `cb` (a new cell for it, `bindCode`) and jumps to the body `bd`; if the body
    does what the source body does in the environment extended by the value (`IH`), then the whole
    does what the source does with the local gone out of scope (`Ausgang.schrumpf`). -/
theorem scope_ok {lay : Layout D} {cenv : List Reg} {lv : Lbl × Lbl} {M : Modl} {S : Sees} {fn : Nat}
    {k : Lbl} {ks : List Frame} {dst : Option Reg} {l : Bool} {Γ : Ctx} {τ : GTy}
    {σ : World D} (ρ : Env D Γ) (v : Wert D τ) {lb1 bd : Lbl} {cv cb : List Instr} {ov : Opd}
    {r0 r1 r2 a ri r' : Nat} (m : Mem) (rs : Regs)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < r0)
    (hMb : M.blk fn lb1 = some ⟨lb1, [], cv ++ cb, .jmp bd⟩) (hKb : KOk M fn bd)
    (Fv : Frag m rs r0 (cv, ov, r1) (encR lay τ v))
    (hb : bindCode τ ov r1 = some (cb, a, r2)) (hri : r2 ≤ ri) (o : Ausgang V l (τ :: Γ))
    (IH : ∀ (m1 : Mem) (rs4 : Regs), Rep lay σ m1 → EnvRep lay rs4 m1 (a :: cenv) (Env.cons v ρ) →
      WfL lay m1 → (∀ x ∈ a :: cenv, x < ri) →
      OutOk lay (a :: cenv) lv M S fn bd k ri r' m1 rs4 ks dst o) :
    OutOk lay cenv lv M S fn lb1 k r0 r' m rs ks dst o.schrumpf := by
  obtain ⟨rs3, hs3, hr3, hag3, hlt3, hev3⟩ := Fv
  have hs3' : seqI cv m rs = some (m, rs3) := hs3
  have hE3 := envRep_regs cenv ρ (fun x hx => hag3 x (hc x hx)) hE
  have hc3 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr3
  obtain ⟨m1, rs4, hs4, hRn, hEnew, hWn, hra, hr4e, hag4, hFb, hcell⟩ :=
    bindCode_run lay (τ := τ) v ov r1 m rs3 hR hE3 hW hev3 hlt3 hc3 hb
  subst hr4e
  have hseq : seqI (cv ++ cb) m rs = some (m1, rs4) := by
    rw [seqI_append, hs3', Option.bind_some]; exact hs4
  obtain ⟨bkr, hbkr, hkpr⟩ := hKb
  have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hMb rfl hbkr hkpr hseq
  have hbound : ∀ x ∈ a :: cenv, x < ri := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hri
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc3 x hx') hra)) hri
  have hF : Fr lay cenv r0 m rs m1 rs4 := fr_trans (fr_regs hag3) hFb hr3 hc
  exact outok_bind hreach hF hcell hc
    (Nat.le_trans hr3 (Nat.le_trans hra (Nat.le_trans (Nat.le_succ a) hri))) o
    (IH m1 rs4 hRn hEnew hWn hbound)

/-- **The scope of a bound value for an end block** (`scope_ok` for the `else` arm of a call that may fail). -/
theorem scope_end_ok {lay : Layout D} {cenv : List Reg} {lv : Lbl × Lbl} {M : Modl} {S : Sees} {fn : Nat}
    {ks : List Frame} {dst : Option Reg} {l : Bool} {Γ : Ctx} {τ : GTy}
    {σ : World D} (ρ : Env D Γ) (v : Wert D τ) {lb1 bd : Lbl} {cv cb : List Instr} {ov : Opd}
    {r0 r1 r2 a ri r' : Nat} (m : Mem) (rs : Regs)
    (hR : Rep lay σ m) (hE : EnvRep lay rs m cenv ρ) (hW : WfL lay m) (hc : ∀ x ∈ cenv, x < r0)
    (hMb : M.blk fn lb1 = some ⟨lb1, [], cv ++ cb, .jmp bd⟩) (hKb : KOk M fn bd)
    (Fv : Frag m rs r0 (cv, ov, r1) (encR lay τ v))
    (hb : bindCode τ ov r1 = some (cb, a, r2)) (hri : r2 ≤ ri) (o : EndAusgang V l (τ :: Γ))
    (IH : ∀ (m1 : Mem) (rs4 : Regs), Rep lay σ m1 → EnvRep lay rs4 m1 (a :: cenv) (Env.cons v ρ) →
      WfL lay m1 → (∀ x ∈ a :: cenv, x < ri) →
      EndOk lay (a :: cenv) lv M S fn bd ri r' m1 rs4 ks dst o) :
    EndOk lay cenv lv M S fn lb1 r0 r' m rs ks dst o.schrumpf := by
  obtain ⟨rs3, hs3, hr3, hag3, hlt3, hev3⟩ := Fv
  have hs3' : seqI cv m rs = some (m, rs3) := hs3
  have hE3 := envRep_regs cenv ρ (fun x hx => hag3 x (hc x hx)) hE
  have hc3 : ∀ x ∈ cenv, x < r1 := fun x hx => Nat.lt_of_lt_of_le (hc x hx) hr3
  obtain ⟨m1, rs4, hs4, hRn, hEnew, hWn, hra, hr4e, hag4, hFb, hcell⟩ :=
    bindCode_run lay (τ := τ) v ov r1 m rs3 hR hE3 hW hev3 hlt3 hc3 hb
  subst hr4e
  have hseq : seqI (cv ++ cb) m rs = some (m1, rs4) := by
    rw [seqI_append, hs3', Option.bind_some]; exact hs4
  obtain ⟨bkr, hbkr, hkpr⟩ := hKb
  have hreach := reach_block_jmp (S := S) (ks := ks) (dst := dst) hMb rfl hbkr hkpr hseq
  have hbound : ∀ x ∈ a :: cenv, x < ri := fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hri
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (hc3 x hx') hra)) hri
  have hF : Fr lay cenv r0 m rs m1 rs4 := fr_trans (fr_regs hag3) hFb hr3 hc
  exact endok_bind hreach hF hcell hc
    (Nat.le_trans hr3 (Nat.le_trans hra (Nat.le_trans (Nat.le_succ a) hri))) o
    (IH m1 rs4 hRn hEnew hWn hbound)

end Gabbro.Code.Lower
