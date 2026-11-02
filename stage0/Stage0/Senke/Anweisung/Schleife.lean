/-
  File:      stage0/Stage0/Senke/Anweisung/Schleife.lean
  Subject:   `traverse` (`travC`): the IR loop runs G's `traverseLauf` over the indices `0 ..< count` (`trav_ok`).

  The counter lives in the index's own slot `s = frei Γ reserved`; the body may not write it (`s` is protected in the body,
  `Keeps`). The head checks the invariant (false: the stop 104, G's `logik schleife`) and `k < count` (false: the
  end, G's `ok`); the body's `ok` and `next` go on at the next part (`k := k + 1`, back to the head), its `leave`
  at the leave part (the invariant once more, then the end or the stop). The proof runs by induction over the
  indices left (`List.range'`).
-/
module
public import Stage0.Senke.Anweisung.Schleifea
public import Stage0.Senke.Anweisung.SchleifeTeile
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D} {reserved : Nat}

/-! ## The loop -/

section
variable {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp : Runner.W}
  {fp : Runner.W} {lo K Ks : Nat} {pr : List Nat} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W}
  {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {inv : Expr D Γ Λ .bool}
  {body : Block D (vertragVon D f) true (.index (D.count t) :: Γ) Λ Λ} {ci' cb : List II × Nat} {pc eL eN : Runner.W}

/-- **`traverse`**: the code of `travC` runs G's `traverseLauf` over all indices. -/
theorem trav_ok (hn : inW (D.count t) (D.count t) = true) (hci : lowE (reserved := reserved) L inv (frei Γ reserved + 1) = some ci')
    (hlenc : 16 * (9 + travCountSize (D.count t) + ci'.1.length + cb.1.length) < 2 ^ 31) (hlo0 : lo = (functionFrame P f).internalResult)
    (htop : max ci'.2 (max cb.2 (frei Γ reserved + 9)) ≤ Ks) (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    (hbody : ∀ m' pc' σ' ρ', PreS L m' pc' fp K (frei (.index (D.count t) :: Γ) reserved) cb.1 ρ' reserved → Umf L A C dv m' fp Ks K →
      Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K (frei Γ reserved :: pr) ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cb.1.length))
        (pc' + BitVec.ofNat 64 (16 * cb.1.length) + BitVec.ofInt 64 48)
        (pc' + BitVec.ofNat 64 (16 * cb.1.length) + BitVec.ofInt 64 0) (execBlock O passes R body σ' ρ') reserved)
    {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ reserved) (travCode (frei Γ reserved) (D.count t) ci'.1 cb.1) ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (travCode (frei Γ reserved) (D.count t) ci'.1 cb.1).length)) eL eN
      (traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) (alleIndizes (D.count t)) σ ρ) reserved := by
  have hindex : valueWords (.index (D.count t)) = 1 :=
    integerWords_word (by omega) (by have h := hn; simp only [inW, Bool.and_eq_true, decide_eq_true_eq] at h; omega)
  have hctxWidth : frei (.index (D.count t) :: Γ) reserved = frei Γ reserved + 1 := by
    simp [frei, hindex, Nat.add_assoc]

  have hks := hW.ks
  have hroom := hp.frame.room
  have hFB3 : FB = 4 := rfl
  have hFramePrefix := functionFrame_prefix P f
  have s0 := const_step (j := frei Γ reserved) (k := 0) (codeAt_left (a := [ci 1 (frei Γ reserved) 0 0]) (by simpa [travCode] using hp.code))
    hp.frame (by omega) hp.small (by decide)
  let m0 := write m (slot fp (BitVec.ofNat 64 (frei Γ reserved))) 8 (BitVec.ofInt 64 (0 : Int)).toNat
  have a0s : Agree fp (frei Γ reserved) Ks m m0 := agree_write (frameOK_sub hp.frame hks).room (Nat.le_refl _) (by omega) _
  have a0 := Agree.widen a0s hks
  have hk0 : m0.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 0) := by
    rw [show BitVec.ofNat 64 0 = BitVec.ofInt 64 (0 : Int) by decide]; exact rd_same hp.frame (by omega) _
  have hp0 : PreS L m0 pc fp K (frei Γ reserved) (travCode (frei Γ reserved) (D.count t) ci'.1 cb.1) ρ reserved :=
    mkPreS (Nat.le_refl _) hp.small (hp.frame.agree a0) (hp.code.agree a0 hp.far) hp.far
      (envAt_agree hp.env a0 hp.frame (Nat.le_refl _) (by omega))
  have hl := trav_loop (l := l) (eL := eL) (eN := eN) hn hci hlenc hlo0 htop hW hlo hlo2 hpr hbody
    (D.count t).toNat 0 m0 σ ρ (by omega) hp0 hk0 (hu.agree a0 hp.frame (by omega)) (hk.agree a0 hp.frame (by omega))
    (weltAt_stab hW.lay (by have := hW.lo; omega) m m0 hWa (a0s.mono (Nat.zero_le _)))
  rw [alleIndizes_ab]
  exact Sim.prefix hlo s0 (agreeW_of (a0.mono hlo2))
    (keeps_write hroom (by omega) (fun j hj => by have := hpr j hj; omega) (fun h => by have := hpr _ h; omega) _) hl

end

end Gabbro.Stage0.Senke
