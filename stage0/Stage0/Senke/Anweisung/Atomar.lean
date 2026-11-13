/-
  File:      stage0/Stage0/Senke/Anweisung/Atomar.lean
  Subject:   The code of `exchange` (`exC`) against G: the global's word into the new variable's slot, the new value
             computed, `cas` of the global from the old word to the new one; one thread alone finds the old word
             still there, so the `cas` takes and the loop does not go round (`ex_tail`). The global then holds G's
             new value, the variable G's old one (`exch_ok`).
-/
module
public import Stage0.Senke.Anweisung.Atomara
public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Anweisung.Puffer.Basis
public import Stage0.Senke.Sperre.Nimm
public import Stage0.Senke.Anweisung
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}
variable {H : List D.Lock}

section
variable {O : Orakel D} {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {L : Lay D} {P : Programm D} {f : D.Fn} {fp : Runner.W}
  {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {pr : List Nat} {ex : Int × Int}
  {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- **`exchange`**: what G answers for the block, the code does. -/
theorem exch_head {reserved : Nat} {g : D.Glob} (hfit : aggregateFits (D.gtyp g) = true) {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)} {cn cr : List II} {tn : Nat}
    (hn : lowE L neu (frei Γ reserved + 1) reserved = some (cn, tn)) (htn : tn ≤ Ks) (hs4 : frei Γ reserved + 4 ≤ Ks)
    (hW : WIn L fp Ks K) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ reserved) (exC (frei Γ reserved) (L.ga g) cn ++ cr) ρ reserved) (hWa : WeltAt m L σ) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length), fp⟩ m' ∧
      AgreeW L fp (frei Γ reserved) K m m' ∧
      PreS L m' (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length)) fp K (frei (D.gtyp g :: Γ) reserved) cr
        (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ) reserved ∧
      WeltAt m' L ((σ.lese Λ (.inr g :: neu.orte)).schreibGlob g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
        (σ.lese Λ (.inr g :: neu.orte)) (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))) := by
  have hw1 := aggregateFits_width hfit
  generalize hsd : frei Γ reserved = s at hn hs4 hp ⊢
  have hfr : frei (D.gtyp g :: Γ) reserved = s + 1 := by simp only [frei, contextWords_cons, hw1] at hsd ⊢; omega
  rw [hfr]
  have hks := hW.ks
  have hK := hp.small
  have hl := hW.lay
  have hgin : L.lo ≤ L.ga g ∧ L.ga g + 8 ≤ L.hi := by
    have h := hl.2.1 g; rw [hw1] at h; omega
  have hhi := hl.2.2
  have hroom := hp.frame.room
  have hga : fp.toNat + 8 * K ≤ L.ga g := by have := hW.ord; have := hW.top; omega
  have hlen := exC_len s (L.ga g) cn
  have heq : exC s (L.ga g) cn ++ cr = [ci 1 s (L.ga g) 0, ci 15 s s 0] ++ (cn ++ ([ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s, ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s,
      ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0] ++ cr)) := by
    simp only [exC, List.append_assoc]
  have hp' := hp
  rw [heq] at hp'
  -- the old word
  obtain ⟨w0, hg0, he0⟩ := ValueAt.cellWord (aggregateFits_compat hfit) (hWa.2.1 g)
  obtain ⟨m1, s1, a1, r1⟩ := glob_word hp'.left.code hp'.left.far hp.frame (by omega) hK hg0 hga (by omega)
  have hq := hp'.next a1 (Nat.le_refl _) (by omega)
  -- the new value
  have hσ : WeltAt m L (σ.lese Λ (.inr g :: neu.orte)) := hWa
  have hp1 : PreS L m1 (pc + BitVec.ofNat 64 (16 * 2)) fp K (s + 1) (cn ++ ([ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s, ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s,
      ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0] ++ cr))
      (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ) reserved :=
    ⟨Nat.le_of_eq hfr, hK, hq.frame, hq.code, hq.far, envAt_cons hq.env (ValueAt.of_enc hw1 (by rw [hsd]; exact r1) he0), trivial,
     wstab_true _ _⟩
  have hpw := PreS.welt hp1.left hks (weltAt_stab hl (by have := hW.top; omega) m m1 hσ (a1.mono (Nat.zero_le _)))
    hl (by have := hW.lo; omega)
  obtain ⟨m2, s2, a2s, wn, rn, hen⟩ := (lowE_ok (same := by intro _; rfl) (σ.lese Λ (.inr g :: neu.orte)) (σ.lese Λ (.inr g :: neu.orte))
    (fun _ h => h) hW.lay neu (s + 1) cn tn hn htn m1 _ _ hpw).word (aggregateFits_compat hfit)
  have a2 := Agree.widen a2s hks
  have hq2 := hq.next (a2.mono (Nat.le_succ s)) (Nat.le_refl _) (by omega)
  have r2 : m2.rd64 (slot fp (BitVec.ofNat 64 s)) = some w0 := by
    rw [agree_rd_low a2 hroom (by omega) (by omega)]; exact r1
  have g2 : m2.rd64 (BitVec.ofNat 64 (L.ga g)) = some w0 := by
    rw [agree_rd_far a2 hga (by omega), agree_rd_far a1 hga (by omega)]; exact hg0
  have hW2 := hpw.wstab m1 m2 hpw.welt (a2s.mono (Nat.zero_le _))
  -- the tail
  obtain ⟨m3, s3, a3, hW3, r3⟩ := ex_tail (σ := σ.lese Λ (.inr g :: neu.orte)) hw1 hq2.left.code hq2.left.far
    hq2.frame (by omega) hK r2 rn g2 hW2 hl hW.dis (by have := hW.top; omega) hen
  have hq3 := Pre.nextW hW hq2 a3 (by omega) (Nat.le_refl _) (by omega)
  have A : AgreeW L fp s K m m3 :=
    (agreeW_of (a1.trans (a2.mono (by omega)))).trans (a3.mono (by omega))
  have e3 : pc + BitVec.ofNat 64 (16 * [ci 1 s (L.ga g) 0, ci 15 s s 0].length) + BitVec.ofNat 64 (16 * cn.length) +
      BitVec.ofNat 64 (16 * [ci 1 ((s + 2 : Nat) : Int) (L.ga g) 0,
      ci 22 ((s + 3 : Nat) : Int) ((s + 2 : Nat) : Int) s, ci 14 ((s + 3 : Nat) : Int) ((s + 3 : Nat) : Int) s,
      ci 19 ((s + 3 : Nat) : Int) (-(16 * ((cn.length + 5 : Nat) : Int))) 0].length) =
      pc + BitVec.ofNat 64 (16 * (exC s (L.ga g) cn).length) := by
    simp only [List.length_cons, List.length_nil]
    rw [pc_jump, pc_jump, hlen]; congr 2; omega
  have hp3 : PreS L m3 (pc + BitVec.ofNat 64 (16 * (exC s (L.ga g) cn).length)) fp K (s + 1) cr
      (Env.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ) reserved := by
    rw [← e3]
    exact ⟨Nat.le_of_eq hfr, hq3.small, hq3.frame, hq3.code, hq3.far, envAt_cons hq3.env (ValueAt.of_enc hw1 (by rw [hsd]; exact r3) he0),
      trivial, wstab_true _ _⟩
  exact ⟨m3, s1.trans (s2.trans (star_cast s3 rfl (by rw [← e3]; rfl))), A, hp3, hW3⟩

theorem exch_ok {reserved : Nat} {g : D.Glob} (hfit : aggregateFits (D.gtyp g) = true) {neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)}
    {hw : (vertragVon D f).gschreibt g = true} {hL : gdarf D g Λ}
    {rest : Block D (vertragVon D f) l (D.gtyp g :: Γ) Λ Λ'} {cn cr : List II} {tn : Nat}
    (hn : lowE (reserved := reserved) L neu (frei Γ reserved + 1) = some (cn, tn)) (htn : tn ≤ Ks) (hs4 : frei Γ reserved + 4 ≤ Ks)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = (functionFrame P f).internalResult) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hrest : ∀ m' σ' (ρ' : Env D (D.gtyp g :: Γ)),
      PreS L m' (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length)) fp K (frei (D.gtyp g :: Γ) reserved) cr ρ' reserved →
      Umf L A C dv m' fp Ks K H → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length), fp⟩ m'
        (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length) + BitVec.ofNat 64 (16 * cr.length))
        (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length) + BitVec.ofNat 64 (16 * cr.length) +
          BitVec.ofInt 64 ex.1)
        (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn).length) + BitVec.ofNat 64 (16 * cr.length) +
          BitVec.ofInt 64 ex.2)
        (execBlock O passes R rest σ' ρ') reserved)
    (hp : PreS L m pc fp K (frei Γ reserved) (exC (frei Γ reserved) (L.ga g) cn ++ cr) ρ reserved) (hu : Umf L A C dv m fp Ks K H)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn ++ cr).length))
      (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn ++ cr).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (exC (frei Γ reserved) (L.ga g) cn ++ cr).length) + BitVec.ofInt 64 ex.2)
      (execBlock O passes R (.exchange g neu hw hL rest) σ ρ) reserved := by
  obtain ⟨m3, s3, A, hp3, hW3⟩ := exch_head (Λ := Λ) hfit hn htn hs4 hW hp hWa
  have ih := hrest m3 _ _ hp3 (hu.agreeW hW (A.mono hlo2) hlo) (hk.agreeW hW (A.mono hlo2) (by omega)) hW3
  simp only [execBlock]
  rw [pc_add1]
  exact Sim.prefix hlo s3 (A.mono hlo2) (keeps_of_agreeW hW A hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)

/-- The load of `awaits`: the global's word into the new variable's slot. -/
theorem awaits_head {reserved : Nat} {g : D.Glob} {cr : List II} (hfit : aggregateFits (D.gtyp g) = true)
    (hl : lit32 (L.ga g) = true) (hs1 : frei Γ reserved + 1 ≤ Ks)
    (hW : WIn L fp Ks K) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ reserved) ([ci 1 (frei Γ reserved) (L.ga g) 0, ci 15 (frei Γ reserved) (frei Γ reserved) 0] ++ cr) ρ reserved)
    (hWa : WeltAt m L σ) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m' ∧ AgreeW L fp (frei Γ reserved) K m m' ∧
      PreS L m' (pc + BitVec.ofNat 64 (16 * 2)) fp K (frei (D.gtyp g :: Γ) reserved) cr (Env.cons (σ.globs g) ρ) reserved ∧ WeltAt m' L σ := by
  have hks := hW.ks
  have hpw := PreS.welt hp.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, hen⟩ := glob_ok (σ := σ) hl (aggregateFits_compat hfit) hpw (fun _ h => h) (by omega)
  have a1 := Agree.widen a1s hks
  have hq := hp.next a1 (Nat.le_refl _) (by have := hp.small; omega)
  exact ⟨m1, s1, agreeW_of a1, ⟨by simp only [frei, contextWords_cons, aggregateFits_width hfit]; omega, hq.small, hq.frame, hq.code, hq.far,
    envAt_cons hq.env (ValueAt.of_enc (aggregateFits_width hfit) hw hen), trivial, wstab_true _ _⟩, hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))⟩

/-- **`awaits`**: the publication is visible (`SichtOK`); the global's word is the new variable. -/
theorem awaits_ok {reserved : Nat} [SichtOK O] {g : D.Glob} (hfit : aggregateFits (D.gtyp g) = true) {pl : List D.Glob} {hpl : pl = D.nutzlast g} {hL : gdarf D g Λ}
    {hat : D.atomar g = true} {rest : Block D (vertragVon D f) l (D.gtyp g :: Γ) Λ Λ'} {cr : List II}
    (hl : lit32 (L.ga g) = true) (hs1 : frei Γ reserved + 1 ≤ Ks)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo0 : lo = (functionFrame P f).internalResult) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved) {m : Runner.Mem} {pc : Runner.W} {σ : World D} {ρ : Env D Γ}
    (hrest : ∀ m' σ' (ρ' : Env D (D.gtyp g :: Γ)),
      PreS L m' (pc + BitVec.ofNat 64 (16 * 2)) fp K (frei (D.gtyp g :: Γ) reserved) cr ρ' reserved →
      Umf L A C dv m' fp Ks K H → Kopf L f m' fp K rp cfp ρ0 P σ0 → WeltAt m' L σ' →
      Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc + BitVec.ofNat 64 (16 * 2), fp⟩ m'
        (pc + BitVec.ofNat 64 (16 * 2) + BitVec.ofNat 64 (16 * cr.length))
        (pc + BitVec.ofNat 64 (16 * 2) + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.1)
        (pc + BitVec.ofNat 64 (16 * 2) + BitVec.ofNat 64 (16 * cr.length) + BitVec.ofInt 64 ex.2)
        (execBlock O passes R rest σ' ρ') reserved)
    (hp : PreS L m pc fp K (frei Γ reserved) ([ci 1 (frei Γ reserved) (L.ga g) 0, ci 15 (frei Γ reserved) (frei Γ reserved) 0] ++ cr) ρ reserved)
    (hu : Umf L A C dv m fp Ks K H) (hk : Kopf L f m fp K rp cfp ρ0 P σ0) (hWa : WeltAt m L σ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * ([ci 1 (frei Γ reserved) (L.ga g) 0, ci 15 (frei Γ reserved) (frei Γ reserved) 0] ++ cr).length))
      (pc + BitVec.ofNat 64 (16 * ([ci 1 (frei Γ reserved) (L.ga g) 0, ci 15 (frei Γ reserved) (frei Γ reserved) 0] ++ cr).length) +
        BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * ([ci 1 (frei Γ reserved) (L.ga g) 0, ci 15 (frei Γ reserved) (frei Γ reserved) 0] ++ cr).length) +
        BitVec.ofInt 64 ex.2)
      (execBlock O passes R (.awaits g pl hpl hL hat rest) σ ρ) reserved := by
  simp only [execBlock, SichtOK.sicht, ↓reduceIte]
  obtain ⟨m1, s1, A, hp1, hW1⟩ := awaits_head hfit hl hs1 hW hp hWa
  have ih := hrest m1 ((σ.fragt (.inr (.inr g))).lese Λ [.inr g]) _ hp1
    (hu.agreeW hW (A.mono hlo2) hlo) (hk.agreeW hW (A.mono hlo2) (by omega)) hW1
  rw [pc_add1]
  exact Sim.prefix hlo s1 (A.mono hlo2) (keeps_of_agreeW hW A hpr (by have := hW.ks; omega)) (Sim.schrumpf ih)

end

end Gabbro.Stage0.Senke
