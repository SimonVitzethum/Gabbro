/- Subject: Capture both operands, then write the byte span against machine G. -/
module
public import Stage0.Senke.Anweisung.Bytes.Write
public import Stage0.Senke.Anweisung.Simulation
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 2048
variable {reserved : Nat}
variable [Kern] {D : Deklaration}

theorem putBytes_ok {L : Lay D} {P : Programm D} {f : D.Fn} {σ0 : World D}
    {ρ0 : Env D (D.params f)} {rp cfp fp pc : Runner.W} {K Ks lo : Nat} {pr : List Nat}
    {A : D.Fn → Nat} {ens : List II × Nat} {ex : Int × Int} {O : Orakel D} {passes : Nat}
    {R : (g : D.Fn) → World D → Env D (D.params g) → RufAusgang g}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {t : D.Tab} {field : D.Feld t} {a b : Int}
    (hf : D.typ t field = .int 0 255) (n : Nat) (i : Expr D Γ Λ (.int a b))
    (hlo : 0 ≤ a) (hhi : b + n ≤ D.count t) (e : Expr D Γ Λ (.int 0 (256 ^ n - 1)))
    (hw : (vertragVon D f).schreibt t = true) (hl : darf D t Λ)
    {c : List II} {top : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) ens pr ex (Stmt.putBytes (l := l) t field hf n i hlo hhi e hw hl) = some (c, top))
    (hK : top ≤ Ks) (hW : WIn L fp Ks K) (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlow : lo ≤ frei Γ reserved) (hWa : WeltAt m L σ) (hpr : ∀ j ∈ pr, j < frei Γ reserved) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (Stmt.putBytes (l := l) t field hf n i hlo hhi e hw hl) σ ρ) reserved := by
  simp only [lowS, resultWords_vertragVon] at h
  split at h
  · next hn =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨ci', ti⟩, hi, ⟨cb, tb⟩, hb, h⟩ := h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hbnd : b < 2 ^ 64 := by
      by_contra hh
      have hcell := hW.lay.1 t field (b.toNat - 1) (L.bounded (by omega))
      have hsmall := hW.lay.2.2
      have cw : valueWords (D.typ t field) = 1 := by rw [hf]; rfl
      simp only [Lay.elem, cw] at hcell
      omega
    have hpow0 : (256 : Int) ^ n ≤ (256 : Int) ^ 8 := by
      exact_mod_cast (Nat.pow_le_pow_right (n := 256) (i := n) (by decide) hn)
    have hvalue : valueWords (.int 0 (256 ^ n - 1)) = 1 :=
      integerWords_unsigned (by omega) (by norm_num at hpow0 ⊢; omega)
    have hindex : valueWords (.int a b) = 1 := integerWords_unsigned hlo hbnd
    have hks := hW.ks
    have hte := lowE_top e _ _ _ he
    have hti := lowE_top i _ _ _ hi
    have htb := putBytesL_top hb
    let σE := σ.lese Λ (i.orte ++ e.orte)
    let z := eval σE e σE ρ
    let k := eval σE i σE ρ
    have hq : PreS L m pc fp K (frei Γ reserved) (ce ++ (ci' ++ cb)) ρ reserved := by simpa only [List.append_assoc] using hp
    have hpe := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, s1, a1s, valueE⟩ := lowE_ok (same := by intro _; rfl) σE σE (fun _ h => h) hW.lay e _ ce te he (by omega) m pc ρ hpe
    obtain ⟨we, re, ene⟩ := ValueAt.word (.int 0 (256 ^ n - 1)) z trivial valueE
    have a1 := Agree.widen a1s hks
    have hw1 : WeltAt m1 L σE := hpe.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
    have hp1 := hq.next a1 (Nat.le_refl _) (by omega)
    have hpi := PreS.welt (hp1.left.up (d' := frei Γ reserved + 1) (by omega)) hks hw1 hW.lay (by have := hW.lo; omega)
    obtain ⟨m2, s2, a2s, valueI⟩ := lowE_ok (same := by intro _; rfl) σE σE (fun _ h => h) hW.lay i _ ci' ti hi (by omega) m1 _ ρ hpi
    obtain ⟨wi, ri, eni⟩ := ValueAt.word (.int a b) k trivial valueI
    have a2 := Agree.widen a2s hks
    have hw2 : WeltAt m2 L σE := hpi.wstab m1 m2 hw1 (a2s.mono (Nat.zero_le _))
    have enz1 : EnvAt L m1 fp (Env.cons z ρ) reserved :=
      envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) valueE
    have enz2 : EnvAt L m2 fp (Env.cons z ρ) reserved := envAt_agree enz1 a2 hp1.frame
      (by simp only [frei, contextWords_cons, hvalue, hindex]; omega) (by omega)
    have enk : EnvAt L m2 fp (Env.cons k (Env.cons z ρ)) reserved := by
      have hr : m2.rd64 (slot fp (BitVec.ofNat 64 (frei ((.int 0 (256 ^ n - 1)) :: Γ) reserved))) = some wi := by
        simpa only [frei, contextWords_cons, hvalue, Nat.add_assoc] using ri
      exact envAt_cons enz2 (by
        simpa only [frei, contextWords_cons, hvalue, Nat.add_assoc] using valueI)
    have hp2 := hp1.next (a := ci') (a2.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
    have hpb : PreS L m2 (pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * ci'.length)) fp K
        (frei Γ reserved + 2) cb (Env.cons k (Env.cons z ρ)) reserved :=
      ⟨by simp only [frei, contextWords_cons, hvalue, hindex]; omega, hp.small, hp2.frame, hp2.code, hp2.far, enk,
        trivial, wstab_true _ _⟩
    have hpow : (256 : Int) ^ n ≤ (256 : Int) ^ 8 := by
      have hh := Nat.pow_le_pow_right (n := 256) (i := n) (by decide) hn
      have hh' : ((256 ^ n : Nat) : Int) ≤ ((256 ^ 8 : Nat) : Int) := by omega
      simpa only [Int.natCast_pow, show ((256 : Nat) : Int) = 256 by rfl] using hh'
    have hz : z.n < 2 ^ 64 := by have := z.le_hi; omega
    obtain ⟨m3, s3, a3, en3, hw3⟩ := putBytesL_ok hf hlo hW z k ρ hz n 0 _ (by omega) cb tb hb (by omega) m2 _ σE hpb hw2
    have aa : AgreeW L fp (frei Γ reserved) K m m3 :=
      (agreeW_of (a1.trans (a2.mono (Nat.le_succ _)))).trans (a3.mono (by omega))
    simp only [execStmt, Sim]
    refine ⟨m3, s1.trans (s2.trans ?_), aa.mono hlow, envAt_tail (envAt_tail en3), ?_,
      keeps_of_agreeW hW aa hpr (by omega)⟩
    · simpa only [List.length_append, pc_add] using s3
    · simpa only [dropBytes, Int.natCast_zero, Int.add_zero] using hw3

  · cases h

end Gabbro.Stage0.Senke
