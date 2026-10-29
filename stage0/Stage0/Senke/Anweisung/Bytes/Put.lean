/- Subject: Capture both operands, then write the byte span against machine G. -/
import Stage0.Senke.Anweisung.Bytes.Write
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxRecDepth 2048
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
    (h : lowS A L lo ens pr ex (Stmt.putBytes (l := l) t field hf n i hlo hhi e hw hl) = some (c, top))
    (hK : top ≤ Ks) (hW : WIn L fp Ks K) (hp : PreS m pc fp K (frei Γ) c ρ)
    (hlow : lo ≤ frei Γ) (hWa : WeltAt m L σ) (hpr : ∀ j ∈ pr, j < frei Γ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (Stmt.putBytes (l := l) t field hf n i hlo hhi e hw hl) σ ρ) := by
  simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, he, ⟨ci', ti⟩, hi, ⟨cb, tb⟩, hb, h⟩ := h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hks := hW.ks
  have hte := lowE_top e _ _ _ he
  have hti := lowE_top i _ _ _ hi
  have htb := putBytesL_top hb
  let σE := σ.lese Λ (i.orte ++ e.orte)
  let z := eval σE e σE ρ
  let k := eval σE i σE ρ
  have hq : PreS m pc fp K (frei Γ) (ce ++ (ci' ++ cb)) ρ := by simpa only [List.append_assoc] using hp
  have hpe := PreS.welt hq.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, we, re, ene⟩ := lowE_ok σE σE (fun _ h => h) e _ ce te he (by omega) m pc ρ hpe
  have a1 := Agree.widen a1s hks
  have hw1 : WeltAt m1 L σE := hpe.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hp1 := hq.next a1 (Nat.le_refl _) (by omega)
  have hpi := PreS.welt (hp1.left.up (d' := frei Γ + 1) (by omega)) hks hw1 hW.lay (by have := hW.lo; omega)
  obtain ⟨m2, s2, a2s, wi, ri, eni⟩ := lowE_ok σE σE (fun _ h => h) i _ ci' ti hi (by omega) m1 _ ρ hpi
  have a2 := Agree.widen a2s hks
  have hw2 : WeltAt m2 L σE := hpi.wstab m1 m2 hw1 (a2s.mono (Nat.zero_le _))
  have enz1 : EnvAt m1 fp (Env.cons z ρ) :=
    envAt_cons (envAt_agree hp.env a1 hp.frame (Nat.le_refl _) (by omega)) re ene
  have enz2 : EnvAt m2 fp (Env.cons z ρ) := envAt_agree enz1 a2 hp1.frame
    (by simp only [frei, List.length_cons]; omega) (by omega)
  have enk : EnvAt m2 fp (Env.cons k (Env.cons z ρ)) := by
    have hr : m2.rd64 (slot fp (BitVec.ofNat 64 (frei ((.int 0 (256 ^ n - 1)) :: Γ)))) = some wi := by
      simpa only [frei, List.length_cons, Nat.add_succ] using ri
    exact envAt_cons enz2 hr eni
  have hp2 := hp1.next (a := ci') (a2.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  have hpb : PreS m2 (pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * ci'.length)) fp K
      (frei Γ + 2) cb (Env.cons k (Env.cons z ρ)) :=
    ⟨by simp only [frei, List.length_cons]; omega, hp.small, hp2.frame, hp2.code, hp2.far, enk,
      trivial, wstab_true _ _⟩
  obtain ⟨m3, s3, a3, en3, hw3⟩ := putBytesL_ok hf hlo hW z k ρ n 0 _ cb tb hb (by omega) m2 _ σE hpb hw2
  have aa : AgreeW L fp (frei Γ) K m m3 :=
    (agreeW_of (a1.trans (a2.mono (Nat.le_succ _)))).trans (a3.mono (by omega))
  simp only [execStmt, Sim]
  refine ⟨m3, s1.trans (s2.trans ?_), aa.mono hlow, envAt_tail (envAt_tail en3), ?_,
    keeps_of_agreeW hW aa hpr (by omega)⟩
  · simpa only [List.length_append, pc_add] using s3
  · simpa only [dropBytes, Int.natCast_zero, Int.add_zero] using hw3

end Gabbro.Stage0.Senke
