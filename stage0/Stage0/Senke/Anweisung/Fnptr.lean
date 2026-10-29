/-
  Subject: Indirect calls and their continuations, sharing the direct call's frame proof.
-/
import Stage0.Senke.Anweisung.Simulation

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem encErg_wert {e : Option Ty} {τ : Ty} (he : e = some τ) {v : ErgVal D e} {w : Runner.W}
    (h : EncErg L e v w) : Enc L τ (ergWert he v) w := by
  subst he; exact h

/-- Transport of the context preserves every encoded variable. -/
theorem envAt_cast {ts us : Ctx} (e : ts = us) {m : Runner.Mem} {fp : Runner.W} {ρ : Env D ts}
    (h : EnvAt L m fp ρ) : EnvAt L m fp ((congrArg (Env D) e).mp ρ) := by cases e; exact h

/-- Reindexing the parameter environment changes no value word or frame slot. -/
theorem envAt_umsig {f : D.Fn} {n : Nat} (hf : D.passt f n = true) {m : Runner.Mem} {fp : Runner.W}
    {ρ : Env D (D.sigNr n).params} (h : EnvAt L m fp ρ) : EnvAt L m fp (umsig hf ρ) := by
  exact envAt_cast (show (D.sigNr n).params = D.params f from (D.passt_sig hf).params.symm) h

/-- An indirect call evaluates the pointer and arguments once, resolves its signature witness,
    and invokes the same callee specification as a direct call. -/
theorem lowInd_ok {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {Λ : List (Res D)} {Γ : Ctx} {n : Nat} (p : Expr D Γ Λ (.fnptr n))
    (args : Args D Γ Λ (D.sigNr n).params) (σ₀ σ : World D) {c : List II} {top : Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {ρ : Env D Γ}
    (hc : lowInd L p args = some (c, top)) (ht : top + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ) c ρ) (hu : Umf L A C dv m fp Ks K)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    let v := eval σ₀ p σ ρ
    match R v.1 σ (umsig v.2 (evalArgs σ₀ args σ ρ)) with
    | .ok σ' r => ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧
        AgreeW L fp (frei Γ) K m m' ∧
        (∃ w, m'.rd64 (slot fp (BitVec.ofNat 64 (frei Γ + 2))) = some w ∧ EncErg L (D.erg v.1) r w) ∧
        WeltAt m' L σ'
    | .logik e => Stops ⟨pc, fp⟩ m (logikCode e)
    | .hardware h => Stops ⟨pc, fp⟩ m (hwCode h)
    | _ => False := by
  simp only [lowInd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨⟨cp, tp⟩, hcp, ⟨ca, ta⟩, hca, rfl, rfl⟩ := hc
  simp only [indTop] at ht
  have hFB3 : FB = 3 := rfl
  have hks := hW.ks
  have hFB : FB ≤ frei Γ := by simp only [frei]; omega
  have hpar := (D.passt_sig (eval σ₀ p σ ρ).2).params
  change D.params (eval σ₀ p σ ρ).1 = (D.sigNr n).params at hpar
  have hp0 : PreS L m pc fp K (frei Γ) (cp ++ (ca ++ callTailN (D.sigNr n).params.length 0 (frei Γ) true)) ρ := hp
  have hpw := PreS.welt hp0.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, w, hw, he⟩ := lowE_ok σ₀ σ (fun _ h => h) p _ cp tp hcp (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hp1 := hp0.next (d' := frei Γ + FB) a1 (by omega) (by omega)
  have hpw1 := PreS.welt hp1.left hks (hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))) hW.lay (by have := hW.lo; omega)
  obtain ⟨m2, s2, a2s, e2⟩ := lowA_ok (F := frei Γ) σ₀ σ (fun _ h => h) args ca ta hca (by omega) (by omega) m1 _ ρ hpw1
  have a2 := Agree.widen a2s hks
  have hp2 := hp1.next a2 (Nat.le_refl _) (by omega)
  have hWa2 := hpw1.wstab m1 m2 hpw1.welt (a2s.mono (Nat.zero_le _))
  have hu2 := (hu.agree a1 hp.frame (by omega)).agree a2 hp1.frame (by omega)
  have htail : callTailN (D.sigNr n).params.length 0 (frei Γ) true =
      callTail A (eval σ₀ p σ ρ).1 (frei Γ) true := by simp only [callTail, callTailN, hpar, ↓reduceIte]
  rw [htail] at hp2
  have hr : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some (BitVec.ofNat 64 (A (eval σ₀ p σ ρ).1)) := by
    rw [agree_rd_low a2 hp1.frame.room (by omega) (by omega), hw]
    simp only [Enc, hS.addr] at he
    exact congrArg some he
  have hc2 := call_ok (indirect := true) (f := (eval σ₀ p σ ρ).1) (F := frei Γ) (Ks := Ks) hS hp2.code (by exact hp2.far) hp2.frame hp.small hFB
    (by rw [hpar]; omega) (by omega) (hA _) hu2.code hu2.depth (envAt_umsig (eval σ₀ p σ ρ).2 e2) hW hWa2 hu2.sync (fun _ => hr)
  dsimp only
  generalize R (eval σ₀ p σ ρ).1 σ (umsig (eval σ₀ p σ ρ).2 (evalArgs σ₀ args σ ρ)) = o at hc2 ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m3, s3, a3, w3, hw3⟩ := hc2
    refine ⟨m3, s1.trans (s2.trans ?_), (agreeW_of a1).trans ((agreeW_of (a2.mono (by omega))).trans a3), w3, hw3⟩
    simpa only [indC, List.length_append, callTail, callTailN, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc, pc_add] using s3
  | logik e => exact Stops.prefix s1 (Stops.prefix s2 hc2)
  | hardware e => exact Stops.prefix s1 (Stops.prefix s2 hc2)
  | why _ _ => exact hc2.elim

/-- Every indirect call reserves the callee header, arguments and target temporary. -/
theorem lowInd_top {Λ : List (Res D)} {Γ : Ctx} {n : Nat} {p : Expr D Γ Λ (.fnptr n)}
    {args : Args D Γ Λ (D.sigNr n).params} {c : List II} {top : Nat}
    (h : lowInd L p args = some (c, top)) : frei Γ + FB + (D.sigNr n).params.length + 1 ≤ top := by
  simp only [lowInd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cp, tp⟩, _, ⟨ca, ta⟩, _, _, rfl⟩ := h
  simp only [indTop]; omega

/-- An ignored indirect result keeps the caller environment and protected slots. -/
theorem indStmt_ok {O : Orakel D} {passes : Nat} {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hfit : RufPasst D (vertragVon D f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    {σ0 : World D} {ρ0 : Env D (D.params f)} {rp cfp fp pc : Runner.W} {lo K Ks : Nat}
    {pr : List Nat} {ex : Int × Int} {c : List II} {top : Nat} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (hc : lowInd L p args = some (c, top)) (ht : top + cap ≤ Ks) (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K (frei Γ) c ρ) (hlo : lo ≤ frei Γ) (hu : Umf L A C dv m fp Ks K)
    (hWa : WeltAt m L σ) (hpr : ∀ j ∈ pr, j < frei Γ) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
      (execStmt O passes R (Stmt.callInd (l := l) p args hfit hr) σ ρ) := by
  have hb := lowInd_top hc
  have hks := hW.ks
  have hi := lowInd_ok hS hA p args (σ.lese Λ (p.orte ++ args.orte)) (σ.lese Λ (p.orte ++ args.orte)) hc ht hp hu hW hWa
  simp only [execStmt]
  dsimp only at hi
  generalize hv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = v at hi ⊢
  obtain ⟨g, hg⟩ := v
  dsimp only at hi ⊢
  generalize R g (σ.lese Λ (p.orte ++ args.orte))
    (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args (σ.lese Λ (p.orte ++ args.orte)) ρ)) = o at hi ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m1, s1, a1, _, hw1⟩ := hi
    exact ⟨m1, s1, a1.mono hlo, envAt_agreeWIn hW hp.env a1 (Nat.le_refl _) (by omega), hw1,
      keeps_of_agreeW hW a1 hpr (by omega)⟩
  | logik e => exact hi
  | hardware e => exact hi
  | why _ _ => exact hi.elim

/-- The shared result dispatch of the two indirect binder forms. -/
def indAntwort {β : Type} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hr : (D.sigNr n).gruende = 0) (σ : World D) (ρ : Env D Γ)
    (k : World D → Wert D τ → β) (err : Logik D → β) (hwerr : Hardware D → β) : β :=
  let ⟨f, hf⟩ := eval σ p σ ρ
  match R f σ (umsig hf (evalArgs σ args σ ρ)) with
  | .ok σ' r => k σ' (ergWert (ergSig hf he) r)
  | .why _ r => keinGrundSig hf hr r
  | .logik e => err e
  | .hardware e => hwerr e

section
variable {V : Vertrag D} {O : Orakel D} {passes : Nat}
  {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
  {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} {τ : Ty}
  {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
  {he : (D.sigNr n).erg = some τ} {hf : RufPasst D V (D.sigNr n) Λ} {hr : (D.sigNr n).gruende = 0}

theorem execBlock_ind_eq (rest : Block D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ') (σ : World D) (ρ : Env D Γ) :
    execBlock O passes R (.bindCallInd p args he hf hr rest) σ ρ =
      indAntwort R p args he hr (σ.lese Λ (p.orte ++ args.orte)) ρ
        (fun σ' v => (execBlock O passes R rest σ' (.cons v ρ)).schrumpf) .logik .hardware := rfl

theorem execEnd_ind_eq (rest : Endblock D V l (τ :: Γ) (nachSig D (D.sigNr n) Λ)) (σ : World D) (ρ : Env D Γ) :
    execEnd O passes R (.bindCallInd p args he hf hr rest) σ ρ =
      indAntwort R p args he hr (σ.lese Λ (p.orte ++ args.orte)) ρ
        (fun σ' v => (execEnd O passes R rest σ' (.cons v ρ)).schrumpf) .logik .hardware := rfl

end

/-- One binder prefix, independent of whether its continuation is a block or an end block.
    The continuation predicate supplies only prefix closure and the two stopping outcomes. -/
theorem indBind_ok {β : Type} {A : D.Fn → Nat} {C : D.Fn → List II}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {dv : Runner.W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {f : D.Fn} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hr : (D.sigNr n).gruende = 0)
    {fp rp cfp pc : Runner.W} {ρ0 : Env D (D.params f)} {lo K Ks : Nat} {pr : List Nat}
    {cc cr : List II} {tc : Nat} {m : Runner.Mem} (σ : World D) (ρ : Env D Γ)
    (hc : lowInd L p args = some (cc, tc)) (ht : tc + cap ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ) (cc ++ [ci 2 (frei Γ) (frei Γ + 2) 0] ++ cr) ρ)
    (hW : WIn L fp Ks K) (hlo0 : lo = FB + (D.params f).length) (hlo : lo ≤ frei Γ) (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0) (hWa : WeltAt m L σ) (hpr : ∀ j ∈ pr, j < frei Γ)
    (k : World D → Wert D τ → β) (err : Logik D → β) (hwerr : Hardware D → β)
    (J : T → Runner.Mem → β → Prop)
    (jprefix : ∀ {t0 t1 m0 m1 b}, Star t0 m0 t1 m1 → AgreeW L fp lo K m0 m1 →
      Keeps fp pr m0 m1 → J t1 m1 b → J t0 m0 b)
    (jerr : ∀ t m e, Stops t m (logikCode e) → J t m (err e))
    (jhw : ∀ t m e, Stops t m (hwCode e) → J t m (hwerr e))
    (kont : ∀ m' σ' v, let pc' := pc + BitVec.ofNat 64 (16 * (cc ++ [ci 2 (frei Γ) (frei Γ + 2) 0]).length)
      PreS L m' pc' fp K (frei (τ :: Γ)) cr (Env.cons v ρ) →
      Umf L A C dv m' fp Ks K → Kopf L f m' fp K rp cfp ρ0 → WeltAt m' L σ' → J ⟨pc', fp⟩ m' (k σ' v)) :
    J ⟨pc, fp⟩ m (indAntwort R p args he hr σ ρ k err hwerr) := by
  have hb := lowInd_top hc
  have hFB3 : FB = 3 := rfl
  have hks := hW.ks
  have hi := lowInd_ok hS hA p args σ σ hc ht hp.left.left hu hW hWa
  dsimp only [indAntwort] at hi ⊢
  generalize hv : eval σ p σ ρ = v at hi ⊢
  obtain ⟨g, hg⟩ := v
  dsimp only at hi ⊢
  generalize R g σ (umsig hg (evalArgs σ args σ ρ)) = o at hi ⊢
  cases o with
  | ok σ' v =>
    obtain ⟨m1, s1, a1, ⟨w, hw, hew⟩, hw1⟩ := hi
    have hp1 := hp.left.nextW hW a1 (by have := hp.ctx; omega) (Nat.le_refl _) (by omega)
    have s2 := mov_to hp1.code hp1.frame (j := frei Γ) (s := frei Γ + 2) (by omega) (by omega) hp.small hw
    rw [← pc_add1] at s2
    let m2 := write m1 (slot fp (BitVec.ofNat 64 (frei Γ))) 8 w.toNat
    have a2s : Agree fp (frei Γ) Ks m1 m2 := agree_write (frameOK_sub hp1.frame hks).room (Nat.le_refl _) (by omega) _
    have a2 : Agree fp (frei Γ) K m1 m2 := Agree.widen a2s hks
    have hw2 : WeltAt m2 L σ' := weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hw1 (a2s.mono (Nat.zero_le _))
    have hq := hp.nextW hW (a1.trans (agreeW_of a2)) (d' := frei Γ + 1) (by have := hp.ctx; omega) (by omega) (by omega)
    have hp2 : PreS L m2 _ fp K (frei (τ :: Γ)) cr (Env.cons (ergWert (ergSig hg he) v) ρ) :=
      ⟨by simp only [frei, List.length_cons]; omega, hq.small, hq.frame, hq.code, hq.far,
       envAt_cons hq.env (rd_same hp1.frame (by omega) w) (encErg_wert (ergSig hg he) hew), trivial, wstab_true _ _⟩
    exact jprefix (s1.trans s2) ((a1.trans (agreeW_of a2)).mono hlo)
      (keeps_of_agreeW hW (a1.trans (agreeW_of a2)) hpr (by omega))
      (kont m2 σ' _ hp2 (hu.agreeW hW (a1.trans (agreeW_of a2)) (by omega))
        (hk.agreeW hW (a1.trans (agreeW_of a2)) (by omega)) hw2)
  | logik e => exact jerr _ _ e hi
  | hardware e => exact jhw _ _ e hi
  | why _ _ => exact hi.elim

end Gabbro.Stage0.Senke
