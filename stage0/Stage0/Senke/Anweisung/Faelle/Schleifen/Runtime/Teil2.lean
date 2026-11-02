module

public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counters.Counter
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Counted.Teil3
public import Stage0.Senke.Anweisung.Simulation
public import Stage0.Senke.Anweisung.Verzweigung
public import Stage0.Senke.Anweisung.Faelle.Kontext
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner Runner.IR
variable [Kern]

/-- Execute the actual source invariant and then the generically lowered body.
    The read event, callee frame, return ABI and protected slots are inherited
    from `lowE_ok`, `choice_ok` and the explicit child induction contract.
    This is one positive pass, not yet the counter/header integration. -/
theorem forever_source_pass {D : Deklaration} {L : Lay D}
    {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp rp cfp : W} {K Ks lo : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)}
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D f) true Γ Λ Λ)
    {cc cb : List II} {tc tb : Nat}
    (hcc : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (hcb : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr (exPlus ex 4) body = some (cb, tb))
    (htc : tc ≤ Ks) (htb : tb + cap ≤ Ks) (room : frei Γ reserved + 8 ≤ Ks)
    (hs : 16 * (cc.length + 1 + cb.length + 1 + 3) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    (bodyRuns : BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp
      σ0 ρ0 cens tens pr (exPlus ex 4) body reserved)
    {m : Mem} {pc : W} {σ : World D} {ρ : Env D Γ}
    (hp : PreS L m pc fp K (frei Γ reserved)
      (cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)) ρ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hw : WeltAt m L σ) :
    let code := cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
      [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * code.length))
      (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * code.length) + BitVec.ofInt 64 ex.2)
      (if wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) then
        execBlock O passes R body (σ.lese Λ inv.orte) ρ else .logik .schleife) reserved := by
  have protectedPrefix := functionFrame_prefix P f
  have hks := hW.ks
  have htop := lowE_top inv (frei Γ reserved) cc tc hcc
  apply choice_ok (d := frei Γ reserved) (ct := cb) (ce := stopC 104 (frei Γ reserved))
    (Nat.le_refl _) (by omega) (by simpa [stopC, sysC] using hs) hW hlo hlo0 hlo2 hpr
  · intro hpc
    have hpw := PreS.welt hpc hks hw hW.lay (by have := hW.lo; omega)
    obtain ⟨m1, st, a1, w, hr, hen⟩ := lowE_ok (same := by intro _; rfl) (σ.lese Λ inv.orte) (σ.lese Λ inv.orte)
      (fun _ h => h) hW.lay inv (frei Γ reserved) cc tc hcc (by omega) m pc ρ hpw |>.word trivial
    exact ⟨m1, st, Agree.widen a1 hks, w, hr, hen⟩
  · intro _ m' pc' hp' _ hu' hk' hw'
    exact bodyRuns cb tb hcb htb (by omega) hW
      m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr
  · intro _ m' pc' hp' _ _ _ _
    exact stop_ok hp'.code hp'.far hp'.frame (by omega) hp'.small (by simp [logikCode])
  · exact hp
  · exact hu
  · exact hk
  · exact hw

/-- Compose the emitted counter header with the actual generic invariant/body lowering
    and induct on semantic fuel, retaining the concrete entry interface. -/
theorem forever_counter_loop {D : Deklaration} {L : Lay D}
    {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : W} {cap : Nat}
    (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31)
    {P : Programm D} {f : D.Fn} {fp rp cfp : W} {K Ks lo : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {counter one : Nat}
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} {Γ : Ctx} {Λ : List (Res D)}
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D f) true Γ Λ Λ)
    {cc cb : List II} {tc tb : Nat}
    (hcc : lowE (reserved := reserved) L inv (frei Γ reserved) = some (cc, tc))
    (hcb : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) (counter :: one :: pr) (exPlus ex 4) body = some (cb, tb))
    (htc : tc ≤ Ks) (htb : tb + cap ≤ Ks) (room : frei Γ reserved + 8 ≤ Ks)
    (hs : 16 * (cc.length + 1 + cb.length + 1 + 3) < 2 ^ 31)
    (hW : WIn L fp Ks K) (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ reserved)
    (hpr : ∀ j ∈ counter :: one :: pr, j < frei Γ reserved)
    (bodyRuns : BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp
      σ0 ρ0 cens tens (counter :: one :: pr) (exPlus ex 4) body reserved)

    {pc back exit outerLeave outerNext : W} {stop : Int} {jump b c : BitVec 32}
    (backAt : pc + 32 + BitVec.ofNat 64
      (16 * (cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved)).length) = back)
    (leaveAt : back + BitVec.ofInt 64 ex.1 = exit)
    (nextAt : back + BitVec.ofInt 64 ex.2 = pc)
    (jumpAt : back + sx jump = pc)
    (low : lo ≤ counter) (allocated : counter < FB + reserved)
    (oneBound : one < K) (distinct : one ≠ counter)
    (hprotected : ∀ j ∈ pr, j < K ∧ j ≠ counter)
    (backFar : CodeFar back 1 fp K)
    (stopFar : CodeFar (pc + sx (BitVec.ofInt 32 stop)) 3 fp K)
    (stopRoom : frei Γ reserved + 8 ≤ K)
    {l : Bool} (a : D.Annahme)
    {m : Mem} {σ : World D} {ρ : Env D Γ} {budget : Nat}
    (fits : budget < 2 ^ 64)
    (pre : PreS L m pc fp K (frei Γ reserved)
      (foreverCounter counter one stop ++
        (cc ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
          [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))) ρ reserved)
    (surround : Umf L A C dv m fp Ks K)
    (head : Kopf L f m fp K rp cfp ρ0 P σ0) (world : WeltAt m L σ)
    (read : m.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 budget))
    (readOne : m.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1)
    (edge : InsAt m back 18 jump b c)
    (stopCode : CodeAt m (pc + sx (BitVec.ofInt 32 stop)) (stopC 111 (frei Γ reserved))) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
      (foreverLauf (l := l) a (execBlock O passes R body)
        (fun σ ρ => (σ.lese Λ inv.orte,
          wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) budget σ ρ) reserved := by
  have protectedPrefix := functionFrame_prefix P f
  have bound : frei Γ reserved ≤ K := by omega
  have inside : counter < K := by unfold frei at bound; omega
  induction budget generalizing m σ ρ with
  | zero =>
    have test := pre.code 0 (by simp [foreverCounter])
    simp [foreverCounter, ci] at test
    have sc := sx_nat (d := counter) (by have := pre.small; omega)
    exact counter_budget_stop_code test (by simpa [sc] using read)
      stopCode stopFar pre.frame stopRoom pre.small
  | succ n ih =>
    obtain ⟨m1, run, frame, hp, hu, hk, hw, keeps, count⟩ :=
      counter_header hW pre surround head world (by omega) low allocated
        (by omega) oneBound read readOne fits (by
          intro j hj
          rcases List.mem_cons.mp hj with h | h
          · subst j; exact ⟨oneBound, distinct⟩
          · exact hprotected j h)
    have pass := forever_source_pass (O := O) hS hA hlo0 hens inv body hcc hcb htc htb room hs
      hW hlo hlo2 hpr bodyRuns hp hu hk hw
    simp only [] at pass
    rw [backAt, leaveAt, nextAt] at pass
    have edge1 : InsAt m1 back 18 jump b c := by
      have hc : CodeAt m back [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
        intro k hk
        have : k = 0 := by simpa using hk
        subst k
        simpa [II.f] using edge
      have h := (codeAt_agreeWIn hW frame hc backFar) 0 (by simp)
      simpa [II.f] using h
    have again : ∀ σ' ρ',
        (∃ m', Star ⟨pc + 32, fp⟩ m1 ⟨pc, fp⟩ m' ∧ AgreeW L fp lo K m1 m' ∧
          EnvAt L m' fp ρ' reserved ∧ WeltAt m' L σ' ∧
          Keeps fp (counter :: one :: pr) m1 m' ∧
          m'.rd64 (slot fp (BitVec.ofNat 64 counter)) = some (BitVec.ofNat 64 n)) →
        Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m exit outerLeave outerNext
          (foreverLauf (l := l) a (execBlock O passes R body)
            (fun σ ρ => (σ.lese Λ inv.orte,
              wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ))) n σ' ρ') reserved := by
      intro σ' ρ' result
      obtain ⟨m2, run2, frame2, env2, world2, keeps2, count2⟩ := result
      have total := frame.trans frame2
      have kp : Keeps fp pr m m2 := fun j hj => (keeps2 j (by simp [hj])).trans (keeps j (by simp [hj]))
      have pre2 : PreS L m2 pc fp K (frei Γ reserved) _ ρ' reserved :=
        ⟨pre.ctx, pre.small, frameOK_agreeW pre.frame total,
          codeAt_agreeWIn hW total pre.code pre.far, pre.far, env2, trivial, wstab_true _ _⟩
      have edge2 : InsAt m2 back 18 jump b c := by
        have hc : CodeAt m1 back [⟨18, jump.toInt, b.toInt, c.toInt⟩] := by
          intro k hk
          have : k = 0 := by simpa using hk
          subst k
          simpa [II.f] using edge1
        have h := (codeAt_agreeWIn hW frame2 hc backFar) 0 (by simp)
        simpa [II.f] using h
      have one2 : m2.rd64 (slot fp (BitVec.ofNat 64 one)) = some 1 := by
        rw [keeps2 one (by simp), keeps one (by simp)]
        exact readOne
      exact Sim.prefix hlo (run.trans run2) total kp
        (ih (by omega) pre2 (surround.agreeW hW total (by omega))
          (head.agreeW hW total (by omega)) world2 count2 one2 edge2
          (codeAt_agreeWIn hW total stopCode stopFar))
    simp only [foreverLauf]
    split
    · rename_i hv
      simp [hv] at pass
      exact Stops.prefix run pass
    · rename_i hv
      have ht : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
        cases h : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) <;> simp_all
      simp only [ht, ite_true] at pass
      have dispatch := pass.counter_dispatch hW (Or.inr (by simp)) (by omega)
        count edge1 backFar jumpAt
      generalize execBlock O passes R body (σ.lese Λ inv.orte) ρ = o at pass dispatch ⊢
      cases o with
      | ok σ' ρ' => exact again σ' ρ' dispatch
      | next h σ' ρ' => exact again σ' ρ' dispatch
      | leave h σ' ρ' =>
        exact Reach.prefix run frame (fun j hj => keeps j (by simp [hj]))
          (by obtain ⟨m', r, f, e, w, k⟩ := dispatch
              exact ⟨m', r, f, e, w, fun j hj => k j (by simp [hj])⟩)
      | zurueck | why | logik | hardware =>
        exact Sim.prefix hlo run frame (fun j hj => keeps j (by simp [hj])) dispatch

end Gabbro.Stage0.Senke
