/- Simulation of finite retry expansion, including both loop exits and an enclosing loop's overflow exits. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Test

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable {reserved : Nat}
variable [Kern] {D : Deklaration} {L : Lay D}

section
variable {O : Orakel D} {passes : Nat}
  {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
  {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
  {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
  {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
  {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
  {bis : Expr D Γ Λ .bool} {body : Block D (vertragVon D f) true Γ Λ Λ}
  {overflow : Block D (vertragVon D f) l Γ Λ Λ} {cc cu : List II × Nat}

theorem retryC_ok (hlo0 : lo = FB + (D.params f).length)
    (hcc : lowE (reserved := reserved) L bis (frei Γ reserved) = some cc)
    (hcu : lowB (reserved := reserved) passes A L lo (cens, tens) pr ex overflow = some cu)
    (ihBody : ∀ {ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex body reserved)
    (ihOverflow : BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex overflow reserved) :
    ∀ (n : Nat) (c : List II) (top : Nat),
    retryC (frei Γ reserved) cc cu (fun ex => lowB (reserved := reserved) passes A L lo (cens, tens) pr ex body) n = some (c, top) →
    top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K →
    ∀ m pc σ ρ, PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved →
    Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ →
    (∀ j ∈ pr, j < frei Γ reserved) →
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length))
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2)
      (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        (fun σ ρ => execBlock O passes R overflow σ ρ) n σ ρ) reserved := by
  intro n
  induction n with
  | zero =>
    intro c top hc hK hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr
    simp only [retryC, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [retryLauf]
    exact retryTest_ok hcc (by omega)
      (by simpa only [retryTest, List.length_append, List.length_singleton] using hs)
      hW hlo hlo0 hlo2 hpr
      (fun m' pc' hp' hu' hk' hw' => ihOverflow cu.1 cu.2 hcu (by omega)
        (by simp only [retryTest, List.length_append, List.length_singleton] at hs; omega)
        hW m' pc' _ ρ hp' hlo hlo2 hu' hk' hw' hpr) hp hu hk hw
  | succ n ih =>
    intro c top hc hK hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr
    simp only [retryC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hc
    obtain ⟨⟨cr, tr⟩, hr, ⟨cb, tb⟩, hb, he⟩ := hc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [retryTest, List.length_append, List.length_singleton] at hs
    simp only [retryLauf]
    apply retryTest_ok hcc (by omega) (by simpa using hs) hW hlo hlo0 hlo2 hpr
      (hp := hp) (hu := hu) (hk := hk) (hWa := hw)
    intro m' pc' hp' hu' hk' hw'
    have ib := ihBody (ex := (16 * cr.length, 0)) cb tb hb (by omega) (by omega)
      hW m' pc' (σ.lese Λ bis.orte) ρ hp'.left hlo hlo2 hu' hk' hw' hpr
    have hEnd : pc' + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 (16 * (cr.length : Int)) =
        pc' + BitVec.ofNat 64 (16 * (cb ++ cr).length) := by
      simp only [List.length_append]
      have hh := tgt_eq (p := pc') (x := 0) (a := 16 * cb.length)
        (b := 16 * (cb.length + cr.length)) (n := cr.length) (by omega)
      simpa using hh
    have hNext : pc' + BitVec.ofNat 64 (16 * cb.length) + BitVec.ofInt 64 0 =
        pc' + BitVec.ofNat 64 (16 * cb.length) := by simp
    have cont : ∀ σ1 ρ1,
        Reach L fp lo K pr ⟨pc', fp⟩ m' (pc' + BitVec.ofNat 64 (16 * cb.length)) σ1 ρ1 reserved →
        Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc', fp⟩ m'
          (pc' + BitVec.ofNat 64 (16 * (cb ++ cr).length))
          (pc' + BitVec.ofNat 64 (16 * (cb ++ cr).length) + BitVec.ofInt 64 ex.1)
          (pc' + BitVec.ofNat 64 (16 * (cb ++ cr).length) + BitVec.ofInt 64 ex.2)
          (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
            (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
            (fun σ ρ => execBlock O passes R overflow σ ρ) n σ1 ρ1) reserved := by
      intro σ1 ρ1 hreach
      obtain ⟨m1, s1, a1, e1, w1, k1⟩ := hreach
      have hf := codeFar_right (n := cb.length) (k := cr.length) (by simpa using hp'.far)
      have hp1 : PreS L m1 (pc' + BitVec.ofNat 64 (16 * cb.length)) fp K (frei Γ reserved) cr ρ1 reserved :=
        mkPreS (Nat.le_refl _) hp'.small (frameOK_agreeW hp'.frame a1)
          (codeAt_agreeWIn hW a1 (codeAt_right hp'.code) hf) hf e1
      have ir := ih cr tr hr (by omega) (by omega) hW m1 _ σ1 ρ1 hp1 hlo hlo2
        (hu'.agreeW hW a1 hlo) (hk'.agreeW hW a1 (by omega)) w1 hpr
      rw [pc_add1]
      exact Sim.prefix hlo s1 a1 k1 ir
    generalize execBlock O passes R body (σ.lese Λ bis.orte) ρ = o at ib ⊢
    cases o with
    | ok σ1 ρ1 => exact cont σ1 ρ1 ib
    | next h σ1 ρ1 => exact cont σ1 ρ1 (by simpa only [Sim, hNext] using ib)
    | leave h σ1 ρ1 => simpa only [Sim, hEnd] using ib
    | zurueck | why | logik | hardware => exact ib
end

theorem retry_case {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
    {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = FB + (D.params f).length) {pr : List Nat} {ex : Int × Int}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {bis : Expr D Γ Λ .bool}
    {body : Block D (vertragVon D f) true Γ Λ Λ} {overflow : Block D (vertragVon D f) l Γ Λ Λ}
    (ihBody : ∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex body reserved)
    (ihOverflow : ∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex overflow reserved) :
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex (.retry n bis body overflow) reserved := by
  intro c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr
  simp only [lowS, bind, Option.bind_eq_some_iff] at h
  obtain ⟨cc, hcc, cu, hcu, hc⟩ := h
  exact retryC_ok hlo0 hcc hcu ihBody ihOverflow n c top hc hK hs hW m pc σ ρ hp hlo hlo2 hu hk hw hpr

/-- Fuel zero stops before even reading the invariant. -/
theorem forever_zero {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (O : Orakel D) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O 0 R (show Stmt D V l Γ Λ Λ from .forever a inv body) σ ρ = .hardware (.fortschritt a) := rfl

/-- One pass checks a false invariant, whereas zero passes answers the progress assumption. -/
theorem forever_one_false {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (a : D.Annahme) (body : Block D V true Γ Λ Λ)
    (O : Orakel D) (R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O 1 R (show Stmt D V l Γ Λ Λ from .forever a .fls body) σ ρ = .logik .schleife := rfl

/-- Refuse until the lowering and its call interface receive the same fuel as G. -/
theorem forever_refused {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {l : Bool}
    (A : D.Fn → Nat) (lo : Nat) (ens : List II × Nat) (pr : List Nat) (ex : Int × Int)
    (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) :
    lowS passes A L lo ens pr ex (show Stmt D V l Γ Λ Λ from .forever a inv body) = none := rfl

end Gabbro.Stage0.Senke
