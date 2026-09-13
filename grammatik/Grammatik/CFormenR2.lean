/-
  File:      Grammatik/CFormenR2.lean
  Subject:   T4, three forms the earlier passes left out: `forever`
             (`for (;;)`), the signed saturation helper `_gabbro_sat_i`,
             and the wrapping shift `<<%`.

  THE EMITTED SHAPES (emit.rs, read 2026-09-13)
    forever (9861ff.): a watchdog declaration `static void (*const
      m_wachhund)(void) __attribute__((unused)) = f;` (no run-time
      effect: the C compiler reads the `on_exceeded` clause a second
      time), then `for (;;) { body [m_weiter: ;] } [m_ende: ;]` --
      `CS.loop`. Gabbro's `foreverLauf` runs `passes` rounds and then
      stands at the progress assumption (a hardware outcome, no
      obligation), so only runs that leave the loop within `passes`
      rounds carry one (`scorr_forever`).
    `_gabbro_sat_i` (SATURATION_PRELUDE, 11717ff.):
          if ((b > 0) && (a > hi - b)) { return hi; }
          if ((b < 0) && (a < lo - b)) { return lo; }
          return a + b;
      all in `int64_t` (`satIBody`, `satI_run`, `satI_zahl`).
    `<<%` (wrap_c, 11598ff., base operator `<<`):
      `(T)(((rt)(a) << (rt)(b)) & mask)`, unmasked at full storage width
      (`wrapC_shl`, the model half `Zahl.shlW`).

  NOT HERE: the `exchange update` CAS loop (its body jumps to
  `_cnN_fertig`, a label `CLbl` does not have, and its compare-exchange
  stands inside an `if` condition, where `CX` has no call); the byte
  writers (`s->bytes[i] = b;` under `if (!(i < N)) __builtin_trap();`).
-/
import Grammatik.CFormenR

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. `forever` -/

section Forever

variable (X : TVCtx D) (m m' : Nat) {Γ : Ctx} (K : CEnvLay D Γ) {V : Vertrag D} {l : Bool}
  {Λ : List (Res D)}

/-- The loop, by induction on the rounds left: `for (;;) { body }`
    against `foreverLauf`. -/
theorem forever_run (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (cbody : CS) (hbody : BlockSem X m' K body cbody) :
    ∀ (k : Nat) (σ : World D) (st : CSt) (ρG : Env D Γ) (ρC : CLok), corrW X.EL σ st →
      EnvRel X.EL K ρG ρC →
      (foreverLauf (V := V) (l := l) a (fun σ ρ => execBlock X.O X.passes X.R body σ ρ)
        (travInv inv) k σ ρG).istFehler = false →
      ∃ o, Exec X.EL.lay X.orc X.fr X.CR X.XR (CS.loop cbody m') st ρC o ∧
        StOut X m K (foreverLauf (V := V) (l := l) a
          (fun σ ρ => execBlock X.O X.passes X.R body σ ρ) (travInv inv) k σ ρG) o := by
  intro k
  induction k with
  | zero => intro σ st ρG ρC _ _ hnf; exact absurd hnf (by simp [foreverLauf, Ausgang.istFehler])
  | succ k ih =>
      intro σ st ρG ρC hc hr hnf
      rw [foreverLauf.eq_2] at hnf ⊢
      by_cases hi : (travInv inv σ ρG).2 = false
      · rw [if_pos hi] at hnf; exact Bool.noConfusion hnf
      rw [if_neg hi] at hnf ⊢
      have hc1 : corrW X.EL (travInv inv σ ρG).1 st := (corrW_lese _ _ _ _ _).mpr hc
      have hcond : ev X.EL.lay X.orc X.fr (.lit 1) st ρC = some (.int 1, st) := rfl
      cases hB : execBlock X.O X.passes X.R body (travInv inv σ ρG).1 ρG with
      | ok σ' ρ' =>
          rw [hB] at hnf
          obtain ⟨o1, h1, hO⟩ := hbody _ st ρG ρC hc1 hr (by rw [hB]; rfl)
          rw [hB] at hO
          obtain ⟨st1, ρC1, ho1, hc2, hr2⟩ := hO
          subst ho1
          obtain ⟨o, h2, hO2⟩ := ih σ' st1 ρ' ρC1 hc2 hr2 hnf
          exact ⟨o, Exec.forStep hcond rfl h1 rfl Exec.skip h2, hO2⟩
      | next hl σ' ρ' =>
          rw [hB] at hnf
          obtain ⟨o1, h1, hO⟩ := hbody _ st ρG ρC hc1 hr (by rw [hB]; rfl)
          rw [hB] at hO
          obtain ⟨st1, ρC1, ho1, hc2, hr2⟩ := hO
          subst ho1
          obtain ⟨o, h2, hO2⟩ := ih σ' st1 ρ' ρC1 hc2 hr2 hnf
          exact ⟨o, Exec.forStep hcond rfl h1 (by simp [COut.weiter]) Exec.skip h2, hO2⟩
      | leave hl σ' ρ' =>
          obtain ⟨o1, h1, hO⟩ := hbody _ st ρG ρC hc1 hr (by rw [hB]; rfl)
          rw [hB] at hO
          obtain ⟨st1, ρC1, ho1, hc2, hr2⟩ := hO
          subst ho1
          exact ⟨_, Exec.forExit hcond rfl h1 (by simp [COut.raus]), st1, ρC1, rfl, hc2, hr2⟩
      | zurueck σ' v =>
          obtain ⟨o1, h1, hO⟩ := hbody _ st ρG ρC hc1 hr (by rw [hB]; rfl)
          rw [hB] at hO
          obtain ⟨st1, cv, ho1, hc2, hrc⟩ := hO
          subst ho1
          exact ⟨_, Exec.forExit hcond rfl h1 rfl, st1, cv, rfl, hc2, hrc⟩
      | grund σ' r =>
          obtain ⟨o1, -, hO⟩ := hbody _ st ρG ρC hc1 hr (by rw [hB]; rfl)
          rw [hB] at hO
          exact hO.elim
      | logik e => rw [hB] at hnf; exact Bool.noConfusion hnf
      | hardware e => rw [hB] at hnf; exact Bool.noConfusion hnf

/-- F1. `forever m progress a { body }` against `for (;;) { body }`
    (`CS.loop`): `next` continues, `leave` ends the loop, `return` leaves
    it; the invariant is logic; the watchdog declaration has no run-time
    effect. -/
theorem scorr_forever (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
    (cbody : CS) (hbody : BlockSem X m' K body cbody) :
    StmtCorr X m K (Stmt.forever (l := l) a inv body) (CS.loop cbody m') := by
  intro σ st ρG ρC hc hr hnf
  exact forever_run X m m' K a inv body cbody hbody X.passes σ st ρG ρC hc hr hnf

end Forever

/-! ## 2. `_gabbro_sat_i` -/

/-- The body of the signed helper; parameters `a`, `b`, `lo`, `hi` are C
    locals 0 to 3, all `int64_t`. -/
def satIBody : CS :=
  .seq (.ite (.land (.cmp .gt CIT.i64 (.var 1) (.lit 0))
        (.cmp .gt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 3) (.var 1))))
      (.ret (some (CIT.i64.ty, .var 3))) .skip)
    (.seq (.ite (.land (.cmp .lt CIT.i64 (.var 1) (.lit 0))
          (.cmp .lt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 2) (.var 1))))
        (.ret (some (CIT.i64.ty, .var 2))) .skip)
      (.ret (some (CIT.i64.ty, .bin .add CIT.i64 (.var 0) (.var 1)))))

theorem i64_lo : CIT.i64.lo = -9223372036854775808 := by decide
theorem i64_hi : CIT.i64.hi = 9223372036854775807 := by decide

/-- S-I. The signed helper computes the clamp: for bounds and operands in
    `int64_t` with the operands inside `lo .. hi`, the run returns
    `max lo (min (a + b) hi)`, and no `int64_t` operation in it overflows
    (`hi - b` because `0 < b ≤ hi`, `lo - b` because `lo ≤ b < 0`,
    `a + b` because the guard failed). -/
theorem satI_run (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR) (st : CSt)
    (ρ : CLok) (a b lo hi : Int) (hlo : -9223372036854775808 ≤ lo) (hla : lo ≤ a) (hah : a ≤ hi)
    (hlb : lo ≤ b) (hbh : b ≤ hi) (hhi : hi ≤ 9223372036854775807) (ha : ρ 0 = .int a)
    (hb : ρ 1 = .int b) (hl : ρ 2 = .int lo) (hh : ρ 3 = .int hi) :
    Exec L orc fr CR XR satIBody st ρ (.ret st (some (.int (max lo (min (a + b) hi))))) := by
  have cv : ∀ v : Int, -9223372036854775808 ≤ v → v ≤ 9223372036854775807 →
      conv CIT.i64 v = some v := fun v h1 h2 => conv_id ⟨by rw [i64_lo]; exact h1, by rw [i64_hi]; exact h2⟩
  have retOk : ∀ v : Int, -9223372036854775808 ≤ v → v ≤ 9223372036854775807 →
      convV CIT.i64.ty (.int v) = some (.int v) := fun v h1 h2 => by
    show (match conv ⟨true, .w64⟩ v with | some b => some (CVal.int b) | none => none) = _
    rw [show (⟨true, .w64⟩ : CIT) = CIT.i64 from rfl, cv v h1 h2]
  have hb0 : ev L orc fr (.cmp .gt CIT.i64 (.var 1) (.lit 0)) st ρ =
      some (.int (b2i (decide (0 < b))), st) :=
    ev_cmp (ev_var hb) rfl (cv b (by omega) (by omega)) (cv 0 (by decide) (by decide))
  have hbl : ev L orc fr (.cmp .lt CIT.i64 (.var 1) (.lit 0)) st ρ =
      some (.int (b2i (decide (b < 0))), st) :=
    ev_cmp (ev_var hb) rfl (cv b (by omega) (by omega)) (cv 0 (by decide) (by decide))
  by_cases hpos : 0 < b
  · -- the first guard: `b > 0`, and `hi - b` cannot overflow
    have hsub : ev L orc fr (.bin .sub CIT.i64 (.var 3) (.var 1)) st ρ = some (.int (hi - b), st) :=
      ev_bin (ev_var hh) (ev_var hb) (cv hi (by omega) hhi) (cv b (by omega) (by omega))
        (cv (hi - b) (by omega) (by omega))
    have hcmp : ev L orc fr (.cmp .gt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 3) (.var 1))) st ρ =
        some (.int (b2i (decide (hi - b < a))), st) :=
      ev_cmp (ev_var ha) hsub (cv a (by omega) (by omega)) (cv (hi - b) (by omega) (by omega))
    rw [decide_eq_true hpos] at hb0
    have hg1 := ev_land_T hb0 rfl hcmp (truth_b2i _)
    by_cases hgt : hi - b < a
    · rw [show max lo (min (a + b) hi) = hi by omega]
      rw [decide_eq_true hgt] at hg1
      exact Exec.seqX (Exec.iteT hg1 rfl (Exec.retS (ev_var hh) (retOk hi (by omega) hhi))) rfl
    · rw [decide_eq_false hgt] at hg1
      rw [decide_eq_false (show ¬ (b < 0) by omega)] at hbl
      have hg2 := ev_land_F (r := .cmp .lt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 2) (.var 1))) hbl rfl
      have hadd : ev L orc fr (.bin .add CIT.i64 (.var 0) (.var 1)) st ρ = some (.int (a + b), st) :=
        ev_bin (ev_var ha) (ev_var hb) (cv a (by omega) (by omega)) (cv b (by omega) (by omega))
          (cv (a + b) (by omega) (by omega))
      rw [show max lo (min (a + b) hi) = a + b by omega]
      exact Exec.seqN (Exec.iteF hg1 rfl Exec.skip) (Exec.seqN (Exec.iteF hg2 rfl Exec.skip)
        (Exec.retS hadd (retOk _ (by omega) (by omega))))
  · rw [decide_eq_false hpos] at hb0
    have hg1 := ev_land_F (r := .cmp .gt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 3) (.var 1))) hb0 rfl
    by_cases hneg : b < 0
    · have hsub : ev L orc fr (.bin .sub CIT.i64 (.var 2) (.var 1)) st ρ = some (.int (lo - b), st) :=
        ev_bin (ev_var hl) (ev_var hb) (cv lo hlo (by omega)) (cv b (by omega) (by omega))
          (cv (lo - b) (by omega) (by omega))
      have hcmp : ev L orc fr (.cmp .lt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 2) (.var 1))) st ρ =
          some (.int (b2i (decide (a < lo - b))), st) :=
        ev_cmp (ev_var ha) hsub (cv a (by omega) (by omega)) (cv (lo - b) (by omega) (by omega))
      rw [decide_eq_true hneg] at hbl
      have hg2 := ev_land_T hbl rfl hcmp (truth_b2i _)
      by_cases hlt : a < lo - b
      · rw [show max lo (min (a + b) hi) = lo by omega]
        rw [decide_eq_true hlt] at hg2
        exact Exec.seqN (Exec.iteF hg1 rfl Exec.skip)
          (Exec.seqX (Exec.iteT hg2 rfl (Exec.retS (ev_var hl) (retOk lo hlo (by omega)))) rfl)
      · rw [decide_eq_false hlt] at hg2
        have hadd : ev L orc fr (.bin .add CIT.i64 (.var 0) (.var 1)) st ρ = some (.int (a + b), st) :=
          ev_bin (ev_var ha) (ev_var hb) (cv a (by omega) (by omega)) (cv b (by omega) (by omega))
            (cv (a + b) (by omega) (by omega))
        rw [show max lo (min (a + b) hi) = a + b by omega]
        exact Exec.seqN (Exec.iteF hg1 rfl Exec.skip) (Exec.seqN (Exec.iteF hg2 rfl Exec.skip)
          (Exec.retS hadd (retOk _ (by omega) (by omega))))
    · rw [decide_eq_false hneg] at hbl
      have hg2 := ev_land_F (r := .cmp .lt CIT.i64 (.var 0) (.bin .sub CIT.i64 (.var 2) (.var 1))) hbl rfl
      have hb00 : b = 0 := by omega
      have hadd : ev L orc fr (.bin .add CIT.i64 (.var 0) (.var 1)) st ρ = some (.int (a + b), st) :=
        ev_bin (ev_var ha) (ev_var hb) (cv a (by omega) (by omega)) (cv b (by omega) (by omega))
          (cv (a + b) (by omega) (by omega))
      rw [show max lo (min (a + b) hi) = a + b by omega]
      exact Exec.seqN (Exec.iteF hg1 rfl Exec.skip) (Exec.seqN (Exec.iteF hg2 rfl Exec.skip)
        (Exec.retS hadd (retOk _ (by omega) (by omega))))

/-- S-I against the model: the signed helper's answer is `Zahl.addS`. -/
theorem satI_zahl (L : CLayout) (orc : DevOrc) (fr : Nat) (CR XR : CCallR) (st : CSt)
    (ρ : CLok) {lo hi : Int} (hlo : -9223372036854775808 ≤ lo) (hle : lo ≤ hi)
    (hhi : hi ≤ 9223372036854775807) (a b : Zahl lo hi) (ha : ρ 0 = .int a.n)
    (hb : ρ 1 = .int b.n) (hl : ρ 2 = .int lo) (hh : ρ 3 = .int hi) :
    Exec L orc fr CR XR satIBody st ρ (.ret st (some (.int (Zahl.addS a b).n))) := by
  rw [Zahl.addS_n a b hle]
  exact satI_run L orc fr CR XR st ρ a.n b.n lo hi hlo a.lo_le a.le_hi b.lo_le b.le_hi hhi ha hb hl hh

/-! ## 3. `<<%` -/

section Schiebung

variable (X : TVCtx D) {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

theorem cWrap_mod (w : CWidth) (v : Int) : cWrap w v = v % 2 ^ w.bits := by
  show ((v % 2 ^ w.bits) + 2 ^ w.bits) % 2 ^ w.bits = _
  have e : (v % 2 ^ w.bits + 2 ^ w.bits) = v % 2 ^ w.bits + 1 * 2 ^ w.bits := by omega
  rw [e, Int.add_mul_emod_self_right, Int.emod_emod_of_dvd _ (Int.dvd_refl _)]

/-- E21 for `<<%`: `(ct)(((rt)(a) << (rt)(s)) & mask)`, unmasked at full
    storage width, computes `Zahl.shlW` -- the shift amount below the word
    (`s ≤ w < N ≤ bits`), the shift computed in the unsigned word `rt`
    (C11 6.5.7p3: the type of the promoted left operand). -/
theorem wrapC_shl (w : Nat) (rt ct : CIT) (hrt : rt.sgn = false) (hct : ct.sgn = false)
    (hN : w + 1 ≤ ct.bits) (hS : ct.bits ≤ rt.bits) (masked : Bool)
    (hmask : masked = false → w + 1 = ct.bits) {ca cb : CX}
    {a : Expr D Γ Λ (.int 0 (2 ^ (w + 1) - 1))} {s : Expr D Γ Λ (.int 0 (w : Int))}
    (ha : ExprCorr X K ca a) (hs : ExprCorr X K cb s) (σ : World D) (st : CSt) (ρG : Env D Γ)
    (ρC : CLok) (hc : corrW X.EL σ st) (hr : EnvRel X.EL K ρG ρC) :
    ∃ st', ev X.EL.lay X.orc X.fr (wrapC .shl rt ct masked (w + 1) ca cb) st ρC =
      some (.int (Zahl.shlW w (eval σ a σ ρG) (eval σ s σ ρG)).n, st') := by
  obtain ⟨st1, h1, hc1⟩ := ha.runI X K hc hr
  obtain ⟨st2, h2, -⟩ := hs.runI X K hc1 hr
  have ra := (eval σ a σ ρG).lo_le
  have ra' := (eval σ a σ ρG).le_hi
  have rs := (eval σ s σ ρG).lo_le
  have rs' := (eval σ s σ ρG).le_hi
  have pN := two_pow_le_two_pow hN
  have pS := two_pow_le_two_pow hS
  have hlo := CIT.lo_u hrt
  have hhi := CIT.hi_u hrt
  have hpR := two_pow_pos' rt.bits
  have hpN := two_pow_pos' (w + 1)
  have hwb : (w : Int) < rt.bits := by
    have : w + 1 ≤ rt.bits := Nat.le_trans hN hS
    omega
  have hw2 : (2 : Int) ^ w < 2 ^ rt.bits := by
    have := two_pow_le_two_pow (show w + 1 ≤ rt.bits from Nat.le_trans hN hS)
    have e : (2 : Int) ^ (w + 1) = 2 * 2 ^ w := by rw [Int.pow_succ]; omega
    have := two_pow_pos' w
    omega
  have ca' : conv rt (eval σ a σ ρG).n = some (eval σ a σ ρG).n := conv_id ⟨by omega, by omega⟩
  have cs' : conv rt (eval σ s σ ρG).n = some (eval σ s σ ρG).n := conv_id ⟨by omega, by
    have : (2 : Int) ^ rt.bits - 1 ≥ rt.bits := by
      have := Nat.lt_two_pow_self (n := rt.bits)
      have e : ((2 ^ rt.bits : Nat) : Int) = (2 : Int) ^ rt.bits := by simp
      omega
    omega⟩
  have hcore : ev X.EL.lay X.orc X.fr (wrapCore .shl rt ca cb) st ρC =
      some (.int ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits), st2) := by
    have e1 := ev_cast rt h1 ca'
    have e2 := ev_cast rt h2 cs'
    have hv : cArith .shl rt (eval σ a σ ρG).n (eval σ s σ ρG).n =
        some ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits) := by
      show (if 0 ≤ (eval σ s σ ρG).n ∧ (eval σ s σ ρG).n < (rt.bits : Int) ∧ 0 ≤ (eval σ a σ ρG).n then
        (if rt.sgn = true then _ else some (cWrap rt.w _)) else none) = _
      rw [if_pos ⟨rs, by omega, ra⟩, if_neg (by rw [hrt]; decide), cWrap_mod]
      rfl
    exact ev_bin e1 e2 ca' cs' hv
  have hdvN : (2 : Int) ^ (w + 1) ∣ 2 ^ rt.bits := two_pow_dvd_two_pow (Nat.le_trans hN hS)
  have hdvS : (2 : Int) ^ ct.bits ∣ 2 ^ rt.bits := two_pow_dvd_two_pow hS
  show ∃ st', _ = some (CVal.int ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ (w + 1)), st')
  cases masked with
  | false =>
      have e := hmask rfl
      refine ⟨st2, ?_⟩
      have c3 := conv_u_mod hct ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits)
      rw [Int.emod_emod_of_dvd _ hdvS, ← e] at c3
      exact ev_cast ct hcore c3
  | true =>
      refine ⟨st2, ?_⟩
      have hm0 : 0 ≤ (eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits :=
        Int.emod_nonneg _ (by omega)
      have hm1 : (eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits < 2 ^ rt.bits :=
        Int.emod_lt_of_pos _ hpR
      have cm : conv rt ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits) =
          some ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits) :=
        conv_id ⟨by omega, by omega⟩
      have ck : conv rt (2 ^ (w + 1) - 1) = some (2 ^ (w + 1) - 1) := conv_id ⟨by omega, by omega⟩
      have hand : ((((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits).toNat &&&
          ((2 : Int) ^ (w + 1) - 1).toNat : Nat) : Int) =
          (eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ (w + 1) := by
        have eN : ((2 : Int) ^ (w + 1) - 1).toNat = 2 ^ (w + 1) - 1 := by
          have : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by simp
          omega
        rw [eN, Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod, Int.toNat_of_nonneg hm0,
          Int.natCast_pow]
        show _ % 2 ^ rt.bits % (2 : Int) ^ (w + 1) = _
        exact Int.emod_emod_of_dvd _ hdvN
      have hb2 : cArith .band rt ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ rt.bits)
          (2 ^ (w + 1) - 1) = some ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ (w + 1)) := by
        show (if 0 ≤ _ ∧ 0 ≤ (2 : Int) ^ (w + 1) - 1 then some _ else none) = _
        rw [if_pos ⟨hm0, by omega⟩, hand]
      have hmv : ev X.EL.lay X.orc X.fr
          (.bin .band rt (wrapCore .shl rt ca cb) (.lit (2 ^ (w + 1) - 1))) st ρC =
          some (.int ((eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ (w + 1)), st2) :=
        ev_bin hcore rfl cm ck hb2
      have hlt : 0 ≤ (eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ (w + 1) ∧
          (eval σ a σ ρG).n * 2 ^ (eval σ s σ ρG).n.toNat % 2 ^ (w + 1) < 2 ^ (w + 1) :=
        ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hpN⟩
      have hcl := CIT.lo_u hct
      have hch := CIT.hi_u hct
      exact ev_cast ct hmv (conv_id ⟨by omega, by omega⟩)

end Schiebung

#print axioms forever_run
#print axioms scorr_forever
#print axioms satI_run
#print axioms satI_zahl
#print axioms wrapC_shl

end Gabbro.Grammatik
