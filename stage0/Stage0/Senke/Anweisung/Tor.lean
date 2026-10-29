/-
  File:      stage0/Stage0/Senke/Anweisung/Tor.lean
  Subject:   The named assumption at a gate (`TorOK`) and the steps of a gate's code: the arguments into the request
             block (`lowR_ok`), zeros into the unused registers (`zero_ok`), the kernel's answer (`sys_step`).

  `TorOK L O` is the operating system doing what it should (Simon, 2026-10-29: an allowed assumption): asked a
  bound gate's request -- the number, the arguments' words in the first argument registers, zero in the others --
  in a memory that holds a world `σ`, the kernel can answer with a word and a memory that holds the oracle's world,
  having changed nothing but the world's bytes, and the oracle's raw answer is the kernel's word as the gate's
  binding reads it (`rohW`, what stage 0's interpreter does, `Stage0/Tor/Ausfuehren.lean`).
-/
import Stage0.Senke.Anweisung.Schleife
import Stage0.Senke.Anweisung.Schreiben

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- The kernel changes nothing but the world's bytes. -/
def KernW (L : Lay D) (m m' : Runner.Mem) : Prop :=
  m'.rd = m.rd ∧ m'.wr = m.wr ∧ ∀ y : Runner.W, ¬ (L.lo ≤ y.toNat ∧ y.toNat < L.hi) → m'.b y = m.b y

/-- The six argument registers of a request, by number. -/
def reqArg (q : Runner.Req) : Nat → Runner.W
  | 0 => q.a1
  | 1 => q.a2
  | 2 => q.a3
  | 3 => q.a4
  | 4 => q.a5
  | 5 => q.a6
  | _ => 0

/-- The words `f 0, f 1, …` are the arguments `ρ`. -/
def ArgsW (f : Nat → Runner.W) : {τs : List Ty} → Env D τs → Prop
  | [], .nil => True
  | τ :: _, .cons v ρ => Enc τ v (f 0) ∧ ArgsW (fun j => f (j + 1)) ρ

/-- The kernel's word as the oracle's raw answer, for a gate with `n` reasons: the signed word; with reasons, a
    listed `-errno` is its case `i + 1`, another error the word of no answer, a value `v` is `v * (n + 1)`. -/
def rohW (b : TorB) (n : Nat) (w : Runner.W) : Int :=
  if n = 0 then w.toInt
  else if -4095 ≤ w.toInt ∧ w.toInt ≤ -1 then
    match b.fehler.find? (fun e => e.1 == w.toInt) with
    | some (_, i) => (i : Int) + 1
    | none => -((n : Int) + 1)
  else w.toInt * ((n : Int) + 1)

/-- **The named assumption at the gates**: the kernel answers a bound gate's request as the oracle says. -/
class TorOK (L : Lay D) (O : Orakel D) : Prop where
  ans : ∀ (a : D.Ax) (b : TorB), L.tor a = some b → torGut b (D.aparams a).length = true →
    ∀ (σ : World D) (ρ : Env D (D.aparams a)) (q : Runner.Req) (m : Runner.Mem),
    q.nr = BitVec.ofNat 64 b.nr → ArgsW (reqArg q) ρ → (∀ i, (D.aparams a).length ≤ i → i < 6 → reqArg q i = 0) →
    WeltAt m L σ →
    ∃ w x m', Kern.ans q m (some (w, x)) m' ∧ KernW L m m' ∧ WeltAt m' L (O.wirkt a σ ρ).1 ∧
      (O.wirkt a σ ρ).2 = rohW b (D.agruende a) w

/-- **Witness** (the assumption is not empty): a kernel that may give any answer, and an oracle that leaves the
    world and answers 0, meet it for every layout. -/
theorem torOK_zeuge (L : Lay D) (O : Orakel D) (hO : ∀ a σ ρ, O.wirkt a σ ρ = (σ, 0)) :
    @TorOK ⟨fun _ _ _ _ => True⟩ D L O := by
  letI : Kern := ⟨fun _ _ _ _ => True⟩
  refine ⟨fun a b _ _ σ ρ q m _ _ _ hW => ⟨0, 0, m, trivial, ⟨rfl, rfl, fun _ _ => rfl⟩, ?_, ?_⟩⟩
  · rw [hO]; exact hW
  · rw [hO]; simp [rohW]

theorem argsW_congr {f g : Nat → Runner.W} : {τs : List Ty} → (ρ : Env D τs) →
    (∀ j, j < τs.length → f j = g j) → ArgsW f ρ → ArgsW g ρ
  | [], .nil, _, _ => trivial
  | _ :: τs, .cons _ ρ, he, h => by
    simp only [ArgsW] at h ⊢
    exact ⟨by rw [← he 0 (by simp)]; exact h.1, argsW_congr ρ (fun j hj => he (j + 1) (by simp; omega)) h.2⟩

/-- The kernel's change lies in the frame's slots from `Ks`, where the world is. -/
theorem kernW_agree {L : Lay D} {fp : Runner.W} {Ks K : Nat} {m m' : Runner.Mem} (hW : WIn L fp Ks K)
    (h : KernW L m m') : Agree fp Ks K m m' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun x hx => h3 x fun ⟨a, b⟩ => hx ⟨?_, ?_⟩⟩
  · have := hW.lo; omega
  · have := hW.hi; omega

/-- The word of slot `i`, zero where none is read. -/
def rdW (m : Runner.Mem) (fp : Runner.W) (i : Nat) : Runner.W := (m.rd64 (slot fp (BitVec.ofNat 64 i))).getD 0

theorem rd64_rdW {m : Runner.Mem} {fp : Runner.W} {K i : Nat} (hF : FrameOK m fp K) (hi : i < K) :
    m.rd64 (slot fp (BitVec.ofNat 64 i)) = some (rdW m fp i) := by
  simp only [rdW, Runner.Mem.rd64, hF.rd i hi, ↓reduceIte, Option.getD_some]

theorem rdW_of {m : Runner.Mem} {fp w : Runner.W} {i : Nat} (h : m.rd64 (slot fp (BitVec.ofNat 64 i)) = some w) :
    rdW m fp i = w := by
  simp only [rdW, h, Option.getD_some]

theorem slot_succ (fp : Runner.W) (s i : Nat) :
    slot fp (BitVec.ofNat 64 s) + BitVec.ofNat 64 (8 * i) = slot fp (BitVec.ofNat 64 (s + i)) := slot_plus fp s i

/-- `sys s s`: the request from the slots `s .. s+6`, the kernel's answer `w` into slot `s`. -/
theorem sys_step {m m' : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {q : Runner.Req} {w x : Runner.W}
    (hc : CodeAt m pc [ci 23 s s 0]) (hF : FrameOK m fp K) (hs : s + 7 ≤ K) (hK : K < 2 ^ 31)
    (h0 : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some q.nr)
    (hr : ∀ i, i < 6 → m.rd64 (slot fp (BitVec.ofNat 64 (s + 1 + i))) = some (reqArg q i))
    (hk : Kern.ans q m (some (w, x)) m') (hwr : m'.wr = m.wr) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci 23 s s 0].length), fp⟩
      (write m' (slot fp (BitVec.ofNat 64 s)) 8 w.toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  have e : ∀ i, i < 6 → slot fp (BitVec.ofNat 64 s) + BitVec.ofNat 64 (8 * (i + 1)) =
      slot fp (BitVec.ofNat 64 (s + 1 + i)) := fun i _ => by
    rw [slot_succ]; congr 2; omega
  have r1 := hr 0 (by decide); rw [← e 0 (by decide)] at r1
  have r2 := hr 1 (by decide); rw [← e 1 (by decide)] at r2
  have r3 := hr 2 (by decide); rw [← e 2 (by decide)] at r3
  have r4 := hr 3 (by decide); rw [← e 3 (by decide)] at r4
  have r5 := hr 4 (by decide); rw [← e 4 (by decide)] at r5
  have r6 := hr 5 (by decide); rw [← e 5 (by decide)] at r6
  refine star_ins hc (by simp [ci]) ?_
  simp only [ci, op]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  simp only [ld]
  refine run_rd64 h0 (run_rd64 r1 (run_rd64 r2 (run_rd64 r3 (run_rd64 r4 (run_rd64 r5 (run_rd64 r6 ?_))))))
  refine Run.sys (a := some (w, x)) (m' := m') hk ?_
  simp only [Runner.opt]
  exact run_wr64 (wr64_some (by rw [hwr]; exact hF.wr s (by omega)))

theorem zeroC_len : (d k : Nat) → (zeroC d k).length = k
  | _, 0 => rfl
  | d, k + 1 => by simp only [zeroC, List.length_cons, zeroC_len (d + 1) k]

/-- Zero into the `k` slots from `d`, nothing else changed. -/
theorem zero_ok {fp : Runner.W} {K : Nat} (hK : K < 2 ^ 31) : (k d : Nat) → (m : Runner.Mem) → (pc : Runner.W) →
    CodeAt m pc (zeroC d k) → CodeFar pc k fp K → FrameOK m fp K → d + k ≤ K →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * k), fp⟩ m' ∧ Agree fp d K m m' ∧
      ∀ i, i < k → m'.rd64 (slot fp (BitVec.ofNat 64 (d + i))) = some 0
  | 0, d, m, pc, _, _, _, _ => ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, fun _ h => absurd h (by omega)⟩
  | k + 1, d, m, pc, hc, hf, hF, hd => by
    have hroom := hF.room
    have hc' : CodeAt m pc ([ci 1 d 0 0] ++ zeroC (d + 1) k) := hc
    have s1 := const_step (k := 0) (codeAt_left hc') hF (by omega) hK (by decide)
    let m1 := write m (slot fp (BitVec.ofNat 64 d)) 8 (BitVec.ofInt 64 0).toNat
    have a1 : Agree fp d K m m1 := agree_write hroom (Nat.le_refl _) (by omega) _
    have hf1 := codeFar_right (n := 1) (k := k) (by simpa [Nat.add_comm] using hf)
    have hc1 := (codeAt_right hc').agree a1 (by simpa [zeroC_len] using hf1)
    simp only [List.length_singleton] at hc1
    obtain ⟨m2, s2, a2, hz⟩ := zero_ok hK k (d + 1) m1 _ hc1 hf1 (hF.agree a1) (by omega)
    have hr1 : m1.rd64 (slot fp (BitVec.ofNat 64 d)) = some (BitVec.ofInt 64 0) :=
      rd64_write_same (hF.rd d (by omega))
    refine ⟨m2, s1.trans (star_cast s2 (by simp) (by rw [step_eq pc (x := 1) (y := k) (z := k + 1) (by omega)])),
      a1.trans (a2.mono (by omega)), fun i hi => ?_⟩
    rcases i with _ | i
    · rw [Nat.add_zero, agree_rd_low a2 hroom (by omega) (by omega), hr1]; rfl
    · have := hz i (by omega); rwa [show d + 1 + i = d + (i + 1) by omega] at this

/-- The arguments of a gate into the slots from `d`, in order; nothing below `d` changed. -/
theorem lowR_ok {Λ : List (Res D)} {L : Lay D} {fp : Runner.W} {K : Nat} {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (hWL : ∀ m, W m → WeltAt m L σ) :
    {Γ : Ctx} → {τs : List Ty} → (args : Args D Γ Λ τs) → (d : Nat) → (c : List II) → (top : Nat) →
    lowR L args d = some (c, top) → top ≤ K → d + τs.length ≤ K →
    ∀ (m : Runner.Mem) (pc : Runner.W) (ρ : Env D Γ), Pre m pc fp K d c ρ W →
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * c.length), fp⟩ m' ∧ Agree fp d K m m' ∧
      ArgsW (fun j => rdW m' fp (d + j)) (evalArgs σ₀ args σ ρ)
  | _, _, .nil, d, c, top, h, _, _, m, pc, ρ, _ => by
    simp only [lowR, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, trivial⟩
  | _, _ :: τs, .cons e rest, d, c, top, h, hK, hL, m, pc, ρ, hp => by
    simp only [lowR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.length_cons] at hL
    have hroom := hp.frame.room
    obtain ⟨m1, s1, a1, w, hw, hen⟩ := lowE_ok (fp := fp) (K := K) σ₀ σ hWL e d ce te he (by omega) m pc ρ hp.left
    have hp1 := (hp.next a1 (Nat.le_refl _) (by omega)).up (d' := d + 1) (by omega)
    obtain ⟨m2, s2, a2, hA⟩ := lowR_ok σ₀ σ hWL rest (d + 1) cr tr hr (by omega) (by omega) m1 _ ρ hp1
    refine ⟨m2, s1.trans (by rw [pc_add1]; exact s2), a1.trans (a2.mono (by omega)), ?_⟩
    simp only [evalArgs, ArgsW]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_zero, rdW_of (by rw [agree_rd_low a2 hroom (by omega) (by omega)]; exact hw)]; exact hen
    · refine argsW_congr _ (fun j _ => ?_) hA
      simp only [show d + 1 + j = d + (j + 1) by omega]

end Gabbro.Stage0.Senke
