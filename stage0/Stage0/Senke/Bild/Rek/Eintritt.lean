/-
  File:      stage0/Stage0/Senke/Bild/Rek/Eintritt.lean
  Subject:   **Boundaries inside a callee, the image side** (package P4 of the closed calls of the image theorem,
             part 2). From a boundary of a caller's body in front of a plain call `g(args); rest`, the image runs the
             call's argument code (`lowA_ok`) and the call tail up to the callee's first instruction
             (`callC_eintritt`: the first half of `callC_ok`, with `call_eintritt` for `call_ok`), then the callee's
             prologue (`prolog_rand`) to the callee's first body boundary.

             The caller's frame is a `rumpfRahmen` at depth `k = j + 1` (callees run as `rufAt k`, depth word `k`);
             the callee's frame is a `rumpfRahmen` at depth `j` (its callees run as `rufAt j`) in the slots from
             `F = frei Γ reserved` of the caller's frame on. Both `FunSpec` instances are explicit: the caller's
             `BodyFrame.Ok` carries `FunSpec … (rufAt k)`, the callee's (from `prolog_rand`) `FunSpec … (rufAt j)`.
             The frame capacities nest: the caller's boundary has `top + (k + 1) * Lm ≤ Ks` with
             `F + FB + |params g| + 1 ≤ top`, so the callee's `(j + 1 + 1) * Lm ≤ Ks - F` (`prolog_rand`'s `hc`) is
             pure arithmetic -- no capacity premise is added.

             The callee's `requires` holds at its entry because the call ends normally under `rufAt k`
             (`rufAt_ok_req`: a failing entry contract is a `vorbedingung` outcome). The callee's body boundary is
             stated at the world the handler runs the body in (`rufWelt`: the reads of the arguments and of
             `requires`), which the image holds in memory exactly as the entry world (`BodyFrame.randIR_lese`).

             `BildCodes` names the image facts both prologues need (the `lowFun` codes and their bounds), which the
             emitted image supplies (`Emitted.bild_anfang_codes`, `Rek/Emitted.lean`).
-/
module
public import Stage0.Senke.Bild.Rek.Maschine
public import Stage0.Senke.Bild.Prolog
public import Stage0.Senke.Bild.Eintritt
public import Stage0.Senke.Rueckkehr.Call
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The image facts every prologue needs -/

/-- **The codes of a laid-out image**: the layout's function addresses are `A`, every function's lowering is `C g`
    with a frame top at most `Lm`, and addresses and code lengths fit the immediates (the premises of `prolog_rand`
    and `lowFun_spec`). -/
structure BildCodes (Y : Lay D) (P : Programm D) (passes : Nat) (A : D.Fn → Nat) (C : D.Fn → List II)
    (Lm : Nat) : Prop where
  fa : Y.fa = A
  low : ∀ g, ∃ top, lowFun passes P A Y g = some (C g, top) ∧ top ≤ Lm
  addr : ∀ g, A g < 2 ^ 31
  len : ∀ g, 16 * (C g).length < 2 ^ 31

/-! ## The callee's entry contract -/

/-- A call above depth `0` that returns normally had its entry contract true (`rufAt_vorbed`). -/
theorem rufAt_ok_req {P : Programm D} {O : Orakel D} {passes n : Nat} {g : D.Fn} {σ σ' : World D}
    {ρ : Env D (D.params g)} {v : ErgVal D (D.erg g)} (h : rufAt P O passes (n + 1) g σ ρ = .ok σ' v) :
    ReqAmEintritt P g σ ρ :=
  Classical.byContradiction fun hn => by
    rw [rufAt_vorbed P O passes n g σ ρ hn] at h
    cases h

/-- A plain call that ends normally under `rufAt (j + 1)` had the callee's entry contract true at the world after
    the argument reads. -/
theorem ruf_ok_req {P : Programm D} {O : Orakel D} {passes j : Nat} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)} {hp : RufPasst D V (D.signatur g) Λ}
    {hr : D.gruende g = 0} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (hex : execStmt O passes (rufAt P O passes (j + 1)) (.call g args hp hr : Stmt D V l Γ Λ (nach D g Λ)) σ ρ =
      .ok σ1 ρ1) :
    ReqAmEintritt P g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) := by
  simp only [execStmt] at hex
  split at hex
  · rename_i σ2 v hR2
    exact rufAt_ok_req hR2
  · exact (Fin.cast hr ‹_›).elim0
  · cases hex
  · cases hex

variable [Kern]

/-! ## The image at a boundary holds every read of its world -/

/-- The image side of a boundary sees only the memory of its world: reads (`World.lese`) keep `RandIR`. -/
theorem BodyFrame.randIR_lese {B : BodyFrame D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {eb : Endblock D (vertragVon D B.f) l Γ Λ} {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandIR eb pc m σ ρ) (Λ0 : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    B.RandIR eb pc m (σ.lese Λ0 os) ρ := by
  obtain ⟨c, top, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨c, top, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## The call site up to the callee's first instruction -/

/-- **A call, up to the callee's entry**: the arguments into the callee frame at slot `F = frei Γ reserved`, then the
    call tail; the image stands at the callee's first instruction with every premise of `FunSpec.run` (the first half
    of `callC_ok`, with `call_eintritt`). -/
theorem callC_eintritt {L : Lay D} {A : D.Fn → Nat} {C : D.Fn → List II} {reserved : Nat} {dv : Runner.W}
    {Λ : List (Res D)} {Γ : Ctx} {g : D.Fn} (hA : A g < 2 ^ 31) (args : Args D Γ Λ (D.params g))
    (σ : World D) {ca : List II} {ta : Nat} {m : Runner.Mem} {pc fp : Runner.W} {K Ks : Nat} {ρ : Env D Γ}
    (hca : lowA L (reserved := reserved) args (frei Γ reserved + FB) = some (ca, ta))
    (htop : callTop g (frei Γ reserved) ta ≤ Ks)
    (hp : PreS L m pc fp K (frei Γ reserved) (callC A g (frei Γ reserved) ca) ρ reserved) {H : List D.Lock}
    (hu : Umf L A C dv m fp Ks K H) (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨BitVec.ofNat 64 (A g), slot fp (BitVec.ofNat 64 (frei Γ reserved))⟩ m' ∧
      Agree fp (frei Γ reserved) K m m' ∧
      WIn L (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (Ks - frei Γ reserved) (K - frei Γ reserved) ∧
      K - frei Γ reserved < 2 ^ 31 ∧
      FrameOK m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved) ∧
      PCode m' A C (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (K - frei Γ reserved) ∧
      m'.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (BitVec.ofNat 64 0)) =
        some (pc + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * 3) + 16) ∧
      m'.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (BitVec.ofNat 64 1)) = some fp ∧
      m'.rd64 (slot (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (BitVec.ofNat 64 2)) = some dv ∧
      EnvAt L m' (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (evalArgs σ args σ ρ) ∧ WeltAt m' L σ ∧
      TicketSync m' L (slot fp (BitVec.ofNat 64 (frei Γ reserved))) (Ks - frei Γ reserved) H := by
  simp only [callTop] at htop
  have hFB : FB ≤ frei Γ reserved := by simp only [frei]; omega
  have hks := hW.ks
  have hp' : PreS L m pc fp K (frei Γ reserved + FB) (ca ++ callTail A g (frei Γ reserved)) ρ reserved :=
    hp.up (by omega)
  have hpw := PreS.welt hp'.left hks hWa hW.lay (by have := hW.lo; omega)
  obtain ⟨m1, s1, a1s, e1⟩ := lowA_ok (same := rfl) (reserved := reserved) (F := frei Γ reserved) σ σ
    (fun _ h => h) hW.lay args ca ta hca (by omega) (by omega) m pc ρ hpw
  have a1 := Agree.widen a1s hks
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have hp1 := hp'.next a1 (Nat.le_refl _) (by omega)
  have hl4 : (callTail A g (frei Γ reserved)).length = 4 := rfl
  have hu1 := hu.agree a1 hp.frame (by omega)
  obtain ⟨m2, s2, a2, hW2, hK2, hF2, hP2, g0, g1, g2, gE, gW, gy⟩ :=
    call_eintritt (σ := σ) hp1.code (by rw [← hl4]; exact hp1.far) hp1.frame hp.small hFB (by omega)
      hA hu1.code hu1.depth e1 hW hWa1 hu1.sync
  exact ⟨m2, s1.trans s2, (a1.mono (by omega)).trans a2, hW2, hK2, hF2, hP2, g0, g1, g2, gE, gW, gy⟩

/-! ## From a caller's boundary to the callee's first body boundary, the image side -/

/-- **Into the callee, the image side**: from the boundary of a caller's body (frame `rumpfRahmen` at depth
    `k = j + 1`) in front of a plain call `g(args); rest` that ends normally under the caller's handler `rufAt k`,
    the image runs the arguments, the call tail and the callee's prologue to the callee's first body boundary:
    `RandIR` of the whole body `P.rumpf g` in the callee's frame `rumpfRahmen` at depth `j` (callees `rufAt j`),
    which satisfies `BodyFrame.Ok`, at the handler's body world `rufWelt` and the callee's parameters `rufEnv`. -/
theorem randIR_ruf_eintritt {Y : Lay D} {O : Orakel D} [TorOK Y O] [SichtOK O] {passes : Nat}
    {P : Programm D} {A : D.Fn → Nat} {C : D.Fn → List II} {Lm : Nat} (hc : BildCodes Y P passes A C Lm)
    {k j : Nat} (hkj : k = j + 1) (hk64 : k < 2 ^ 64) {f : D.Fn} {fp : Runner.W} {K Ks : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {H : List D.Lock} {ens : List II × Nat}
    (hB : (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens).Ok)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {pc : Runner.W} {m : Runner.Mem} {σ σ1 : World D}
    {ρ ρ1 : Env D Γ}
    (h : (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens).RandIR
      (.cons (.call g args hp hr) rest) pc m σ ρ)
    (hex : execStmt O passes (rufAt P O passes k)
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ1 ρ1) :
    ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (pcI : Runner.W) (mI : Runner.Mem),
      Star ⟨pc, fp⟩ m ⟨pcI, fpc⟩ mI ∧
      (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) H
        ensc).Ok ∧
      (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) H
        ensc).RandIR (P.rumpf g) pcI mI (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) := by
  subst hkj
  have hreq : ReqAmEintritt P g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) := ruf_ok_req hex
  obtain ⟨c, top, hl, hK, _, hpre, _, hu, _, hWa, _, hH⟩ := h
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨cr, tr⟩, _, ⟨cs, ts⟩, hs1, hcc⟩ := hl
  simp only [Prod.mk.injEq] at hcc
  obtain ⟨rfl, rfl⟩ := hcc
  simp only [lowS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hs1
  obtain ⟨⟨ca, ta⟩, hca, hcs⟩ := hs1
  simp only [Prod.mk.injEq] at hcs
  obtain ⟨rfl, rfl⟩ := hcs
  have hW := hB.win
  -- the frame capacities nest: the callee's frame fits behind the call's slot `F`
  have hK' : max (callTop g (frei Γ (functionFrame P f).bodyReserved) ta) tr + (j + 1 + 1) * Lm ≤ Ks := hK
  simp only [callTop] at hK'
  have hTop : callTop g (frei Γ (functionFrame P f).bodyReserved) ta ≤ Ks := by
    simp only [callTop]
    omega
  have hcap : (j + 1 + 1) * Lm ≤ Ks - frei Γ (functionFrame P f).bodyReserved := by
    omega
  obtain ⟨m2, s2, _, hW2, hK2, hF2, hP2, g0, g1, g2, gE, gW, gy⟩ :=
    callC_eintritt (L := Y) (hc.addr g) args (σ.lese Λ args.orte) hca hTop hpre.left hu hW hWa
  obtain ⟨ensc, pcI, mI, sP, hOk, hRand⟩ :=
    prolog_rand (Y := Y) (P := P) (O := O) (passes := passes) (A := A) (C := C) (Lm := Lm) hc.fa hc.low
      hc.addr hc.len (k := j) hk64 hcap hW2 hK2 hF2 hP2 g0 g1 g2 gE gW gy
      (HeldIn.ruf (V := vertragVon D f) hH hp) hreq
  exact ⟨_, _, _, _, ensc, pcI, mI, s2.trans sP, hOk,
    BodyFrame.randIR_lese hRand (Signatur.anfang D (D.signatur g)) (P.requires g).orte⟩

#print axioms randIR_ruf_eintritt

end Gabbro.Stage0.Senke.BildLauf
