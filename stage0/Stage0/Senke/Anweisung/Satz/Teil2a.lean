module

public import Stage0.Senke.Anweisung.Schreiben
public import Stage0.Senke.Welt.Spans.CellStore
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Sperre.Ticket.Satz
public import Stage0.Senke.Sperre.OhneRet
public import Stage0.Senke.Anweisung.Faelle.Gleit.Narrow
public import Stage0.Senke.Anweisung.Faelle.Gleit.Literal
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Wahl
public import Stage0.Senke.Anweisung.Bindung.Option
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Why
public import Stage0.Senke.Anweisung.Faelle.CallElse
public import Stage0.Senke.Anweisung.Faelle.Fnptr
public import Stage0.Senke.Anweisung.Bytes.Shift
public import Stage0.Senke.Anweisung.Bytes.Put
public import Stage0.Senke.Anweisung.Faelle.Schreiben
public import Stage0.Senke.Anweisung.Faelle.Speicher
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Traversal
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Retry
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Runtime.Teil2
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Emission
public import Stage0.Senke.Anweisung.Faelle.Bloecke
public import Stage0.Senke.Anweisung.Faelle.BlockRuf
public import Stage0.Senke.Anweisung.Faelle.Ende
public import Stage0.Senke.Anweisung.Faelle.Ends.EndRuf
public import Stage0.Senke.Anweisung.Faelle.Ends.EndWahl
public import Stage0.Senke.Anweisung.Faelle.Ends.EndFehler
public import Stage0.Senke.Anweisung.Faelle.Ends.EndAtomar
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Check
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.NarrowCases
public import Stage0.Senke.Anweisung.Faelle.BlockFehler
public import Stage0.Senke.Anweisung.Satz.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable [Kern]
variable {D : Deklaration} {L : Lay D} {V : Vertrag D}
variable {H : List D.Lock}

set_option linter.unusedSectionVars false in
theorem lowS_ok_forever {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (inv)
    (body)
    (c : List II)
    (top : Nat)
    (h : lowS (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.forever a inv body : Stmt D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : FB ≤ lo)
    (hlo2 : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K H)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hw : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (hH : HeldIn H Λ (vertragVon D f).boden)
    (ih_lowB_ok_body : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, HeldIn H (blockAnf body) (vertragVon D f).boden → ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex body = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K H → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R body σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execStmt O passes R (.forever a inv body : Stmt D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  dsimp only [lowS, ← hlo0, resultWords_vertragVon] at h
  split at h
  · rename_i allowed
    obtain ⟨cc, hcc, emitted⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cb, tb, hcb, rfl, htc, htb, hcounter, hone, hscratch⟩ := foreverC_actual emitted
    have bodyRuns : ∀ {pr ex}, BlockCase L O passes R A C dv cap P f fp K Ks lo
        rp cfp σ0 ρ0 cens tens pr ex H body reserved := fun {pr ex} =>
      ih_lowB_ok_body (pr := pr) (ex := ex) hS hA hlo0 hens hH
    have fuel := foreverC_budget emitted
    have pairStep : (counterPair reserved (counterDepthB body)).2 =
        (counterPair reserved (counterDepthB body)).1 + 1 := rfl
    have room : frei Γ reserved + 8 ≤ K := by have := hW.ks; omega
    obtain ⟨m1, initRun, initFrame, entry, surrounds, snapshot, world, keeps, count, unit⟩ :=
      forever_initialize_entry (lo := lo) (pr := pr) hW hp hu hk hw
        (by omega) (by rw [hlo0]; exact allowed.1) (by omega) (by omega) allowed.2.1
        (by omega) (by omega) fuel.1 (by
          intro j hj
          have member := hpr j hj
          exact ⟨by omega, fun eq => allowed.2.2.1 (eq ▸ hj),
            fun eq => allowed.2.2.2 (eq ▸ hj)⟩)
    let control := foreverCounter (counterPair reserved (counterDepthB body)).1
      (counterPair reserved (counterDepthB body)).2 (16 * (cc.1.length + cb.length + 8)) ++
      (cc.1 ++ [ci 19 (frei Γ reserved) (16 * (cb.length + 2)) 0] ++ cb ++
        [ci 18 64 0 0] ++ stopC 104 (frei Γ reserved))
    have controlLength : control.length = cc.1.length + cb.length + 7 := by
      simp [control, foreverCounter, stopC, sysC]
      omega
    have emittedCode : CodeAt m1 (pc + 32)
        (control ++ ([ci 18 (-(16 * (cc.1.length + cb.length + 7 : Nat) : Int)) 0 0] ++
          stopC 111 (frei Γ reserved))) := by
      simpa [control, foreverCounter, List.append_assoc] using entry.code
    have emittedFar : CodeFar (pc + 32) (control.length + 4) fp K := by
      simpa [control, foreverCounter, stopC, sysC, Nat.add_assoc] using entry.far
    have backCode := codeAt_right emittedCode
    have backFar := codeFar_left (n := 1) (k := 3)
      (codeFar_right (n := control.length) (k := 4) emittedFar)
    have budgetCode := codeAt_right backCode
    have budgetFar := codeFar_right (n := 1) (k := 3)
      (codeFar_right (n := control.length) (k := 4) emittedFar)
    have reservationBound : FB + reserved ≤ frei Γ reserved := by unfold frei; omega
    have imageBound : 16 * (cc.1.length + cb.length + 13) < 2 ^ 31 := by
      simpa only [foreverCode_length] using hs
    have stopSX : sx (BitVec.ofInt 32 ((16 * (cc.1.length + cb.length + 8) : Nat) : Int)) =
        BitVec.ofNat 64 (16 * (cc.1.length + cb.length + 8)) := sx_nat (d := 16 * (cc.1.length + cb.length + 8)) (by omega)
    have stopAddress : pc + 32 + sx (BitVec.ofInt 32 ((16 * (cc.1.length + cb.length + 8) : Nat) : Int)) =
        pc + 32 + BitVec.ofNat 64 (16 * control.length) + BitVec.ofNat 64 16 := by
      rw [stopSX, addr_norm, controlLength]
      congr 2 <;> omega
    have castBack : (16 * (cc.1.length + cb.length + 7 : Nat) : Int) =
        ((16 * (cc.1.length + cb.length + 7) : Nat) : Int) := by omega
    have nextAddress : pc + 32 + BitVec.ofNat 64 (16 * control.length) +
        BitVec.ofInt 64 (-(16 * (cc.1.length + cb.length + 7 : Nat) : Int)) = pc + 32 := by
      rw [controlLength, castBack, BitVec.ofInt_neg, BitVec.ofInt_natCast,
        BitVec.add_neg_eq_sub, BitVec.add_sub_cancel]
    have jumpLiteral : lit32 (-(16 * (cc.1.length + cb.length + 7 : Nat) : Int)) = true := by
      simp only [lit32, Bool.and_eq_true, decide_eq_true_eq]
      omega
    apply Sim.prefix hlo initRun.forget initFrame keeps
    simp only [execStmt]
    apply forever_counter_loop (O := O) (cb := cb) (tb := tb)
      (stop := (16 * (cc.1.length + cb.length + 8) : Nat))
      (back := pc + 32 + BitVec.ofNat 64 (16 * control.length))
      (jump := II.f (-(16 * (cc.1.length + cb.length + 7 : Nat) : Int)))
      (b := 0) (c := 0)
      (counter := (counterPair reserved (counterDepthB body)).1)
      (one := (counterPair reserved (counterDepthB body)).2)
      (ex := (64, -(16 * (cc.1.length + cb.length + 7 : Nat) : Int)))
      hS hA hlo0 hens inv body hcc
    case hcb => simpa only [forever_runtime_targets] using hcb
    case hW => exact hW
    case hlo => exact hlo
    case hlo2 => exact hlo2
    case backFar => exact backFar
    case stopRoom => exact room
    case surround => exact surrounds
    case head => exact snapshot
    case world => exact world
    case read => exact count
    case readOne => exact unit
    case backAt =>
      change (pc + 32) + BitVec.ofNat 64 32 + _ = _
      rw [addr_norm]
      apply congrArg (fun n : Nat => (pc + 32) + BitVec.ofNat 64 n)
      rw [controlLength]
      simp only [stopC, sysC, List.length_append, List.length_cons, List.length_nil]
      omega
    case leaveAt =>
      change pc + 32 + BitVec.ofNat 64 (16 * control.length) + BitVec.ofNat 64 64 = _
      rw [addr_norm]
      change pc + BitVec.ofNat 64 32 + _ = _
      rw [addr_norm, controlLength, foreverCode_length]
      exact congrArg (fun n : Nat => pc + BitVec.ofNat 64 n) (by omega)
    case nextAt => exact nextAddress
    case jumpAt => rw [sx_lit jumpLiteral]; exact nextAddress
    case low => rw [hlo0]; exact allowed.1
    case allocated => omega
    case oneBound => omega
    case distinct => omega
    case hprotected =>
      intro j hj
      exact ⟨by have := hpr j hj; omega, fun eq => allowed.2.2.1 (eq ▸ hj)⟩
    case stopFar => rw [stopAddress]; exact budgetFar
    case fits => exact fuel.2
    case pre =>
      exact ⟨entry.ctx, entry.small, entry.frame, codeAt_left emittedCode,
        codeFar_left (n := control.length) (k := 4) emittedFar,
        entry.env, trivial, wstab_true _ _⟩
    case edge => simpa [ci, II.f] using backCode 0 (by simp)
    case stopCode => rw [stopAddress]; exact budgetCode
    case htc => omega
    case htb => omega
    case room => omega
    case hs => omega
    case hpr =>
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · unfold frei; omega
      · unfold frei; omega
      · exact hpr j hj
    case bodyRuns => exact bodyRuns
  · simp at h

set_option linter.unusedSectionVars false in
theorem lowB_ok_nil {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.nil : Block D (vertragVon D f) l Γ Λ (Λ)) = some (c, top))
    (zzh1 : top + cap ≤ Ks)
    (zzh2 : 16 * c.length < 2 ^ 31)
    (zzh3 : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (zzh4 : FB ≤ lo)
    (zzh5 : lo ≤ frei Γ reserved)
    (zzh6 : Umf L A C dv m fp Ks K H)
    (zzh7 : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.nil : Block D (vertragVon D f) l Γ Λ (Λ)) σ ρ) reserved :=
  by
  simp only [lowB, ← hlo0, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [execBlock, Sim]
  exact ⟨m, by simpa using Star.refl _ m, AgreeW.refl _ _ _ _ _, hp.env, hWa, Keeps.refl _ _ _⟩


end Gabbro.Stage0.Senke
