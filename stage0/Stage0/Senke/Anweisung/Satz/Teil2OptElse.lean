module
public import Stage0.Senke.Anweisung.Satz.Teil4
import Stage0.Senke.Anweisung.Satz.Teil2Opt

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

theorem lowB_ok_bindAxiomOptElse_some {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hr)
    (hcall)
    (hd)
    (hgd)
    (err)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindAxiomOptElse (e := some zi_τ) a args he hcall hd hgd hr err rest : Block D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (hH : HeldIn H Λ (vertragVon D f).boden)
    (ih_lowB_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, HeldIn H (blockAnf rest) (vertragVon D f).boden → ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (zi_τ :: Γ)), PreS L m pc fp K (frei (zi_τ :: Γ) reserved) c ρ reserved → FB ≤ lo → lo ≤ frei (zi_τ :: Γ) reserved → Umf L A C dv m fp Ks K H → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (zi_τ :: Γ) reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R rest σ ρ) reserved)
    (ih_lowEnd_ok_err : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, HeldIn H (endAnf err) (vertragVon D f).boden → ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex err = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) c ρ reserved → lo ≤ frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved → Umf L A C dv m fp Ks K H → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R err σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.bindAxiomOptElse (e := some zi_τ) a args he hcall hd hgd hr err rest : Block D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved :=
  by
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, errorMade, ⟨cr, tr⟩, restMade, ⟨cg, tg⟩, foreignMade, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have metadata := fallibleForeignC_top foreignMade
  have reasonWidth := metadata.2.2
  have hks := hW.ks
  simp only [List.length_append, List.length_singleton] at hs
  simp only [execBlock]
  rcases fallibleForeignC_ok (L := L) (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ)
      he foreignMade (by omega) hW (by simpa only [List.append_assoc] using hp) hWa with
      ⟨v, m2, decoded, steps, changed, value, world⟩ |
      ⟨reason, m2, decoded, steps, changed, read, world⟩ | ⟨decoded, stopped⟩
  · rw [decoded]
    simp only [Ausgang.weiterOpt, someAnswer_env he v ρ]
    have pre : PreS L m pc fp K (frei Γ reserved)
        (cg ++ ((cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]) ++ ce)) ρ reserved := by
      simpa only [List.append_assoc] using hp
    have next := pre.nextW hW changed (d' := frei Γ reserved + valueWords zi_τ)
      (by have := hp.ctx; omega) (by omega) (by omega)
    have bodyPre : PreS L m2 _ fp K (frei (zi_τ :: Γ) reserved) cr
        (Env.cons (ergWert he v) ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons]; omega, next.small, next.frame,
        next.left.left.code, next.left.left.far, envAt_cons next.env value, trivial, wstab_true _ _⟩
    have ih := ih_lowB_ok_rest (O := O) (passes := passes) (σ0 := σ0)
      (reserved := reserved) (pr := pr) (ex := exPlus ex (ce.length + 1))
      hS hA hlo0 hens (HeldIn.sig (S := D.asignatur a) hH) cr tr restMade (by omega) (by omega) hW m2 _ _ _ bodyPre hlo
      (by simp only [frei, contextWords_cons] at hlo2 ⊢; omega)
      (hu.agreeW hW changed (by omega)) (hk.agreeW hW changed (by omega)) world
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)
    refine Sim.prefix hlo steps (changed.mono hlo2) (keeps_of_agreeW hW changed hpr (by omega))
      (Sim.cont (Sim.schrumpf ih) ?_ ?_ ?_)
    · intro m3 bodyChanged
      have code := codeAt_agreeWIn hW bodyChanged (codeAt_right next.left.code)
        (codeFar_right (n := cr.length) (k := 1) (by simpa using next.left.far))
      have instruction := code 0 (by simp)
      simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at instruction
      have jump := Star.one (run_step (t := ⟨_, fp⟩) instruction (by decide)
        (run_jmp (t := ⟨_, fp⟩) instruction))
      have offset : sx (II.f (16 * ((ce.length : Int) + 1))) =
          BitVec.ofNat 64 (16 * (ce.length + 1)) := by
        have := sx_nat (d := 16 * (ce.length + 1)) (by omega)
        simpa using this
      rw [offset] at jump
      refine star_cast jump rfl ?_
      simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, addr_norm]
      congr 2 <;> omega
    · simp only [exPlus, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
    · simp only [exPlus, List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq (by omega)
  · rw [decoded]
    have pre : PreS L m pc fp K (frei Γ reserved)
        ((cg ++ (cr ++ [ci 18 (16 * (ce.length + 1)) 0 0])) ++ ce) ρ reserved := by
      simpa only [List.append_assoc] using hp
    have next := pre.nextW hW changed (d' := frei Γ reserved + 1)
      (by have := hp.ctx; omega) (by omega) (by omega)
    simp only [List.length_append] at next
    have errorPre : PreS L m2 _ fp K (frei (.why (D.agruende a) :: Γ) reserved) ce
        (Env.cons (τ := .why (D.agruende a)) reason ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons, reasonWidth]; omega, next.small, next.frame,
        next.code, next.far, envAt_cons next.env (ValueAt.of_enc reasonWidth read rfl),
        trivial, wstab_true _ _⟩
    have ih := ih_lowEnd_ok_err (O := O) (passes := passes) (σ0 := σ0)
      (reserved := reserved) (pr := pr) (ex := ex) hS hA hlo0 hens (HeldIn.sig (S := D.asignatur a) hH) ce te errorMade
      (by omega) (by omega) hW m2 _ _ _ errorPre
      (by simp only [frei, contextWords_cons, reasonWidth] at hlo2 ⊢; omega)
      (hu.agreeW hW changed (by omega)) (hk.agreeW hW changed (by omega)) world
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, reasonWidth] at this ⊢; omega)
    refine Sim.prefix hlo steps (changed.mono hlo2) (keeps_of_agreeW hW changed hpr (by omega))
      (Ret.toSim (Ret.cast (Ret.schrumpf ih) ?_ ?_ ?_))
    · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, addr_norm]
    · simp only [List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · rw [decoded]
    exact stopped

theorem lowEnd_ok_bindAxiomOptElse_some {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {zi_τ}
    (a)
    (args)
    (he)
    (hr)
    (hcall)
    (hd)
    (hgd)
    (err)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindAxiomOptElse (e := some zi_τ) a args he hcall hd hgd hr err rest : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K H)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (hH : HeldIn H Λ (vertragVon D f).boden)
    (ih_lowEnd_ok_err : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, HeldIn H (endAnf err) (vertragVon D f).boden → ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex err = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) c ρ reserved → lo ≤ frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved → Umf L A C dv m fp Ks K H → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R err σ ρ) reserved)
    (ih_lowEnd_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, HeldIn H (endAnf rest) (vertragVon D f).boden → ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (zi_τ :: Γ)), PreS L m pc fp K (frei (zi_τ :: Γ) reserved) c ρ reserved → lo ≤ frei (zi_τ :: Γ) reserved → Umf L A C dv m fp Ks K H → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (zi_τ :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R rest σ ρ) reserved)
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.bindAxiomOptElse (e := some zi_τ) a args he hcall hd hgd hr err rest : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved :=
  by
  simp only [lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ce, te⟩, errorMade, ⟨cr, tr⟩, restMade, ⟨cg, tg⟩, foreignMade, hc⟩ := h
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have metadata := fallibleForeignC_top foreignMade
  have reasonWidth := metadata.2.2
  have hks := hW.ks
  have framePrefix := functionFrame_prefix P f
  have frameBase : FB = 4 := rfl
  simp only [List.length_append, List.length_singleton] at hs
  simp only [execEnd]
  rcases fallibleForeignC_ok (L := L) (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ)
      he foreignMade (by omega) hW (by simpa only [List.append_assoc] using hp) hWa with
      ⟨v, m2, decoded, steps, changed, value, world⟩ |
      ⟨reason, m2, decoded, steps, changed, read, world⟩ | ⟨decoded, stopped⟩
  · rw [decoded]
    simp only [EndAusgang.weiterOpt, someAnswer_env he v ρ]
    have pre : PreS L m pc fp K (frei Γ reserved) (cg ++ (cr ++ ce)) ρ reserved := by
      simpa only [List.append_assoc] using hp
    have next := pre.nextW hW changed (d' := frei Γ reserved + valueWords zi_τ)
      (by have := hp.ctx; omega) (by omega) (by omega)
    have bodyPre : PreS L m2 _ fp K (frei (zi_τ :: Γ) reserved) cr
        (Env.cons (ergWert he v) ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons]; omega, next.small, next.frame,
        next.left.code, next.left.far, envAt_cons next.env value, trivial, wstab_true _ _⟩
    have ih := ih_lowEnd_ok_rest (O := O) (passes := passes) (σ0 := σ0)
      (reserved := reserved) (pr := pr) (ex := exPlus ex ce.length)
      hS hA hlo0 hens (HeldIn.sig (S := D.asignatur a) hH) cr tr restMade (by omega) (by omega) hW m2 _ _ _ bodyPre
      (by simp only [frei, contextWords_cons] at hlo ⊢; omega)
      (hu.agreeW hW changed (by omega)) (hk.agreeW hW changed (by omega)) world
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons] at this ⊢; omega)
    refine Ret.prefix (by omega) steps (changed.mono (by omega))
      (keeps_of_agreeW hW changed hpr (by omega)) (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [exPlus, List.length_append, addr_norm]
      exact tgt_eq (by omega)
    · simp only [exPlus, List.length_append, addr_norm]
      exact tgt_eq (by omega)
  · rw [decoded]
    have pre : PreS L m pc fp K (frei Γ reserved) ((cg ++ cr) ++ ce) ρ reserved := by
      simpa only [List.append_assoc] using hp
    have next := pre.nextW hW changed (d' := frei Γ reserved + 1)
      (by have := hp.ctx; omega) (by omega) (by omega)
    simp only [List.length_append] at next
    have errorPre : PreS L m2 _ fp K (frei (.why (D.agruende a) :: Γ) reserved) ce
        (Env.cons (τ := .why (D.agruende a)) reason ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons, reasonWidth]; omega, next.small, next.frame,
        next.code, next.far, envAt_cons next.env (ValueAt.of_enc reasonWidth read rfl),
        trivial, wstab_true _ _⟩
    have ih := ih_lowEnd_ok_err (O := O) (passes := passes) (σ0 := σ0)
      (reserved := reserved) (pr := pr) (ex := ex) hS hA hlo0 hens (HeldIn.sig (S := D.asignatur a) hH) ce te errorMade
      (by omega) (by omega) hW m2 _ _ _ errorPre
      (by simp only [frei, contextWords_cons, reasonWidth] at hlo ⊢; omega)
      (hu.agreeW hW changed (by omega)) (hk.agreeW hW changed (by omega)) world
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, reasonWidth] at this ⊢; omega)
    refine Ret.prefix (by omega) steps (changed.mono (by omega))
      (keeps_of_agreeW hW changed hpr (by omega)) (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
    · simp only [List.length_append, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [List.length_append, addr_norm]
      exact tgt_eq0 (by omega)
  · rw [decoded]
    exact stopped

end Gabbro.Stage0.Senke
