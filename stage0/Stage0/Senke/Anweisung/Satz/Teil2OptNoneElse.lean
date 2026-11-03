module
public import Stage0.Senke.Anweisung.Satz.Teil4

public import Stage0.Senke.Anweisung.Bindung.Void
public import Stage0.Senke.Anweisung.FehlerLauf
public import Stage0.Senke.Anweisung.Faelle.Hilfen
public import Stage0.Senke.Anweisung.Faelle.CallElse
public import Stage0.Senke.Anweisung.Schreiben
public import Stage0.Senke.Welt.Spans.CellStore
public import Stage0.Senke.Welt.WordCell
public import Stage0.Senke.Sperre.Satz
public import Stage0.Senke.Anweisung.Faelle.Gleit.Narrow
public import Stage0.Senke.Anweisung.Faelle.Gleit.Literal
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Wahl
public import Stage0.Senke.Anweisung.Bindung.Option
public import Stage0.Senke.Anweisung.Faelle.Kontrolle.Why
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

/-- `let x? = g(…) else (e) { … };` over a VOID foreign result («C08»): on an answer
    the rest runs in the same context (`ErgCtx Γ none = Γ`); a reason runs `err`. -/
theorem lowB_ok_bindAxiomOptElse_none {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    {Λ' : List (Res D)}
    (a)
    (args)
    (he)
    (hcall)
    (hd)
    (hgd)
    (hr)
    (err)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindAxiomOptElse (e := none) a args he hcall hd hgd hr err rest : Block D (vertragVon D f) l Γ Λ Λ') = some (c, top))
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
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowB_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ f, A f < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowB (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → FB ≤ lo → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R rest σ ρ) reserved)
    (ih_lowEnd_ok_err : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex err = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) c ρ reserved → lo ≤ frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R err σ ρ) reserved)
    : Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length)) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execBlock O passes R (.bindAxiomOptElse (e := none) a args he hcall hd hgd hr err rest : Block D (vertragVon D f) l Γ Λ Λ') σ ρ) reserved := by
  simp only [lowB, ← hlo0] at h
  split at h
  · next b hb _ =>
    split at h
    · next hc =>
      obtain ⟨hf, hn, hwhy⟩ := hc
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ct, tt⟩, ht, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hr, hc⟩ := h
      split at hc
      · next hJ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp only [List.length_append, List.length_singleton, fehlC_len] at hs
        have hks := hW.ks
        simp only [execBlock]
        rcases torElseNone_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he hb hf hn ht hJ (by omega)
          (by omega) hW hp hWa with ⟨v, m2, hAA, s12, a12, hW2⟩ | ⟨r, m2, hAA, s12, a12, hw2, hW2⟩
        · rw [hAA]
          simp only [Ausgang.weiterOpt, ergEnv]
          have hp2 : PreS (reserved := reserved) L m pc fp K (frei Γ reserved) ((ct ++ fehlC (frei Γ reserved) b.fehler ((16 * ((cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]).length) : Nat) : Int)) ++ ((cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]) ++ ce)) ρ reserved := by simpa only [List.append_assoc] using hp
          have hq := hp2.nextW hW a12 (d' := frei Γ reserved) (by have := hp.ctx; omega) (by omega) (by omega)
          simp only [List.length_append, fehlC_len] at hq
          have hp3 : PreS (reserved := reserved) L m2 _ fp K (frei Γ reserved) cr ρ reserved :=
            ⟨by omega, hq.small, hq.frame, hq.left.left.code, hq.left.left.far,
             hq.env, trivial, wstab_true _ _⟩
          have ih := ih_lowB_ok_rest hS hA hlo0 hens (cap := cap) (pr := pr) (ex := exPlus ex (ce.length + 1)) cr tr hr (by omega) (by omega) hW m2 _ _ _ hp3 hlo hlo2
            (hu.agreeW hW (a12.mono hlo2) hlo) (hk.agreeW hW (a12.mono hlo2) (by omega)) hW2 hpr
          refine Sim.prefix hlo s12 (a12.mono hlo2) (keeps_of_agreeW hW a12 hpr (by omega))
            (Sim.cont ih ?_ ?_ ?_)
          · intro m3 a3
            have hc3 := codeAt_agreeWIn hW a3 (codeAt_right hq.left.code)
              (codeFar_right (n := cr.length) (k := 1) (by simpa using hq.left.far))
            have hj := hc3 0 (by simp)
            simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hj
            have sj := Star.one (run_step (t := ⟨_, fp⟩) hj (by decide) (run_jmp (t := ⟨_, fp⟩) hj))
            have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
              have := sx_nat (d := 16 * (ce.length + 1)) (by omega); simpa using this
            rw [hl] at sj
            refine star_cast sj rfl ?_
            simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, fehlC_len, addr_norm]
            congr 2 <;> omega
          · simp only [exPlus, List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq (by omega)
          · simp only [exPlus, List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq (by omega)
        · rw [hAA]
          have hp2 : PreS (reserved := reserved) L m pc fp K (frei Γ reserved) ((ct ++ fehlC (frei Γ reserved) b.fehler ((16 * ((cr ++ [ci 18 (16 * (ce.length + 1)) 0 0]).length) : Nat) : Int)
              ++ (cr ++ [ci 18 (16 * (ce.length + 1)) 0 0])) ++ ce) ρ reserved := by simpa only [List.append_assoc] using hp
          have hq := hp2.nextW hW a12 (d' := frei Γ reserved + 1) (by have := hp.ctx; omega) (by omega) (by omega)
          simp only [List.length_append, fehlC_len] at hq
          have hp3 : PreS (reserved := reserved) L m2 _ fp K (frei (.why (D.agruende a) :: Γ) reserved) ce (Env.cons (τ := .why (D.agruende a)) r ρ) reserved :=
            ⟨by simp only [frei, contextWords_cons, hwhy]; omega, hq.small, hq.frame, hq.code, hq.far,
             envAt_cons hq.env (ValueAt.of_enc hwhy hw2 rfl), trivial, wstab_true _ _⟩
          have ih := ih_lowEnd_ok_err hS hA hlo0 hens (cap := cap) (pr := pr) (ex := ex) ce te hce (by omega) (by omega) hW m2 _ _ _ hp3
            (by simp only [frei, contextWords_cons, hwhy] at hlo ⊢; omega)
            (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
            (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, hwhy] at this ⊢; omega)
          refine Sim.prefix hlo s12 (a12.mono hlo2) (keeps_of_agreeW hW a12 hpr (by omega))
            (Ret.toSim (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_))
          · simp only [List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
          · simp only [List.length_append, List.length_singleton, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
      · cases hc
    · cases h
  · cases h


/-- `let x? = g(…) else (e) { … };` over a VOID foreign result at the top level of a body
    («C08»): same handover as `lowB_ok_bindAxiomOptElse_none`, for end blocks. -/
theorem lowEnd_ok_bindAxiomOptElse_none {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}
    {l : Bool}
    {Γ : Ctx}
    {Λ : List (Res D)}
    (a)
    (args)
    (he)
    (hcall)
    (hd)
    (hgd)
    (hr)
    (err)
    (rest)
    (c : List II)
    (top : Nat)
    (h : lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex (.bindAxiomOptElse (e := none) a args he hcall hd hgd hr err rest : Endblock D (vertragVon D f) l Γ Λ) = some (c, top))
    (hK : top + cap ≤ Ks)
    (hs : 16 * c.length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (m : Runner.Mem)
    (pc : Runner.W)
    (σ : World D)
    (ρ : Env D Γ)
    (hp : PreS L m pc fp K (frei Γ reserved) c ρ reserved)
    (hlo : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K)
    (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hWa : WeltAt m L σ)
    (hpr : (∀ j ∈ pr, j < frei Γ reserved))
    (ih_lowEnd_ok_err : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex err = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ)), PreS L m pc fp K (frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) c ρ reserved → lo ≤ frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei (Gabbro.Grammatik.Ty.why (D.agruende a) :: Γ) reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R err σ ρ) reserved)
    (ih_lowEnd_ok_rest : ∀ {O : Orakel D} [zinst1 : TorOK L O] [zinst2 : SichtOK O] {passes : Nat} {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap) (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {fp : Runner.W} {K : Nat} {Ks : Nat} {lo : Nat} {rp : Runner.W} {cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat} (hlo0 : lo = (functionFrame P f).internalResult) (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens)) {reserved : Nat} {pr : List Nat} {ex : Int × Int}, ∀ (c : List II), ∀ (top : Nat), lowEnd (reserved := reserved) passes A L (functionFrame P f) (cens, tens) pr ex rest = some (c, top) → top + cap ≤ Ks → 16 * c.length < 2 ^ 31 → WIn L fp Ks K → ∀ (m : Runner.Mem), ∀ (pc : Runner.W), ∀ (σ : World D), ∀ (ρ : Env D Γ), PreS L m pc fp K (frei Γ reserved) c ρ reserved → lo ≤ frei Γ reserved → Umf L A C dv m fp Ks K → Kopf L f m fp K rp cfp ρ0 P σ0 → WeltAt m L σ → (∀ j ∈ pr, j < frei Γ reserved) → Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R rest σ ρ) reserved)
    : Ret L P f σ0 ρ0 fp lo K pr rp cfp ⟨pc, fp⟩ m (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.1) (pc + BitVec.ofNat 64 (16 * c.length) + BitVec.ofInt 64 ex.2) (execEnd O passes R (.bindAxiomOptElse (e := none) a args he hcall hd hgd hr err rest : Endblock D (vertragVon D f) l Γ Λ) σ ρ) reserved := by
  simp only [lowEnd, ← hlo0, resultWords_vertragVon] at h
  split at h
  · next b hb _ =>
    split at h
    · next hc =>
      obtain ⟨hf, hn, hwhy⟩ := hc
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ct, tt⟩, ht, ⟨ce, te⟩, hce, ⟨cr, tr⟩, hr, hc⟩ := h
      split at hc
      · next hJ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp only [List.length_append, fehlC_len] at hs
        have hks := hW.ks
        have hFB3 : FB = 4 := rfl
        have hFramePrefix := functionFrame_prefix P f
        simp only [execEnd]
        rcases torElseNone_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) he hb hf hn ht hJ (by omega)
          (by omega) hW hp hWa with ⟨v, m2, hAA, s12, a12, hW2⟩ | ⟨r, m2, hAA, s12, a12, hw2, hW2⟩
        · rw [hAA]
          simp only [EndAusgang.weiterOpt, ergEnv]
          have hp2 : PreS L m pc fp K (frei Γ reserved) ((ct ++ fehlC (frei Γ reserved) b.fehler ((16 * cr.length : Nat) : Int)) ++ (cr ++ ce)) ρ reserved := by simpa only [List.append_assoc] using hp
          have hq := hp2.nextW hW a12 (d' := frei Γ reserved) (by have := hp.ctx; omega) (by omega) (by omega)
          simp only [List.length_append, fehlC_len] at hq
          have hp3 : PreS L m2 _ fp K (frei Γ reserved) cr ρ reserved :=
            ⟨by omega, hq.small, hq.frame, hq.left.code, hq.left.far, hq.env, trivial, wstab_true _ _⟩
          have ih := ih_lowEnd_ok_rest hS hA hlo0 hens (cap := cap) (pr := pr) (ex := exPlus ex ce.length) cr tr hr (by omega) (by omega) hW m2 _ _ _ hp3 hlo
            (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2 hpr
          refine Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
            (Ret.cast ih rfl ?_ ?_)
          · simp only [List.length_append, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
          · simp only [List.length_append, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
        · rw [hAA]
          have hp2 : PreS L m pc fp K (frei Γ reserved) ((ct ++ fehlC (frei Γ reserved) b.fehler ((16 * cr.length : Nat) : Int) ++ cr) ++ ce) ρ reserved := by simpa only [List.append_assoc] using hp
          have hq := hp2.nextW hW a12 (d' := frei Γ reserved + 1) (by have := hp.ctx; omega) (by omega) (by omega)
          simp only [List.length_append, fehlC_len] at hq
          have hp3 : PreS L m2 _ fp K (frei (.why (D.agruende a) :: Γ) reserved) ce (Env.cons (τ := .why (D.agruende a)) r ρ) reserved :=
            ⟨by simp only [frei, contextWords_cons, hwhy]; omega, hq.small, hq.frame, hq.code, hq.far,
             envAt_cons hq.env (ValueAt.of_enc hwhy hw2 rfl), trivial, wstab_true _ _⟩
          have ih := ih_lowEnd_ok_err hS hA hlo0 hens (cap := cap) (pr := pr) (ex := ex) ce te hce (by omega) (by omega) hW m2 _ _ _ hp3
            (by simp only [frei, contextWords_cons, hwhy] at hlo ⊢; omega)
            (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hW2
            (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, hwhy] at this ⊢; omega)
          refine Ret.prefix (by omega) s12 (a12.mono (by omega)) (keeps_of_agreeW hW a12 hpr (by omega))
            (Ret.cast (Ret.schrumpf ih) rfl ?_ ?_)
          · simp only [List.length_append, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
          · simp only [List.length_append, fehlC_len, addr_norm]
            exact tgt_eq0 (by omega)
      · cases hc
    · cases h
  · cases h

end Gabbro.Stage0.Senke
