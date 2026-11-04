/- Fallible statement calls discard success values and bind only the reason. -/
module
public import Stage0.Senke.Anweisung.Satz.Teil2OptNoneElse
public import Stage0.Senke.Tore.FallibleRun
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Shared handover after errno dispatch: success skips the end block, while a
    reason enters it with one extra environment slot. The gate prefix can include
    a result range check, even though its successful value is discarded. -/
private theorem discardGate_result {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat}
    {P : Programm D} {f : D.Fn} {fp rp cfp : Runner.W} {K Ks lo reserved : Nat}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {a : D.Ax} {err : Endblock D (vertragVon D f) l (.why (D.agruende a) :: Γ) Λ}
    {cg ce : List II} {te : Nat} {m : Runner.Mem} {pc : Runner.W} {ρ : Env D Γ}
    {σ' : World D} {answer : World D × Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a))}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hwhy : valueWords (.why (D.agruende a)) = 1)
    (hce : lowEnd passes A L (functionFrame P f) (cens, tens) pr ex err reserved = some (ce, te))
    (hroom : frei Γ reserved + 10 ≤ Ks) (hK : te + cap ≤ Ks) (hs : 16 * (cg ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length < 2 ^ 31)
    (hW : WIn L fp Ks K)
    (hp : PreS L m pc fp K (frei Γ reserved) (cg ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce) ρ reserved)
    (hlo : FB ≤ lo) (hlo2 : lo ≤ frei Γ reserved)
    (hu : Umf L A C dv m fp Ks K) (hk : Kopf L f m fp K rp cfp ρ0 P σ0)
    (hpr : ∀ j ∈ pr, j < frei Γ reserved)
    (ihErr : ∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err reserved)
    (hgate :
      (∃ v m2, answer = (σ', some (.inl v)) ∧
        Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * cg.length), fp⟩ m2 ∧
        AgreeW L fp (frei Γ reserved) K m m2 ∧ WeltAt m2 L σ') ∨
      (∃ r m2, answer = (σ', some (.inr r)) ∧
        Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (cg.length + 1)), fp⟩ m2 ∧
        AgreeW L fp (frei Γ reserved) K m m2 ∧
        m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ reserved))) = some (BitVec.ofNat 64 r.val) ∧ WeltAt m2 L σ') ∨
      (answer = (σ', none) ∧ Stops ⟨pc, fp⟩ m 110)) :
    Sim L P f σ0 ρ0 rp cfp fp lo K pr ⟨pc, fp⟩ m
      (pc + BitVec.ofNat 64 (16 * (cg ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length))
      (pc + BitVec.ofNat 64 (16 * (cg ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.1)
      (pc + BitVec.ofNat 64 (16 * (cg ++ [ci 18 (16 * (ce.length + 1)) 0 0] ++ ce).length) + BitVec.ofInt 64 ex.2)
      (match answer with
       | (σ, some (.inl _)) => .ok σ ρ
       | (σ, some (.inr r)) => (execEnd O passes R err σ (.cons r ρ)).schrumpf.zuAusgang
       | (_, none) => .hardware (.annahme a)) reserved := by
  have hks := hW.ks
  have hp' : PreS L m pc fp K (frei Γ reserved) (cg ++ ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce)) ρ reserved := by
    simpa only [List.append_assoc] using hp
  rcases hgate with ⟨v, m2, rfl, s12, a12, hw⟩ | ⟨r, m2, rfl, s12, a12, hw2, hw⟩ | ⟨rfl, hst⟩
  · have hq := hp'.nextW hW a12 (d' := frei Γ reserved) (by have := hp.ctx; omega) (by omega) (by omega)
    have hj := hq.left.code 0 (by simp)
    simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hj
    have sj := Star.one (run_step (t := ⟨_, fp⟩) hj (by decide) (run_jmp (t := ⟨_, fp⟩) hj))
    have hl : sx (II.f (16 * ((ce.length : Int) + 1))) = BitVec.ofNat 64 (16 * (ce.length + 1)) := by
      have := sx_nat (d := 16 * (ce.length + 1)) (by simp only [List.length_append, List.length_singleton] at hs; omega)
      simpa using this
    rw [hl] at sj
    refine ⟨m2, s12.trans (star_cast sj rfl ?_), a12.mono hlo2, hq.env, hw,
      keeps_of_agreeW hW a12 hpr (by omega)⟩
    simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton, addr_norm]
    congr 2 <;> omega
  · have hp2 : PreS L m pc fp K (frei Γ reserved) ((cg ++ [ci 18 (16 * (ce.length + 1)) 0 0]) ++ ce) ρ reserved := hp
    have hq := hp2.nextW hW a12 (d' := frei Γ reserved + 1) (by have := hp.ctx; omega) (by omega) (by omega)
    simp only [List.length_append, List.length_singleton] at hq
    have hp3 : PreS L m2 _ fp K (frei (.why (D.agruende a) :: Γ) reserved) ce
        (Env.cons (τ := .why (D.agruende a)) r ρ) reserved :=
      ⟨by simp only [frei, contextWords_cons, hwhy]; omega, hq.small, hq.frame, hq.code, hq.far,
       envAt_cons hq.env (ValueAt.of_enc hwhy hw2 rfl), trivial, wstab_true _ _⟩
    have ih := ihErr ce te hce hK (by simp only [List.length_append, List.length_singleton] at hs; omega) hW m2 _ _ _ hp3
      (by simp only [frei, contextWords_cons, hwhy] at hlo2 ⊢; omega)
      (hu.agreeW hW a12 (by omega)) (hk.agreeW hW a12 (by omega)) hw
      (fun j hj => by have := hpr j hj; simp only [frei, contextWords_cons, hwhy] at this ⊢; omega)
    refine Sim.prefix hlo s12 (a12.mono hlo2) (keeps_of_agreeW hW a12 hpr (by omega))
      (Ret.zuAusgang (Ret.cast (Ret.schrumpf ih) ?_ ?_ ?_))
    · simp only [T.mk.injEq, and_true, List.length_append, List.length_singleton]
    · simp only [List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
    · simp only [List.length_append, List.length_singleton, addr_norm]
      exact tgt_eq0 (by omega)
  · exact hst

/-- Generic lowering case for statement-position fallible gates, for both a
    bounded integer result and VOID. Only the reason extends the caller context. -/
theorem stmtAxiomElse_case {O : Orakel D} [TorOK L O] [SichtOK O] {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f}
    {A : D.Fn → Nat} {C : D.Fn → List II} {dv : Runner.W} {cap : Nat} (hS : FunSpec L A C R dv cap)
    (hA : ∀ g, A g < 2 ^ 31) {P : Programm D} {f : D.Fn} {fp : Runner.W} {K Ks lo : Nat} {rp cfp : Runner.W}
    {σ0 : World D} {ρ0 : Env D (D.params f)} {cens : List II} {tens : Nat}
    (hlo0 : lo = (functionFrame P f).internalResult)
    (hens : lowPost L (functionFrame P f) P f (lo + returnWords (D.erg f) (D.gruende f)) = some (cens, tens))
    {reserved : Nat} {pr : List Nat} {ex : Int × Int} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {e : Option Ty} {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {he : D.aerg a = e}
    {hcall : RufPasst D (vertragVon D f) (D.asignatur a) Λ} {hd : _} {hgd : _} {hr : 0 < D.agruende a}
    {err : Endblock D (vertragVon D f) l (reasonTy (D.agruende a) :: Γ) (nachSig D (D.asignatur a) Λ)} :
    (∀ {pr ex}, EndCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex err reserved) →
    StmtCase L O passes R A C dv cap P f fp K Ks lo rp cfp σ0 ρ0 cens tens pr ex
      (.axiomCallElse e a args he hcall hd hgd hr err) reserved := by
  intro ihErr c top h hK hs hW m pc σ ρ hp hlo hlo2 hu hk hWa hpr
  simp only [lowS, ← hlo0] at h
  split at h
  · next b answer hb hτ =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨⟨ce, te⟩, hce, ⟨cg, tg⟩, hg, hc⟩ := h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have metadata := fallibleForeignC_top hg
    have hgate := fallibleForeignC_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) hτ hg
      (success := [ci 18 (16 * (ce.length + 1)) 0 0]) (by omega) hW hp hWa
    apply discardGate_result hlo0 metadata.2.2 hce (by omega) (by omega) hs hW hp hlo hlo2 hu hk hpr ihErr
    rcases hgate with ⟨v, m2, decoded, run, changed, value, world⟩ |
        ⟨reason, m2, decoded, run, changed, read, world⟩ | invalid
    · exact .inl ⟨v, m2, decoded, run, changed, world⟩
    · exact .inr (.inl ⟨reason, m2, decoded, by simpa only [List.length_singleton] using run,
        changed, read, world⟩)
    · exact .inr (.inr invalid)
  · next b hb hτ =>
    split at h
    · next hc =>
      obtain ⟨hf, hn, hwhy⟩ := hc
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ct, tt⟩, ht, ⟨ce, te⟩, hce, hc⟩ := h
      split at hc
      · next hJ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hg := torElseNone_ok (O := O) (σ := σ.lese Λ args.orte) (ρ := ρ) hτ hb hf hn ht
          (cr := [ci 18 (16 * (ce.length + 1)) 0 0]) hJ (by omega) (by omega) hW hp hWa
        apply discardGate_result hlo0 hwhy hce (by omega) (by omega) hs hW hp hlo hlo2 hu hk hpr ihErr
        rcases hg with ⟨v, m2, ha, st, ag, hw⟩ | ⟨r, m2, ha, st, ag, wr, hw⟩
        · exact .inl ⟨v, m2, ha, by simpa only [List.length_append, fehlC_len] using st, ag, hw⟩
        · exact .inr (.inl ⟨r, m2, ha, by simpa only [List.length_append, List.length_singleton, fehlC_len] using st, ag, wr, hw⟩)
      · cases hc
    · cases h
  · cases h

end Gabbro.Stage0.Senke
