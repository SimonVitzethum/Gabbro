module
public import Bruecke.Kette.Verknuepfung
public import Bruecke.Anweisung.Ruf.Rahmen
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

/-- A result call, including a pure one, contributes one ordered answer-table entry.
    The private clock is part of the Body proof frame, never a canonical write right. -/
theorem resultCall_strecke {P : Programm (declOf u)} (G : GesenktC u C P)
    (S : Getragen u C) {c : Fin u.fns.length} (hc : C c)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (hRR : RespektiertRahmen P R) {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {ns : BodyNames} {x g : String} {args : List UArg}
    {k : RufKopf u c Γ Λ} {ty : Ty} {b : Gabbro.Body.Stmt}
    (hk : lowRufKopf u c Γ fn Λ g args = .ok k)
    (he : (declOf u).erg k.callee = some ty)
    (hb : namedResult u fn ns x g args = some (b, ty))
    (hm : UStmt.bindCall x g args ∈ (fnAt u c).body)
    (hU : UmfangB Γ fn ns) (σ σ' : World (declOf u)) (ρ : Env (declOf u) Γ)
    (s : Gabbro.Body.State) (hW : WGRel u σ s.world)
    (hL : PositionalLRel fn ns.active 0 ρ s.local')
    (v : ErgVal (declOf u) ((declOf u).erg k.callee))
    (hR : R k.callee (σ.lese Λ k.args.orte)
      (evalArgs (σ.lese Λ k.args.orte) k.args (σ.lese Λ k.args.orte) ρ) = .ok σ' v) :
    ∃ A s', Strecke_G u C A s s' [b] ∧ WGRel u σ' s'.world ∧
      PositionalLRel (fn.mitTy x ty) (ns.push x).active 0 (Env.cons (ergWert he v) ρ) s'.local' := by
  obtain ⟨hi, _, _⟩ := lowRufKopf_ok hk
  have hf : fnSuch u g = some (fnAt u k.callee) := fnIdx_find _ _ _ hi
  have hd := callee_getragen_calls S hc (CallsIn.bind hm) hf
  obtain ⟨_, es, sh, hsh, _, hbst, hev, hLt, hpre⟩ :=
    resultCall_sim hk he hb hU S.tab (S.namen k.callee hd) (S.art k.callee hd).2.1 σ ρ s hW hL
  let σr := σ.lese Λ k.args.orte
  let envA := evalArgs σr k.args σr ρ
  let t : Gabbro.Body.State :=
    ⟨s.world, Gabbro.Body.bindAll ((fnAt u k.callee).params.map (·.1)) (envVals envA) (fun _ => .absent)⟩
  have hWr : WGRel u σr t.world := wgrel_same u rfl rfl hW
  cases hw : writesU (fnAt u k.callee) with
  | nil =>
    have hclock : callClock ∈ writesU (fnAt u k.callee) := by simp [writesU]
    rw [hw] at hclock
    cases hclock
  | cons w ws =>
    let entry : Eintrag := ⟨g, t, antwort w σ' t (ergValOf ((declOf u).erg k.callee) v)⟩
    let s' : Gabbro.Body.State :=
      ⟨bump w (encG u σ' s.world), Gabbro.Body.bindLocal s.local' (ns.fresh x) (valOf ty (ergWert he v))⟩
    have hgeist : geistVon u g = some w := by simp [geistVon, hf, hw]
    have hclock : gz w s'.world = gz w s.world + 1 := by
      change gz w (bump w (encG u σ' s.world)) = _
      rw [gz_bump_self, gz_enc]
    refine ⟨[entry], s', {
      gut := fun e hm => by
        rcases List.mem_singleton.mp hm with rfl
        exact eintrag_gut_teil G S R hRR k.callee hd σr σ' envA v hR t hWr hLt w ws hw g hf
      oben := fun e hm => by
        rcases List.mem_singleton.mp hm with rfl
        exact ⟨w, hgeist, Int.le_refl _⟩
      unten := fun e hm => by
        rcases List.mem_singleton.mp hm with rfl
        refine ⟨w, hgeist, ?_⟩
        change gz w s.world < gz w s'.world
        rw [hclock]
        omega
      schluessel := List.pairwise_singleton _ _
      mono := fun w' => by
        have hh := gz_bump_le w w' (encG u σ' s.world)
        rw [gz_enc] at hh
        exact hh
      lauf := fun ρB hT _ => by
        have hentry : ρB g t = entry.aus := hT entry (List.mem_singleton_self _)
        have hstep : Gabbro.Body.step ρB b s = .running s' := by
          rw [hbst]
          simp only [Gabbro.Body.step, hev, hpre]
          rw [hentry]
          simp only [entry, antwort, ergValOf_wert he v] <;> rfl
        simp only [Gabbro.Body.exec, hstep] },
      wgrel_bump w (wgrel_enc u σ' s.world),
      hL.pushTy x (ns.fresh x) (BodyNames.fresh_not_active hU.valid x) hsh (ergWert he v)⟩

theorem blockZiel_bindCall_ok_G {loopMode : Bool} {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
    {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}
    {Γ : Ctx} {Λ Λ' : List (Res (declOf u))} {fn : UFn} {ns : BodyNames}
    {x : String} {ty : Ty} {sh : Gabbro.Body.Shape} (ht : shapeOfTy ty = some sh)
    (head : RufKopf u c Γ Λ) (he : (declOf u).erg head.callee = some ty)
    (hr : (declOf u).gruende head.callee = 0)
    (rest : Block (declOf u) (verOf u c) loopMode (ty :: Γ) (nach (declOf u) head.callee Λ) Λ')
    {σ σ₁ : World (declOf u)} {ρ : Env (declOf u) Γ}
    {v : ErgVal (declOf u) ((declOf u).erg head.callee)}
    (hR : R head.callee (σ.lese Λ head.args.orte)
      (evalArgs (σ.lese Λ head.args.orte) head.args (σ.lese Λ head.args.orte) ρ) = .ok σ₁ v)
    {A : List Eintrag} {s s₁ : Gabbro.Body.State} {b : Gabbro.Body.Stmt}
    {ys : List Gabbro.Body.Stmt} (hS : Strecke_G u C A s s₁ [b])
    (ih : BlockZiel_G u C c O passes R (fn.mitTy x ty) (ns.push x).active rest σ₁
      (Env.cons (ergWert he v) ρ) s₁ ys) :
    BlockZiel_G u C c O passes R fn ns.active
      (.bindCall head.callee head.args he head.hp hr rest) σ ρ s (b :: ys) := by
  refine ⟨fun err h => ?_, fun σ' v' h => ?_, fun σ' ρ' h => ?_⟩
  · simp only [execBlock, hR] at h
    exact ih.1 err (schrumpfZ_logik h)
  · simp only [execBlock, hR] at h
    obtain ⟨A₂, hret⟩ := ih.2.1 σ' v' (schrumpfZ_zurueck h)
    refine ⟨A ++ A₂, ?_⟩
    rw [← List.singleton_append]
    exact RueckZ_G.nach hS hret
  · simp only [execBlock, hR] at h
    obtain ⟨ρ'', hin, rfl⟩ := schrumpfZ_ok h
    obtain ⟨A₂, s₂, hS₂, hW₂, hL₂⟩ := ih.2.2 σ' ρ'' hin
    exact ⟨A ++ A₂, s₂, Strecke_G.cons hS hS₂, hW₂, hL₂.tailTy ht⟩

end Gabbro.Bruecke
