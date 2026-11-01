module

public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 6. Sequential inversion lemmas -/

section Inversion

variable {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem schrumpf_ok {τ : Ty} {o : Ausgang V l (τ :: Γ)} {σ' : World D} {ρ' : Env D Γ}
    (h : o.schrumpf = .ok σ' ρ') : ∃ v, o = .ok σ' (.cons v ρ') := by
  cases o with
  | ok σ ρ =>
      cases ρ with
      | cons v ρt =>
          simp only [Ausgang.schrumpf, Env.tail, Ausgang.ok.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨v, rfl⟩
  | _ => simp only [Ausgang.schrumpf, reduceCtorEq] at h

theorem schrumpf_zurueck {τ : Ty} {o : Ausgang V l (τ :: Γ)} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.schrumpf = .zurueck σ' v) : o = .zurueck σ' v := by
  cases o <;> simp_all [Ausgang.schrumpf]

theorem endSchrumpf_zurueck {τ : Ty} {o : EndAusgang V l (τ :: Γ)} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.schrumpf = .zurueck σ' v) : o = .zurueck σ' v := by
  cases o <;> simp_all [EndAusgang.schrumpf]

theorem mapWelt_ok {o : Ausgang V l Γ} {g : World D → World D} {σ' : World D}
    {ρ' : Env D Γ} (h : o.mapWelt g = .ok σ' ρ') : ∃ σ1, o = .ok σ1 ρ' ∧ σ' = g σ1 := by
  cases o with
  | ok σ ρ =>
      simp only [Ausgang.mapWelt, Ausgang.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ, rfl, rfl⟩
  | _ => simp only [Ausgang.mapWelt, reduceCtorEq] at h

theorem mapWelt_zurueck {o : Ausgang V l Γ} {g : World D → World D} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.mapWelt g = .zurueck σ' v) :
    ∃ σ1, o = .zurueck σ1 v ∧ σ' = g σ1 := by
  cases o with
  | zurueck σ w =>
      simp only [Ausgang.mapWelt, Ausgang.zurueck.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ, rfl, rfl⟩
  | _ => simp only [Ausgang.mapWelt, reduceCtorEq] at h

theorem zuAusgang_ne_ok (o : EndAusgang V l Γ) (σ' : World D) (ρ' : Env D Γ) :
    o.zuAusgang ≠ .ok σ' ρ' := by
  cases o <;> simp only [EndAusgang.zuAusgang, ne_eq, reduceCtorEq, not_false_eq_true]

theorem zuAusgang_zurueck {o : EndAusgang V l Γ} {σ' : World D} {v : ErgVal D V.erg}
    (h : o.zuAusgang = .zurueck σ' v) : o = .zurueck σ' v := by
  cases o <;> simp_all [EndAusgang.zuAusgang]

theorem execBlock_cons_ok (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    {σ σ' : World D} {ρ ρ' : Env D Γ}
    (h : execBlock O passes R (.cons s rest) σ ρ = .ok σ' ρ') :
    ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
      execBlock O passes R rest σ1 ρ1 = .ok σ' ρ' := by
  simp only [execBlock] at h
  split at h
  · rename_i σ1 ρ1 hs
    exact ⟨σ1, ρ1, hs, h⟩
  · rename_i hne
    exact absurd h (hne σ' ρ')

theorem execBlock_cons_zurueck (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'')
    {σ σ' : World D} {ρ : Env D Γ} {v : ErgVal D V.erg}
    (h : execBlock O passes R (.cons s rest) σ ρ = .zurueck σ' v) :
    execStmt O passes R s σ ρ = .zurueck σ' v ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        execBlock O passes R rest σ1 ρ1 = .zurueck σ' v := by
  simp only [execBlock] at h
  split at h
  · rename_i σ1 ρ1 hs
    exact Or.inr ⟨σ1, ρ1, hs, h⟩
  · exact Or.inl h

theorem execEnd_cons_zurueck (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    {σ σ' : World D} {ρ : Env D Γ} {v : ErgVal D V.erg}
    (h : execEnd O passes R (.cons s rest) σ ρ = .zurueck σ' v) :
    execStmt O passes R s σ ρ = .zurueck σ' v ∨
      ∃ σ1 ρ1, execStmt O passes R s σ ρ = .ok σ1 ρ1 ∧
        execEnd O passes R rest σ1 ρ1 = .zurueck σ' v := by
  simp only [execEnd] at h
  split at h
  · rename_i σ1 ρ1 hs
    exact Or.inr ⟨σ1, ρ1, hs, h⟩
  · rename_i σ1 w hs
    simp only [EndAusgang.zurueck.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl hs
  all_goals simp only [reduceCtorEq] at h

/-- `execArms` runs the arm `armWahlG` selects. -/
theorem execArms_wahl (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
      (σ : World D) (ρ : Env D Γ),
    execArms O passes R arms v σ ρ =
      (execBlock O passes R (armWahlG arms v).2.1 σ (armEnv (armWahlG arms v).2.2 ρ)).schrumpfArm
        (armWahlG arms v).1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArms, armWahlG]
      exact execArms_wahl O passes R rest _ σ ρ

/-- `execGrund` runs the arm `grundWahlG` selects. -/
theorem execGrund_wahl (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrund O passes R arms r σ ρ = execBlock O passes R (grundWahlG arms r) σ ρ
  | _, .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨k + 1, h⟩, σ, ρ => by
      simp only [execGrund, grundWahlG]
      exact execGrund_wahl O passes R rest _ σ ρ

/-- `execGrund_wahl` with the selector typed as a `Wert`, as `execStmt` passes it. -/
theorem execGrund_wahlW (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {Λ Λ' : List (Res D)}
    {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Wert D (.why n)) (σ : World D)
    (ρ : Env D Γ) :
    execGrund O passes R arms r σ ρ = execBlock O passes R (grundWahlG arms r) σ ρ :=
  execGrund_wahl O passes R arms r σ ρ

end Inversion
theorem heldGenau_lese {Λ Λ₀ : List (Res D)} {σ : World D} (os : List (D.Tab ⊕ D.Glob))
    (h : HeldGenau Λ (offen σ.spur)) : HeldGenau Λ (offen (σ.lese Λ₀ os).spur) := by
  rw [(Erw.lese σ Λ₀ os).offen]
  exact h

theorem heldB_lese {bo : Option Int} {Λ Λ₀ : List (Res D)} {σ : World D} (os : List (D.Tab ⊕ D.Glob))
    (h : HeldB bo Λ (offen σ.spur)) : HeldB bo Λ (offen (σ.lese Λ₀ os).spur) := by
  rw [(Erw.lese σ Λ₀ os).offen]
  exact h

theorem heldB_iff {bo : Option Int} {Λ Λ' : List (Res D)} {hs : List D.Lock}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (h : HeldB bo Λ hs) : HeldB bo Λ' hs :=
  ⟨fun L hL => h.1 L ((hm L).mp hL), fun L hL hn => h.2 L hL (fun h' => hn ((hm L).mpr h'))⟩

theorem heldGenau_iff {Λ Λ' : List (Res D)} {hs : List D.Lock}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (h : HeldGenau Λ hs) : HeldGenau Λ' hs := by
  intro L
  rw [hm L]
  exact h L

theorem offen_gibt_nimmt (σ σ1 : World D) (L : D.Lock)
    (h : offen σ1.spur = offen (σ.nimmt L).spur) :
    offen (σ1.gibt L).spur = offen σ.spur := by
  show (offen σ1.spur).erase L = offen σ.spur
  rw [h]
  show (L :: offen σ.spur).erase L = offen σ.spur
  exact List.erase_cons_head L _

/-! ## 7. Normal completion: the machine reaches the continuation -/

section SimOk

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (log : List (RufEreignisF D)) (A : D.Lock → Prop)

/-- Block simulation, normal completion: `dann b k` at `σ, ρ` runs (steps of
    `f` only) to `k` at the world and environment `execBlock` returns. -/
def SimOkB {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ ρ' : Env D Γ), execBlock O passes keinRuf b σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldGenau Λ (offen σ.spur) →
    FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧ ZustandG M' f stapel fn rho s0 log ρ' k σ' ∧
      offen σ'.spur = offen σ.spur

/-- Statement simulation, normal completion: `dann (s; rest) k` runs to
    `dann rest k`. -/
def SimOkS {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (σ σ' : World D) (ρ ρ' : Env D Γ), execStmt O passes keinRuf s σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldGenau Λ (offen σ.spur) → FreiA A M f →
    ∃ M', RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 log ρ' (.dann rest k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- A covered leaf: one `dannBlatt` step. -/
theorem blattOk {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimOkS P O passes f fn stapel rho s0 log A s := by
  intro σ σ' ρ ρ' hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  have herw := h.erw O passes keinRuf σ σ' ρ ρ' hex
  obtain ⟨M', hs, hZ'⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) hZ.1 s rest k ρ
    h.istBlatt rfl hΛ.heldIn σ' ρ' (by rw [hW]; exact hex) (by rw [hW]; exact herw)
  exact ⟨M', RufLaufG.einzeln hs, hZ', herw.offen⟩

/-- A `schrumpf` layer after a sub-block: one `schrumpfVergiss` step. -/
theorem schrumpfOk {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {M : RufMaschineG D} {k : GRest D (vertragVon D fn) l Γ Λ} {v : Wert D τ}
    {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log (.cons v ρ) (.schrumpf k) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧ ZustandG M' f stapel fn rho s0 log ρ k σ := by
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_schrumpf (P := P) (O := O) (passes := passes) hZ.1 k v ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩


end SimOk
end Gabbro.Grammatik
