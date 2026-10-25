/- Part 3 of 12 of `RufAdaequatG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T2

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
  | _ => simp [Ausgang.schrumpf] at h

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
  | _ => simp [Ausgang.mapWelt] at h

theorem mapWelt_zurueck {o : Ausgang V l Γ} {g : World D → World D} {σ' : World D}
    {v : ErgVal D V.erg} (h : o.mapWelt g = .zurueck σ' v) :
    ∃ σ1, o = .zurueck σ1 v ∧ σ' = g σ1 := by
  cases o with
  | zurueck σ w =>
      simp only [Ausgang.mapWelt, Ausgang.zurueck.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨σ, rfl, rfl⟩
  | _ => simp [Ausgang.mapWelt] at h

theorem zuAusgang_ne_ok (o : EndAusgang V l Γ) (σ' : World D) (ρ' : Env D Γ) :
    o.zuAusgang ≠ .ok σ' ρ' := by
  cases o <;> simp [EndAusgang.zuAusgang]

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
  all_goals simp at h

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


mutual

theorem stmtOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtG A mr s →
    SimOkS P O passes f fn stapel rho s0 log A s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignSlotRef r t ht ho f' e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignSlotRef _ r t ht ho f' e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattOk P O passes f fn stapel rho s0 log A (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk t ht _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk e he _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onOption o p a, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk p hp _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hv
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk a ha _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, Λ₀, _, .onTag v arms, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsOk arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = w
        at hex hsim
      obtain ⟨c, b, nutz⟩ := w
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨w', hw'⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ hw' M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onWhy r arms, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes keinRuf arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := grundOk arms ha _ _ _ _ _ hex M1 _ hZ1
        (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .call .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .locks L hr body, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hAL, hb⟩ := hs.locks_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨σ1, hb1, rfl⟩ := mapWelt_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_locks (P := P) (O := O) (passes := passes) hZ.1
        L hr body rest k ρ rfl hΛ (hA L hAL)
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk body hb _ _ _ _ hb1 M1 _ hZ1
        (heldGenau_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      have hW2 := hZ2.welt
      obtain ⟨M3, hs3, hZ3⟩ := w_freiGib (P := P) (O := O) (passes := passes) hZ2.1
        L (.dann rest k) ρ' rfl
      rw [hW2] at hZ3
      exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        offen_gibt_nimmt σ σ1 L ho2⟩
  | _, _, _, _, _, .breaking i body, hs => by
      intro σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk body hb _ _ _ _ hex M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .traverse .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .retry .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .forever .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .ret .., _ => by
      intro σ σ' ρ ρ' hex
      simp [execStmt] at hex
  | _, _, _, _, _, .retWhy .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .leave .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])
  | _, _, _, _, _, .next .., hs => by exact absurd hs.art (by simp [Stmt.gArt, Stmt.blattArt])

theorem blockOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockG A mr b →
    SimOkB P O passes f fn stapel rho s0 log A b
  | _, _, _, _, _, .nil, _ => by
      intro σ σ' ρ ρ' hex M k hZ _ _
      simp only [execBlock, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      have hW := hZ.welt
      obtain ⟨M1, hs1, hZ1⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ.1 k ρ rfl
      rw [hW] at hZ1
      exact ⟨M1, RufLaufG.einzeln hs1, hZ1, rfl⟩
  | _, _, _, _, _, .cons s rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      obtain ⟨σ1, ρ1, hs1, hr1⟩ := execBlock_cons_ok O passes keinRuf s rest hex
      obtain ⟨M1, hl1, hZ1, ho1⟩ := stmtOk s hs _ _ _ _ hs1 M rest k hZ hΛ hA
      have hΛ1 := heldGenau_iff (s.held_iff) hΛ
      rw [← ho1] at hΛ1
      obtain ⟨M2, hl2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hr1 M1 k hZ1 hΛ1 (hA.lauf hl1)
      exact ⟨M2, hl1.trans hl2, hZ2, by rw [ho2, ho1]⟩
  | _, _, _, _, _, .bind e rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
        (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
      exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .bindCall .., hb => by cases hb
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by cases hb
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .regRead r hk rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hzs
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
          rw [hW] at hZ1
          obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
            hΛ (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
          exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
        · cases hex
      · cases hex
  | _, _, _, _, _, .regReadElse r hk zusage sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLiesElse_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hw0
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl v (by rw [hW]; exact hv)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
            (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
          exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]; rfl⟩
        · exact absurd hex (zuAusgang_ne_ok _ _ _)
      · cases hex
  | _, _, _, _, _, .awaits g payload hp hL hat rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]; rfl⟩
      · cases hex
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw'⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw' M1 _ hZ1
        (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
      exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, herw.offen]⟩
  | _, _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.narrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .check c sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.pruefung_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hex M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .float op a b lo hi rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .floatLit q lo hi rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl v hv
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          hΛ (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
      · cases hex
  | _, _, _, _, _, .floatOf e lo hi rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .floatNarrow e lo hi sonst rest, hb => by
      intro σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitNarrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes)
          hZ.1 e lo hi sonst rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, hr2, hZ2, ho2⟩ := blockOk rest hr _ _ _ _ hw M1 _ hZ1
          (heldGenau_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOk P O passes f fn stapel rho s0 log hZ2
        exact ⟨M3, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)

theorem armsOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsG A mr arms → ∀ (v : Wert D (.sum cs)),
    SimOkB P O passes f fn stapel rho s0 log A (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockOk b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsOk rest ha.cons_inv.2 _

theorem grundOk : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsG A mr arms →
    ∀ (r : Fin n), SimOkB P O passes f fn stapel rho s0 log A (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockOk b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundOk rest ha.cons_inv.2 _

end

end SimOk

end Gabbro.Grammatik
