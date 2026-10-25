import Grammatik.Zielsatz.Einbettung.Schleifen

/-!
  File:      Grammatik/Zielsatz/Einbettung/Werkzeug.lean
  Subject:   The small facts the simulation of a body uses (stage E2c, part 4).

  Transported syntax runs as the syntax (`exec_nachΛ`, `execBlock_umΓ`, ...); a raw answer of a
  pointer-free type fits in `D'` exactly when it fits in `D` (`einpassen_E`); a callee's or an
  axiom's result, bound to a name, is the same value on both sides (`ergWert_ergZ`,
  `bindAxiom_wert`); a register answer and its promise (`regLies_wert`); the indices of a table
  and of its image (`alleIndizes_bild`); a foreign answer's world under the keys (`inv_antwort`);
  a boundary check (`pruef_sim`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

/-! ## Transported syntax -/

section Transport

variable {D₀ : Deklaration} (S : SperrInv D₀) (O : Orakel D₀) (U : Umwelt D₀) (A : AUmwelt D₀)
  (passes : Nat) (R : ∀ f : D₀.Fn, World D₀ → Env D₀ (D₀.params f) → RufAusgang f)
  {V : Vertrag D₀} {l : Bool}

theorem exec_nachΛ {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D₀)} (h : Λ₁ = Λ₂) (s : Stmt D₀ V l Γ Λ Λ₁)
    (σ : World D₀) (ρ : Env D₀ Γ) :
    execStmtHA S O U A passes R (Stmt.nachΛ h s) σ ρ = execStmtHA S O U A passes R s σ ρ := by
  subst h; rfl

theorem execBlock_vorΛ {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D₀)} (h : Λ₁ = Λ₂) (b : Block D₀ V l Γ Λ₁ Λ')
    (σ : World D₀) (ρ : Env D₀ Γ) :
    execBlockHA S O U A passes R (Block.vorΛ h b) σ ρ = execBlockHA S O U A passes R b σ ρ := by
  subst h; rfl

theorem execEnd_umΛ {Γ : Ctx} {Λ₁ Λ₂ : List (Res D₀)} (h : Λ₁ = Λ₂) (b : Endblock D₀ V l Γ Λ₁)
    (σ : World D₀) (ρ : Env D₀ Γ) :
    execEndHA S O U A passes R (Endblock.umΛ h b) σ ρ = execEndHA S O U A passes R b σ ρ := by
  subst h; rfl

theorem execBlock_umΓ {Γ Γ' : Ctx} {Λ Λ' : List (Res D₀)} (h : Γ = Γ') (b : Block D₀ V l Γ Λ Λ')
    (σ : World D₀) (ρ : Env D₀ Γ') :
    execBlockHA S O U A passes R (Block.umΓ h b) σ ρ =
      castAus h (execBlockHA S O U A passes R b σ (castE h.symm ρ)) := by
  subst h; rfl

theorem execEnd_umΓ {Γ Γ' : Ctx} {Λ : List (Res D₀)} (h : Γ = Γ') (b : Endblock D₀ V l Γ Λ)
    (σ : World D₀) (ρ : Env D₀ Γ') :
    execEndHA S O U A passes R (Endblock.umΓ h b) σ ρ =
      castEnd h (execEndHA S O U A passes R b σ (castE h.symm ρ)) := by
  subst h; rfl

theorem eval_umΓ {Γ Γ' : Ctx} {Λ : List (Res D₀)} {τ : Ty} (h : Γ = Γ') (e : Expr D₀ Γ Λ τ)
    (σ₀ σ : World D₀) (ρ : Env D₀ Γ') : eval σ₀ (Expr.umΓ h e) σ ρ = eval σ₀ e σ (castE h.symm ρ) := by
  subst h; rfl

theorem evalArgs_umτs {Γ : Ctx} {Λ : List (Res D₀)} {τs τs' : List Ty} (h : τs = τs')
    (a : Args D₀ Γ Λ τs) (σ₀ σ : World D₀) (ρ : Env D₀ Γ) :
    evalArgs σ₀ (Args.umτs h a) σ ρ = castE h (evalArgs σ₀ a σ ρ) := by
  subst h; rfl

end Transport

namespace Einbettung

variable (E : Einbettung D D')

/-! ## Raw answers -/

/-- **A raw answer of a pointer-free type** fits in `D'` exactly as in `D`. -/
theorem einpassen_E (z : Int → Option D.Fn) (z' : Int → Option D'.Fn) :
    ∀ (τ : Ty), τ.zeigerfrei = true → ∀ n : Int,
      einpassen z' (E.tyE τ) n = (einpassen z τ n).map (E.valE τ)
  | .int lo hi, _, n => by by_cases h : lo ≤ n ∧ n ≤ hi <;> (simp only [einpassen, h, dite_true, dite_false, not_false_eq_true]) <;> rfl
  | .bool, _, n => by rfl
  | .opt m, _, n => by
      by_cases h1 : 0 ≤ n ∧ n ≤ m - 1
      · simp only [einpassen, h1, dite_true, and_self]; rfl
      · by_cases h2 : n < 0 <;> (simp only [einpassen, h1, h2, dite_false, ite_true, ite_false, not_false_eq_true]) <;> rfl
  | .sum cs, _, n => by
      show summePasst cs n = Option.map _ (summePasst cs n)
      cases summePasst cs n <;> rfl
  | .why m, _, n => by by_cases h : 0 ≤ n ∧ n < m <;> (simp only [einpassen, h, dite_true, dite_false, not_false_eq_true]) <;> rfl
  | .never, _, n => rfl
  | .fl lo hi, _, n => by
      show gleitWortPasst lo hi n = Option.map _ (gleitWortPasst lo hi n)
      cases gleitWortPasst lo hi n <;> rfl
  | .fnptr _, h, _ => absurd h (by simp [Ty.zeigerfrei])
  | .ptr t rw, _, n => rfl
  | .ref t, _, n => by by_cases h : 0 ≤ n <;> (simp only [einpassen, h, dite_true, dite_false, not_false_eq_true]) <;> rfl

/-- A register answer, on both sides. -/
theorem regLies_wert (hZ : E.Rueck) (z : Int → Option D.Fn) (z' : Int → Option D'.Fn)
    (r : D.Reg) (n : Int) (hr : D'.rtyp (E.reg r) = E.tyE (D.rtyp r)) :
    (einpassen z (D.rtyp r) n = Option.none → einpassen z' (D'.rtyp (E.reg r)) n = Option.none) ∧
    ∀ v, einpassen z (D.rtyp r) n = some v →
      einpassen z' (D'.rtyp (E.reg r)) n = some (hr.symm ▸ E.valE _ v) := by
  have e := E.einpassen_E z z' (D.rtyp r) (hZ.rtypFrei r) n
  revert hr
  generalize D'.rtyp (E.reg r) = T'
  intro hr
  subst hr
  refine ⟨fun h => by rw [e, h]; rfl, fun v h => by rw [e, h]; rfl⟩

/-- A result of a pointer-free type fits in `D'` exactly as in `D`. -/
theorem einpassenErg_E (z : Int → Option D.Fn) (z' : Int → Option D'.Fn) :
    ∀ (e : Option Ty), (∀ τ, e = some τ → τ.zeigerfrei = true) → ∀ n : Int,
      einpassenErg z' (e.map E.tyE) n = (einpassenErg z e n).map (E.ergE e)
  | none, _, _ => rfl
  | some τ, hz, n => E.einpassen_E z z' τ (hz τ rfl) n

/-- An axiom's result, on both sides. -/
theorem axiom_wert (hZ : E.Rueck) (z : Int → Option D.Fn) (z' : Int → Option D'.Fn)
    (a : D.Ax) (n : Int) (ha : D'.aerg (E.ax a) = (D.aerg a).map E.tyE) :
    einpassenErg z' (D'.aerg (E.ax a)) n =
      (einpassenErg z (D.aerg a) n).map (fun v => castV ha.symm (E.ergE (D.aerg a) v)) := by
  have hz := hZ.aergFrei a
  revert ha
  generalize D'.aerg (E.ax a) = e'
  intro ha
  subst ha
  rw [E.einpassenErg_E z z' _ hz n]
  rfl

/-- A fallible axiom's result (value or reason), on both sides. -/
theorem axiomSonst_wert (hZ : E.Rueck) (z : Int → Option D.Fn) (z' : Int → Option D'.Fn)
    (a : D.Ax) (n : Int) (ha : D'.aerg (E.ax a) = (D.aerg a).map E.tyE)
    (hg : D'.agruende (E.ax a) = D.agruende a) :
    sonstPasst z' (D'.aerg (E.ax a)) (D'.agruende (E.ax a)) n =
      match sonstPasst z (D.aerg a) (D.agruende a) n with
      | Option.none => Option.none
      | Option.some (Sum.inl v) => Option.some (Sum.inl (castV ha.symm (E.ergE (D.aerg a) v)))
      | Option.some (Sum.inr r) => Option.some (Sum.inr (Fin.cast hg.symm r)) := by
  have hz := hZ.aergFrei a
  revert ha hg
  generalize D'.aerg (E.ax a) = e'
  generalize D'.agruende (E.ax a) = m'
  intro ha hg
  subst ha; subst hg
  simp only [sonstPasst]
  by_cases t0 : n % ((D.agruende a : Int) + 1) = 0
  · simp only [t0, if_true, E.einpassenErg_E z z' _ hz]
    cases einpassenErg z (D.aerg a) (n / ((D.agruende a : Int) + 1)) <;> rfl
  · simp only [t0, if_false]
    by_cases t1 : 0 < n % ((D.agruende a : Int) + 1) ∧ n % ((D.agruende a : Int) + 1) ≤ D.agruende a
    · simp only [t1, dif_pos, and_self]; rfl
    · simp only [t1, dif_neg, not_false_eq_true]

/-! ## Results bound to a name -/

theorem ergWert_ergZ (hZ : E.Rueck) {τ : Ty} {e e' : Option Ty} (heq : e.map E.tyE = e')
    (he : e = some τ) (he' : e' = some (E.tyE τ)) (v' : ErgVal D' e') :
    E.VRel hZ τ (ergWert he (E.ergZ hZ e (castV heq.symm v'))) (ergWert he' v') := by
  subst heq; subst he
  exact E.vrel_valZ hZ τ v'

theorem ergWert_ergE (hZ : E.Rueck) {τ : Ty} {e e' : Option Ty} (heq : e' = e.map E.tyE)
    (he : e = some τ) (he' : e' = some (E.tyE τ)) (v : ErgVal D e) :
    E.VRel hZ τ (ergWert he v) (ergWert he' (castV heq.symm (E.ergE e v))) := by
  subst heq; subst he; exact E.vrel_valE hZ τ v

theorem castW_why {a b : Nat} (h : Ty.why a = Ty.why b) (r : Fin a) :
    castW (D := D') h r = Fin.cast (Ty.why.inj h) r := by
  obtain rfl := Ty.why.inj h; rfl

/-! ## Indices -/

/-- The indices of a table's image are the table's. -/
theorem alleIndizes_bild {c c' : Int} (hc : c' = c) :
    alleIndizes c' =
      (alleIndizes c).map (fun k => castW (D := D') (show Ty.index c = Ty.index c' by rw [hc]) k) := by
  subst hc
  exact (List.map_id' _).symm

/-! ## Foreign answers -/

theorem inv_antwort (hZ : E.Rueck) {pad : List (Ereignis D)} (hp : PadOk pad)
    {M : Keys D D'} {σ : World D} {σ' : World D'} (h : E.Inv hZ M σ σ') (W : World D') :
    E.Inv hZ M (E.antwortWelt hZ pad σ W) W :=
  h.wachs E (E.antwortWelt_laenge hZ hp σ W) (E.treu_antwortWelt hZ pad σ W)

/-! ## Reads with an expression -/

/-- **A read and an evaluation**: the read events, the key, the atomic answer; then every
    expression of `D` evaluates as its image in the worlds after. -/
theorem lese_eval (hZ : E.Rueck) {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (T : D.Tab ⊕ D.Glob → Prop) {T' : D'.Tab ⊕ D'.Glob → Prop}
    {A' : AUmwelt D'} (hA' : HavocA T' A') (hT : ∀ c, T' (E.ortE c) → T c)
    (Λ : List (Res D)) (Λ' : List (Res D')) (X : List (D.Tab ⊕ D.Glob)) :
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → leseA (E.aumweltΦ hZ Φ T A') σ Λ X = σ₁) ∧
      E.Inv hZ M₁ σ₁ (leseA A' σ' Λ' (X.map E.ortE)) ∧
      ∀ {Γ : Ctx} {Λ₀ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ₀ τ) (ρ : Env D Γ)
        (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' →
        E.VRel hZ τ (eval σ₁ e σ₁ ρ)
          (eval (leseA A' σ' Λ' (X.map E.ortE)) (exE E e) (leseA A' σ' Λ' (X.map E.ortE)) ρ') := by
  obtain ⟨M₁, σ₁, hs, hΦ, hI⟩ := E.lese_schritt h T hA' hT Λ Λ' X
  exact ⟨M₁, σ₁, hs, hΦ, hI, fun e ρ ρ' hρ => E.eval_exE hZ hI.treu hI.treu e ρ ρ' hρ⟩

end Einbettung

end Gabbro.Grammatik.Einbettung
