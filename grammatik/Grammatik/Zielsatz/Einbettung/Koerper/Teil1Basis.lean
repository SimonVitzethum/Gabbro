module
public import Grammatik.Zielsatz.Einbettung.Simulation
@[expose] public section


/-!
  File:      Grammatik/Zielsatz/Einbettung/Koerper.lean
  Subject:   **The simulation, form by form** (stage E2c): every statement, block, end block and
             arm list of `D` runs beside its image (`sim_stmt`, `sim_block`, `sim_end`, `sim_arms`,
             `sim_grund`).
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

theorem ortE_inl (t : D.Tab) : (Sum.inl (E.tab t) : D'.Tab ⊕ D'.Glob) = E.ortE (.inl t) := by rfl
theorem ortE_inr (g : D.Glob) : (Sum.inr (E.glob g) : D'.Tab ⊕ D'.Glob) = E.ortE (.inr g) := by rfl

theorem aparamsUm_falt (a : D.Ax) (ρ : Env D (D.aparams a)) :
    castE (E.aparams a).symm (E.envE ρ) = E.aparamsUm a ρ := by rfl

variable (hZ : E.Rueck) (hS : E.SigTreu) (pad : List (Ereignis D)) (S : SperrInv D)
  (T : D.Tab ⊕ D.Glob → Prop) (S' : SperrInv D') (T' : D'.Tab ⊕ D'.Glob → Prop) (O' : Orakel D')
  (U' : Umwelt D') (A' : AUmwelt D') (passes : Nat)
  (R' : ∀ f : D'.Fn, World D' → Env D' (D'.params f) → RufAusgang f)

/-- **A call through the keys**: the pair before the call as a main key, the callee of `D'` and
    its arguments as a call key; the induced handler answers as the `D'`-callee there, and every
    answer world is a world beside its restriction. -/
theorem ruf_schritt {M : Keys D D'} {σ : World D} {σ' : World D'} (hp : PadOk pad)
    (h : E.Inv hZ M σ σ') (g : D.Fn) (ρa : Env D (D.params g)) (f' : D'.Fn)
    (a' : Env D' (D'.params f')) (hr : E.EnvR hZ ρa a') (hk : E.Konform hZ g f') :
    ∃ M₁ : Keys D D', Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → E.rufΦ hZ hS pad Φ R' g σ ρa =
        E.antwortR hZ pad g σ (konform_sig hS hk).2.1 (konform_sig hS hk).2.2 (R' f' σ' a')) ∧
      ∀ W, E.Inv hZ M₁ (E.antwortWelt hZ pad σ W) W := by
  refine ⟨⟨(σ, σ') :: M.haupt, M.atom, (σ, ⟨f', a'⟩) :: M.ruf⟩,
    ⟨fun _ hq => List.mem_cons_of_mem _ hq, fun _ hq => hq, fun _ hq => List.mem_cons_of_mem _ hq⟩,
    fun Φ hP => ?_, fun W => ?_⟩
  · have h1 : Φ.haupt σ = σ' := hP.1 _ List.mem_cons_self
    have h2 : Φ.ruf σ = some ⟨f', a'⟩ := hP.2.2 _ List.mem_cons_self
    unfold rufΦ
    rw [h2]
    simp only []
    rw [dif_pos ⟨hr, hk⟩, h1]
  · exact (h.merke E).merkeRuf E ⟨f', a'⟩ (E.antwortWelt_laenge hZ hp σ W) (E.treu_antwortWelt hZ pad σ W)

/-- An axiom through the keys. -/
theorem ax_schluessel {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (a : D.Ax) (ρa : Env D (D.aparams a)) :
    ∃ M₁ : Keys D D', Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → (E.orakelΦ hZ pad Φ O').wirkt a σ ρa =
        (E.antwortWelt hZ pad σ (O'.wirkt (E.ax a) σ' (E.aparamsUm a ρa)).1,
          (O'.wirkt (E.ax a) σ' (E.aparamsUm a ρa)).2)) ∧ E.Inv hZ M₁ σ σ' := by
  obtain ⟨hk, hs, hΦ⟩ := E.schluessel h
  exact ⟨_, hs, fun Φ hP => by simp only [orakelΦ, hΦ Φ hP], hk⟩

/-- Pointer-free values beside each other are equal through the embedding. -/
theorem frei_eq {τ : Ty} {v : Wert D τ} {v' : Wert D' (E.tyE τ)} (h : E.VRel hZ τ v v')
    (hτ : τ.zeigerfrei = true) : v' = E.valE τ v :=
  (E.vrel_frei hZ τ hτ v v').mp h

/-- **Pointer-free expressions evaluate as their images**, in environments beside each other. -/
theorem frei_alle {σ₁ : World D} {σ₁' : World D'}
    (hev : ∀ {Γ : Ctx} {Λ₀ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ₀ τ) (ρ : Env D Γ)
      (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' →
      E.VRel hZ τ (eval σ₁ e σ₁ ρ) (eval σ₁' (exE E e) σ₁' ρ'))
    {Γ : Ctx} {ρ : Env D Γ} {ρ' : Env D' (Γ.map E.tyE)} (hρ : E.EnvR hZ ρ ρ') :
    ∀ (Λ₀ : List (Res D)) (τ : Ty) (e : Expr D Γ Λ₀ τ), τ.zeigerfrei = true →
      eval σ₁' (exE E e) σ₁' ρ' = E.valE τ (eval σ₁ e σ₁ ρ) :=
  fun _ _ e hτ => E.frei_eq hZ (hev e ρ ρ' hρ) hτ

theorem zf_int {a b : Int} : (Ty.int a b).zeigerfrei = true := by rfl
theorem zf_index {c : Int} : (Ty.index c).zeigerfrei = true := by rfl
theorem zf_bool : Ty.bool.zeigerfrei = true := by rfl
theorem zf_opt {n : Int} : (Ty.opt n).zeigerfrei = true := by rfl
theorem zf_why {n : Nat} : (Ty.why n).zeigerfrei = true := by rfl
theorem zf_fl {lo hi : Int × Int} : (Ty.fl lo hi).zeigerfrei = true := by rfl
theorem zf_ref {n : Nat} : (Ty.ref n).zeigerfrei = true := by rfl

/-- A value written through a type equation, beside its source. -/
theorem vrel_um {τ T' : Ty} (e : T' = E.tyE τ) {v : Wert D τ} {v' : Wert D' (E.tyE τ)}
    (h : E.VRel hZ τ v v') : E.VRel hZ τ v (castW e (castW e.symm v')) := by
  rw [castW_symm]; exact h

/-- **Pointer-free arguments beside each other are equal through the embedding.** -/
theorem envR_eq_frei : ∀ {Γ : Ctx}, (∀ τ ∈ Γ, τ.zeigerfrei = true) →
    ∀ (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE)), E.EnvR hZ ρ ρ' → ρ' = E.envE ρ
  | [], _, .nil, .nil, _ => rfl
  | τ :: Γ, hf, .cons v ρ, .cons v' ρ', h => by
      obtain ⟨⟨e, hv⟩, h2⟩ := h
      rw [castW_self] at hv
      rw [E.frei_eq hZ hv (hf τ List.mem_cons_self),
        envR_eq_frei (fun τ' h' => hf τ' (List.mem_cons_of_mem _ h')) ρ ρ' h2]
      rfl

theorem castW_index_n {D₀ : Deklaration} {c c' : Int} (h : Ty.index c = Ty.index c')
    (v : Wert D₀ (Ty.index c)) : (castW h v).n = v.n := castW_n h v

theorem valE_index_n {c : Int} (v : Wert D (Ty.index c)) : (E.valE (Ty.index c) v).n = v.n := by rfl

theorem umsig_heq {D₀ : Deklaration} {f : D₀.Fn} {n : Nat} (hf : D₀.passt f n = true)
    (ρ : Env D₀ (D₀.sigNr n).params) : HEq (umsig hf ρ) ρ := by
  unfold umsig
  simp only [_root_.id]
  exact cast_heq _ _

theorem castE_heq {D₀ : Deklaration} {Γ Γ' : Ctx} (h : Γ = Γ') (ρ : Env D₀ Γ) : HEq (castE h ρ) ρ := by
  subst h; rfl

theorem envE_heq {Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (ρ₁ : Env D Γ₁) (ρ₂ : Env D Γ₂) (e : HEq ρ₁ ρ₂) :
    HEq (E.envE ρ₁) (E.envE ρ₂) := by
  subst h; cases e; rfl

theorem umsig_castE {D₀ : Deklaration} {f : D₀.Fn} {n : Nat} (hf : D₀.passt f n = true)
    (ρ : Env D₀ (D₀.sigNr n).params) :
    umsig hf ρ = castE (by unfold Deklaration.params; rw [(D₀.passt_sig hf).params]) ρ :=
  eq_of_heq ((umsig_heq hf ρ).trans (castE_heq _ ρ).symm)

/-- **The arguments of an indirect call, on both sides**, beside each other. -/
theorem envR_umsig {f : D.Fn} {f' : D'.Fn} {n n' : Nat} (hf : D.passt f n = true)
    (hf' : D'.passt f' n' = true) (x : Env D (D.sigNr n).params) (x' : Env D' (D'.sigNr n').params)
    (h : E.EnvR hZ x x') : E.EnvR hZ (umsig hf x) (umsig hf' x') := by
  rw [umsig_castE, umsig_castE, E.envR_umD hZ, E.envR_um hZ]; exact h

/-- A slot read through a type equation, on both sides. -/
theorem zahl_cast_n {T T' : Ty} {lo hi : Int} (hτ : T = .int lo hi) (hτ' : T' = .int lo hi)
    (e : T' = E.tyE T) (x : Wert D T) (x' : Wert D' T') (hx : E.VRel hZ T x (castW e x')) :
    (hτ' ▸ x' : Zahl _ _).n = (hτ ▸ x : Zahl _ _).n := by
  subst hτ; subst hτ'
  exact congrArg Zahl.n hx

/-- A state value written through a type equation, on both sides. -/
theorem zahl_cast_wert {T T' : Ty} {lo hi : Int} (hτ : T = .int lo hi) (hτ' : T' = .int lo hi)
    (e : T' = E.tyE T) (z : Zahl lo hi) :
    E.VRel hZ T (hτ ▸ (z : Zahl _ _)) (castW e (hτ' ▸ (z : Zahl _ _))) := by
  subst hτ; subst hτ'; rfl

theorem logikRel_kein {e : Logik D} {e' : Logik D'} (h : ∀ g', e' ≠ .vorbedingung g') :
    LogikRel e e' := fun g' he => absurd he (h g')

theorem wahr_valE (v : Wert D .bool) : wahr? (D := D') (E.valE .bool v) = wahr? v := by rfl

theorem zelle_valE {n : Nat} (v : Wert D (.ref n)) : (E.valE (.ref n) v).zelle = v.zelle := by rfl

@[simp] theorem valE_ref {n : Nat} (v : Wert D (.ref n)) : E.valE (.ref n) v = v := by rfl

theorem orakelΦ_regLies (Φ : Phi D D') (r : D.Reg) (σ : World D) :
    (E.orakelΦ hZ pad Φ O').regLies r σ = O'.regLies (E.reg r) (Φ.haupt σ) := by rfl

theorem orakelΦ_sichtbar (Φ : Phi D D') (g : D.Glob) (σ : World D) (h : (D.gtyp g).zeigerfrei = true) :
    (E.orakelΦ hZ pad Φ O').sichtbar g σ = O'.sichtbar (E.glob g) (Φ.haupt σ) := by
  simp only [orakelΦ, h, if_true]

theorem orakelΦ_zeiger (Φ : Phi D D') :
    (E.orakelΦ hZ pad Φ O').zeiger = fun _ => Option.none := by rfl

/-- A block whose image is transported along its scope. -/
theorem koerperSim_block_um {V : Vertrag D} {l : Bool} {Δ : Ctx} {Δ₁ Δ₂ : Ctx}
    {Λ₁ Λ₂ : List (Res D')} (h : Δ₁ = Δ₂)
    (lauf : Phi D D' → World D → Env D Δ → Ausgang V l Δ)
    (b : Block D' (E.vertragE V) l Δ₁ Λ₁ Λ₂)
    (hs : E.KoerperSim hZ lauf (execBlockHA S' O' U' A' passes R' b)) :
    E.KoerperSim hZ lauf (execBlockHA S' O' U' A' passes R' (Block.umΓ h b)) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um hZ h.symm ρ ρ').mpr hρ)
  refine ⟨M₁, o, hs1, hΦ, ?_⟩
  rw [execBlock_umΓ]
  exact (E.ausRel_um h o _).mpr hR

/-- An end block whose image is transported along its scope. -/
theorem endSim_end_um {V : Vertrag D} {l : Bool} {Δ : Ctx} {Δ₁ Δ₂ : Ctx}
    {Λ₁ : List (Res D')} (h : Δ₁ = Δ₂)
    (lauf : Phi D D' → World D → Env D Δ → EndAusgang V l Δ)
    (b : Endblock D' (E.vertragE V) l Δ₁ Λ₁)
    (hs : E.EndSim hZ lauf (execEndHA S' O' U' A' passes R' b)) :
    E.EndSim hZ lauf (execEndHA S' O' U' A' passes R' (Endblock.umΓ h b)) := by
  intro M σ σ' ρ ρ' hI hρ
  obtain ⟨M₁, o, hs1, hΦ, hR⟩ := hs M σ σ' ρ (castE h.symm ρ') hI ((E.envR_um hZ h.symm ρ ρ').mpr hρ)
  refine ⟨M₁, o, hs1, hΦ, ?_⟩
  rw [execEnd_umΓ]
  exact (E.endRel_um h o _).mpr hR

end Einbettung
end Gabbro.Grammatik.Einbettung
