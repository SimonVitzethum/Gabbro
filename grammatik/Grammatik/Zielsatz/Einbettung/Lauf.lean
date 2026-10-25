import Grammatik.Zielsatz.Einbettung.Handler

/-!
  File:      Grammatik/Zielsatz/Einbettung/Lauf.lean
  Subject:   The relation between a run of `D` and the run of its image, and its single steps
             with a handler (stage E2c, part 2).

  * `EnvR` -- an environment of `D` beside one of `D'`, value by value (the scopes may differ by
    a transport: a field's or a register's type, a table's count).
  * `AusRel` / `EndRel` -- an outcome of `D` beside one of `D'`: the same kind, worlds under the
    keys (`Inv`), environments by `EnvR`, values by `ergE`, a blamed caller to a blamed caller.
  * the steps that ask a handler: an atomic read (`lese_schritt`), a lock move
    (`umwelt_schritt`), and any key (`schluessel`): each puts the current pair among the keys,
    and every map `Φ` that repeats the keys makes the induced handler answer as the `D'`-one.
-/

namespace Gabbro.Grammatik.Einbettung

open Gabbro.Grammatik

variable {D D' : Deklaration}

namespace Einbettung

variable (E : Einbettung D D')

/-! ## Environments -/

/-- An environment of `D` beside one of `D'`. -/
def EnvR : {Γ : Ctx} → Env D Γ → {Γ' : Ctx} → Env D' Γ' → Prop
  | _, .nil, _, .nil => True
  | _, .cons (τ := τ) v ρ, _, .cons (τ := τ') v' ρ' =>
      (∃ h : τ' = E.tyE τ, castW h v' = E.valE τ v) ∧ EnvR ρ ρ'
  | _, _, _, _ => False

theorem envR_envE : ∀ {Γ : Ctx} (ρ : Env D Γ), E.EnvR ρ (E.envE ρ)
  | _, .nil => trivial
  | _, .cons _ ρ => ⟨⟨rfl, rfl⟩, envR_envE ρ⟩

theorem envR_eq : ∀ {Γ : Ctx} (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE)), E.EnvR ρ ρ' → ρ' = E.envE ρ
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons v ρ, .cons v' ρ', h => by
      simp only [EnvR] at h
      obtain ⟨⟨_, hv⟩, hr⟩ := h
      rw [castW_self] at hv
      rw [hv, envR_eq ρ ρ' hr]; rfl

theorem envR_tail {τ τ' : Ty} {Γ Γ' : Ctx} (ρ : Env D (τ :: Γ)) (ρ' : Env D' (τ' :: Γ'))
    (h : E.EnvR ρ ρ') : E.EnvR ρ.tail ρ'.tail := by
  cases ρ with
  | cons v ρ => cases ρ' with
    | cons v' ρ' => exact h.2

theorem envR_cons {τ τ' : Ty} {Γ Γ' : Ctx} {ρ : Env D Γ} {ρ' : Env D' Γ'} (h : E.EnvR ρ ρ')
    (v : Wert D τ) (v' : Wert D' τ') (e : τ' = E.tyE τ) (hv : castW e v' = E.valE τ v) :
    E.EnvR (Env.cons v ρ) (Env.cons v' ρ') := ⟨⟨e, hv⟩, h⟩

theorem envE_set : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (x : Var Γ τ) (v : Wert D τ),
    (E.envE ρ).set (varE E x) (E.valE τ v) = E.envE (ρ.set x v)
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ ρ, .there x, v => by
      show Env.cons _ ((E.envE ρ).set (varE E x) (E.valE _ v)) = _
      rw [envE_set ρ x v]; rfl

/-- Transporting the scope of the `D'`-side keeps the relation. -/
theorem envR_um {Γ : Ctx} {Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (ρ : Env D Γ) (ρ' : Env D' Γ₁) :
    E.EnvR ρ (castE h ρ') ↔ E.EnvR ρ ρ' := by subst h; rfl

/-! ## Outcomes -/

/-- **An outcome of `D` beside one of `D'`**, under the keys `M`. -/
def AusRel (M : Keys D D') {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} :
    Ausgang V l Γ → Ausgang (E.vertragE V) l Γ' → Prop
  | .ok σ ρ, .ok σ' ρ' => E.Inv M σ σ' ∧ E.EnvR ρ ρ'
  | .zurueck σ v, .zurueck σ' v' => E.Inv M σ σ' ∧ v' = E.ergE V.erg v
  | .why σ r, .why σ' r' => E.Inv M σ σ' ∧ r'.val = r.val
  | .leave _ σ ρ, .leave _ σ' ρ' => E.Inv M σ σ' ∧ E.EnvR ρ ρ'
  | .next _ σ ρ, .next _ σ' ρ' => E.Inv M σ σ' ∧ E.EnvR ρ ρ'
  | .logik e, .logik e' => E.LogikRel e e' ∧ E.KeyOk M
  | .hardware _, .hardware _ => True
  | _, _ => False

/-- **An end outcome of `D` beside one of `D'`.** -/
def EndRel (M : Keys D D') {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} :
    EndAusgang V l Γ → EndAusgang (E.vertragE V) l Γ' → Prop
  | .zurueck σ v, .zurueck σ' v' => E.Inv M σ σ' ∧ v' = E.ergE V.erg v
  | .why σ r, .why σ' r' => E.Inv M σ σ' ∧ r'.val = r.val
  | .leave _ σ ρ, .leave _ σ' ρ' => E.Inv M σ σ' ∧ E.EnvR ρ ρ'
  | .next _ σ ρ, .next _ σ' ρ' => E.Inv M σ σ' ∧ E.EnvR ρ ρ'
  | .logik e, .logik e' => E.LogikRel e e' ∧ E.KeyOk M
  | .hardware _, .hardware _ => True
  | _, _ => False

section Rel

variable {M : Keys D D'} {V : Vertrag D} {l : Bool}

theorem ausRel_schrumpf {τ τ' : Ty} {Γ Γ' : Ctx} {o : Ausgang V l (τ :: Γ)}
    {o' : Ausgang (E.vertragE V) l (τ' :: Γ')} (h : E.AusRel M o o') :
    E.AusRel M o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp only [AusRel, Ausgang.schrumpf] at h ⊢ <;>
    first
    | exact ⟨h.1, E.envR_tail _ _ h.2⟩
    | exact h
    | exact h.elim

theorem endRel_schrumpf {τ τ' : Ty} {Γ Γ' : Ctx} {o : EndAusgang V l (τ :: Γ)}
    {o' : EndAusgang (E.vertragE V) l (τ' :: Γ')} (h : E.EndRel M o o') :
    E.EndRel M o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp only [EndRel, EndAusgang.schrumpf] at h ⊢ <;>
    first
    | exact ⟨h.1, E.envR_tail _ _ h.2⟩
    | exact h
    | exact h.elim

theorem endRel_zuAusgang {Γ Γ' : Ctx} {o : EndAusgang V l Γ}
    {o' : EndAusgang (E.vertragE V) l Γ'} (h : E.EndRel M o o') :
    E.AusRel M o.zuAusgang o'.zuAusgang := by
  cases o <;> cases o' <;> simp only [EndRel, AusRel, EndAusgang.zuAusgang] at h ⊢ <;>
    first
    | exact h
    | exact h.elim

/-- Transporting the scope of the `D'`-side keeps the relation. -/
theorem ausRel_um {Γ Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (o : Ausgang V l Γ)
    (o' : Ausgang (E.vertragE V) l Γ₁) :
    E.AusRel M o (castAus h o') ↔ E.AusRel M o o' := by subst h; rfl

theorem endRel_um {Γ Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (o : EndAusgang V l Γ)
    (o' : EndAusgang (E.vertragE V) l Γ₁) :
    E.EndRel M o (castEnd h o') ↔ E.EndRel M o o' := by subst h; rfl

end Rel

/-! ## Carriers and their images -/

theorem ortE_inj : Function.Injective E.ortE := by
  intro a b h
  rcases a with t | g <;> rcases b with t' | g' <;> simp only [ortE, Sum.map_inl, Sum.map_inr,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · rw [E.tab_inj h]
  · rw [E.glob_inj h]

theorem mem_map_ortE {c : D.Tab ⊕ D.Glob} {X : List (D.Tab ⊕ D.Glob)} :
    E.ortE c ∈ X.map E.ortE ↔ c ∈ X :=
  ⟨fun h => by
      obtain ⟨c0, hc0, he⟩ := List.mem_map.mp h
      rw [← E.ortE_inj he]; exact hc0,
    List.mem_map_of_mem⟩

/-- A carrier of `D'` outside the image is in no list of images. -/
theorem fremd_nicht_tab {t' : D'.Tab} (h : E.tabZ t' = none) (X : List (D.Tab ⊕ D.Glob)) :
    (Sum.inl t' : D'.Tab ⊕ D'.Glob) ∉ X.map E.ortE := by
  intro hm
  obtain ⟨c, _, he⟩ := List.mem_map.mp hm
  rcases c with t | g
  · simp only [ortE, Sum.map_inl, Sum.inl.injEq] at he
    rw [← he, E.tabZ_tab] at h; cases h
  · simp only [ortE, Sum.map_inr, reduceCtorEq] at he

theorem fremd_nicht_glob {g' : D'.Glob} (h : E.globZ g' = none) (X : List (D.Tab ⊕ D.Glob)) :
    (Sum.inr g' : D'.Tab ⊕ D'.Glob) ∉ X.map E.ortE := by
  intro hm
  obtain ⟨c, _, he⟩ := List.mem_map.mp hm
  rcases c with t | g
  · simp only [ortE, Sum.map_inl, reduceCtorEq] at he
  · simp only [ortE, Sum.map_inr, Sum.inr.injEq] at he
    rw [← he, E.globZ_glob] at h; cases h

variable (hZ : ZeigerfreiD D)

/-- **A mixed world beside its `D'`-move**: on the carriers `P` the mixed world holds the move's
    memory restricted; elsewhere both keep what they had. -/
theorem treu_misch {σ m : World D} {σ' W' : World D'} (hσ : E.Treu σ.speicher σ')
    (P : D.Tab ⊕ D.Glob → Prop)
    (hin : ∀ c, P c → TraegerGleich m.speicher (E.speicherZ hZ W'.speicher) c)
    (hout : ∀ c, ¬ P c → TraegerGleich m.speicher σ.speicher c ∧
      TraegerGleich W'.speicher σ'.speicher (E.ortE c)) :
    E.Treu m.speicher W' := by
  refine ⟨fun t k f => ?_, fun g => ?_⟩
  · by_cases hp : P (.inl t)
    · have e : m.slots t = (E.speicherZ hZ W'.speicher).slots t := hin _ hp
      show castW _ (W'.slots (E.tab t) k (E.feld t f)) = E.valE _ (m.slots t k f)
      rw [e]; exact (E.valE_valZ _ _ _).symm
    · obtain ⟨e1, e2⟩ := hout _ hp
      have e1 : m.slots t = σ.slots t := e1
      have e2 : W'.slots (E.tab t) = σ'.slots (E.tab t) := e2
      show castW _ (W'.slots (E.tab t) k (E.feld t f)) = E.valE _ (m.slots t k f)
      rw [e1, e2]; exact hσ.1 t k f
  · by_cases hp : P (.inr g)
    · have e : m.globs g = (E.speicherZ hZ W'.speicher).globs g := hin _ hp
      show castW _ (W'.globs (E.glob g)) = E.valE _ (m.globs g)
      rw [e]; exact (E.valE_valZ _ _ _).symm
    · obtain ⟨e1, e2⟩ := hout _ hp
      have e1 : m.globs g = σ.globs g := e1
      have e2 : W'.globs (E.glob g) = σ'.globs (E.glob g) := e2
      show castW _ (W'.globs (E.glob g)) = E.valE _ (m.globs g)
      rw [e1, e2]; exact hσ.2 g

/-! ## Keys -/

/-- `Φ` repeats the keys. -/
def Passt (Φ : Phi D D') (M : Keys D D') : Prop :=
  (∀ p ∈ M.haupt, Φ.haupt p.1 = p.2) ∧ (∀ p ∈ M.atom, Φ.atom p.1 = p.2)

theorem passt_teil {Φ : Phi D D'} {M M' : Keys D D'} (h : Passt Φ M') (hs : Teil M M') : Passt Φ M :=
  ⟨fun p hp => h.1 p (hs.1 p hp), fun p hp => h.2 p (hs.2 p hp)⟩

/-- **The current pair as a main key.** -/
theorem schluessel {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') :
    E.Inv ⟨(σ, σ') :: M.haupt, M.atom⟩ σ σ' ∧ Teil M ⟨(σ, σ') :: M.haupt, M.atom⟩ ∧
      ∀ Φ, Passt Φ ⟨(σ, σ') :: M.haupt, M.atom⟩ → Φ.haupt σ = σ' :=
  ⟨h.merke E, ⟨fun _ hp => List.mem_cons_of_mem _ hp, fun _ hp => hp⟩,
    fun _ hP => hP.1 _ List.mem_cons_self⟩

theorem mischT_nil (T : D.Tab ⊕ D.Glob → Prop) (σ : World D) (s : Speicher D) :
    mischT T [] σ s = σ :=
  world_ext (fun c => mischT_aussen σ s (fun h => absurd h.1 List.not_mem_nil)) rfl

theorem havocA_nil {T' : D'.Tab ⊕ D'.Glob → Prop} {A' : AUmwelt D'} (hA' : HavocA T' A')
    (σ' : World D') : A' [] σ' = σ' :=
  world_ext (fun c => (hA' [] σ').2 c (fun h => absurd h.1 List.not_mem_nil)) (hA' [] σ').1

/-- **An atomic read.** The read events on both sides, the pair after them as an atomic key, and
    the `D'`-environment's answer: the induced environment answers the same at the key. A read of
    nothing asks nothing. -/
theorem lese_schritt {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (T : D.Tab ⊕ D.Glob → Prop) {T' : D'.Tab ⊕ D'.Glob → Prop}
    {A' : AUmwelt D'} (hA' : HavocA T' A') (hT : ∀ c, T' (E.ortE c) → T c)
    (Λ : List (Res D)) (Λ' : List (Res D')) (X : List (D.Tab ⊕ D.Glob)) :
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → leseA (E.aumweltΦ hZ Φ T A') σ Λ X = σ₁) ∧
      E.Inv M₁ σ₁ (leseA A' σ' Λ' (X.map E.ortE)) := by
  cases X with
  | nil =>
      refine ⟨M, σ, teil_refl M, fun Φ _ => ?_, ?_⟩
      · show mischT T [] (σ.lese Λ []) _ = σ
        rw [mischT_nil, lese_nil]
      · show E.Inv M σ (A' [] (σ'.lese Λ' []))
        rw [havocA_nil hA', lese_nil]; exact h
  | cons x X =>
      have hl := h.lese E Λ Λ' (x :: X)
      have hgr : σ.spur.length < (σ.lese Λ (x :: X)).spur.length := by
        rw [lese_laenge]; simp
      have hk := hl.merkeA E (fun p hp => Nat.lt_of_le_of_lt (h.aKurz p hp) hgr)
      let σl := σ.lese Λ (x :: X)
      let σl' := σ'.lese Λ' ((x :: X).map E.ortE)
      let W' := A' ((x :: X).map E.ortE) σl'
      refine ⟨⟨M.haupt, (σl, σl') :: M.atom⟩, mischT T (x :: X) σl (E.speicherZ hZ W'.speicher),
        ⟨fun _ hp => hp, fun _ hp => List.mem_cons_of_mem _ hp⟩, ?_, ?_⟩
      · intro Φ hP
        show mischT T (x :: X) σl (E.speicherZ hZ (A' ((x :: X).map E.ortE) (Φ.atom σl)).speicher) = _
        rw [hP.2 _ List.mem_cons_self]
      · have ht : E.Treu (mischT T (x :: X) σl (E.speicherZ hZ W'.speicher)).speicher W' :=
          E.treu_misch hZ hk.treu (fun c => c ∈ x :: X ∧ T c) (fun c hc => mischT_innen σl _ hc)
            (fun c hc => ⟨mischT_aussen σl _ hc, (hA' _ σl').2 _ fun ⟨h1, h2⟩ =>
              hc ⟨E.mem_map_ortE.mp h1, hT c h2⟩⟩)
        refine ⟨ht, hk.eintrag, hk.kurz, fun p hp he => absurd he (Nat.ne_of_lt ?_), hk.funk,
          hk.aEintrag, hk.aKurz, hk.aFunk⟩
        exact Nat.lt_of_le_of_lt (h.kurz p hp) hgr

/-- **A lock move and the take.** The pair at the acquire as a main key, the `D'`-move's answer
    (the induced move answers the same there, the protected carriers of the image lock being the
    images), then the take event on both sides. -/
theorem umwelt_schritt {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv M σ σ') (S : SperrInv D) {S' : SperrInv D'} {U' : Umwelt D'} (hU' : HavocOk S' U')
    (hSo : ∀ L, S'.orte (E.lock L) = (S.orte L).map E.ortE) (L : D.Lock) :
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → E.umweltΦ hZ Φ S U' L σ = σ₁) ∧
      E.Inv M₁ (σ₁.nimmt L) ((U' (E.lock L) σ').nimmt (E.lock L)) := by
  obtain ⟨hk, hsub, hΦ⟩ := E.schluessel h
  let W' := U' (E.lock L) σ'
  refine ⟨_, mischU S L σ (E.speicherZ hZ W'.speicher), hsub, ?_, ?_⟩
  · intro Φ hP
    show mischU S L σ (E.speicherZ hZ (U' (E.lock L) (Φ.haupt σ)).speicher) = _
    rw [hΦ Φ hP]
  · have ht : E.Treu (mischU S L σ (E.speicherZ hZ W'.speicher)).speicher W' :=
      E.treu_misch hZ hk.treu (fun c => c ∈ S.orte L) (fun c hc => mischU_innen S L σ _ c hc)
        (fun c hc => ⟨mischU_aussen S L σ _ c hc, (hU' (E.lock L) σ').2.1 _ (by
          rw [hSo]; exact fun hm => hc (E.mem_map_ortE.mp hm))⟩)
    exact hk.wachs E (by simp [World.nimmt, mischU_spur]) ht

/-- The memory of a `D'`-world beside a `D`-memory, restricted, is that memory. -/
theorem speicherZ_treu {s : Speicher D} {σ' : World D'} (h : E.Treu s σ') :
    E.speicherZ hZ σ'.speicher = s := by
  cases s with
  | mk sl gl =>
    simp only [speicherZ]
    congr 1
    · funext t k f
      have := h.1 t k f
      show E.valZ _ _ (castW _ (σ'.slots (E.tab t) k (E.feld t f))) = _
      rw [this]; exact E.valZ_valE _ _ _
    · funext g
      have := h.2 g
      show E.valZ _ _ (castW _ (σ'.globs (E.glob g))) = _
      rw [this]; exact E.valZ_valE _ _ _

/-- **A release on both sides**: the image lock's invariant is the lock's, over the image
    memory. -/
theorem freiH_rel {M : Keys D D'} {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx}
    (S : SperrInv D) {S' : SperrInv D'}
    (hSi : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s')) (L : D.Lock)
    {o : Ausgang V l Γ} {o' : Ausgang (E.vertragE V) l Γ'} (h : E.AusRel M o o') :
    E.AusRel M (freiH S L o) (freiH S' (E.lock L) o') := by
  have hb : ∀ {σ : World D} {σ' : World D'}, E.Inv M σ σ' →
      S'.inv (E.lock L) σ'.speicher = S.inv L σ.speicher := fun h =>
    by rw [hSi, E.speicherZ_treu hZ h.treu]
  cases o <;> cases o' <;> simp only [AusRel] at h <;> (try exact h.elim)
  · simp only [freiH, hb h.1]
    split
    · exact ⟨h.1.gibt E L (E.lock L), h.2⟩
    · exact (show E.LogikRel _ _ ∧ E.KeyOk M from ⟨fun _ he => (by cases he), h.1.keyOk E⟩)
  · simp only [freiH]; exact ⟨h.1.gibt E L (E.lock L), h.2⟩
  · simp only [freiH]; exact ⟨h.1.gibt E L (E.lock L), h.2⟩
  · simp only [freiH, hb h.1]
    split
    · exact ⟨h.1.gibt E L (E.lock L), h.2⟩
    · exact (show E.LogikRel _ _ ∧ E.KeyOk M from ⟨fun _ he => (by cases he), h.1.keyOk E⟩)
  · simp only [freiH, hb h.1]
    split
    · exact ⟨h.1.gibt E L (E.lock L), h.2⟩
    · exact (show E.LogikRel _ _ ∧ E.KeyOk M from ⟨fun _ he => (by cases he), h.1.keyOk E⟩)
  · simp only [freiH]; exact h
  · simp only [freiH]; exact h

end Einbettung

end Gabbro.Grammatik.Einbettung
