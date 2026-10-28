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

variable (hZ : E.Rueck)

/-! ## Environments -/

theorem envR_tail {τ τ' : Ty} {Γ Γ' : Ctx} (ρ : Env D (τ :: Γ)) (ρ' : Env D' (τ' :: Γ'))
    (h : E.EnvR hZ ρ ρ') : E.EnvR hZ ρ.tail ρ'.tail := by
  cases ρ with
  | cons v ρ => cases ρ' with
    | cons v' ρ' => exact h.2

theorem envR_set : ∀ {Γ : Ctx} {τ : Ty} (ρ : Env D Γ) (ρ' : Env D' (Γ.map E.tyE)) (x : Var Γ τ)
    (v : Wert D τ) (v' : Wert D' (E.tyE τ)), E.EnvR hZ ρ ρ' → E.VRel hZ τ v v' →
    E.EnvR hZ (ρ.set x v) (ρ'.set (varE E x) v')
  | _ :: _, _, .cons _ _, .cons _ _, .here, _, _, h, hv => ⟨⟨rfl, hv⟩, h.2⟩
  | _ :: _, _, .cons _ ρ, .cons _ ρ', .there x, v, v', h, hv => ⟨h.1, envR_set ρ ρ' x v v' h.2 hv⟩

/-- Transporting the scope of the `D'`-side keeps the relation. -/
theorem envR_um {Γ : Ctx} {Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (ρ : Env D Γ) (ρ' : Env D' Γ₁) :
    E.EnvR hZ ρ (castE h ρ') ↔ E.EnvR hZ ρ ρ' := by subst h; rfl

/-- Transporting the scope of the `D`-side keeps the relation. -/
theorem envR_umD {Γ₁ Γ₂ Γ' : Ctx} (h : Γ₁ = Γ₂) (ρ : Env D Γ₁) (ρ' : Env D' Γ') :
    E.EnvR hZ (castE h ρ) ρ' ↔ E.EnvR hZ ρ ρ' := by subst h; rfl

/-! ## Outcomes -/

/-- **An outcome of `D` beside one of `D'`**, under the keys `M`. -/
def AusRel (M : Keys D D') {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} :
    Ausgang V l Γ → Ausgang (E.vertragE V) l Γ' → Prop
  | .ok σ ρ, .ok σ' ρ' => E.Inv hZ M σ σ' ∧ E.EnvR hZ ρ ρ'
  | .zurueck σ v, .zurueck σ' v' => E.Inv hZ M σ σ' ∧ E.ErgRel hZ V.erg v v'
  | .why σ r, .why σ' r' => E.Inv hZ M σ σ' ∧ r'.val = r.val
  | .leave _ σ ρ, .leave _ σ' ρ' => E.Inv hZ M σ σ' ∧ E.EnvR hZ ρ ρ'
  | .next _ σ ρ, .next _ σ' ρ' => E.Inv hZ M σ σ' ∧ E.EnvR hZ ρ ρ'
  | .logik e, .logik e' => LogikRel e e' ∧ E.KeyOk hZ M
  | .hardware _, .hardware _ => True
  | _, _ => False

/-- **An end outcome of `D` beside one of `D'`.** -/
def EndRel (M : Keys D D') {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx} :
    EndAusgang V l Γ → EndAusgang (E.vertragE V) l Γ' → Prop
  | .zurueck σ v, .zurueck σ' v' => E.Inv hZ M σ σ' ∧ E.ErgRel hZ V.erg v v'
  | .why σ r, .why σ' r' => E.Inv hZ M σ σ' ∧ r'.val = r.val
  | .leave _ σ ρ, .leave _ σ' ρ' => E.Inv hZ M σ σ' ∧ E.EnvR hZ ρ ρ'
  | .next _ σ ρ, .next _ σ' ρ' => E.Inv hZ M σ σ' ∧ E.EnvR hZ ρ ρ'
  | .logik e, .logik e' => LogikRel e e' ∧ E.KeyOk hZ M
  | .hardware _, .hardware _ => True
  | _, _ => False

variable {hZ}

section Rel

variable {M : Keys D D'} {V : Vertrag D} {l : Bool}

theorem ausRel_schrumpf {τ τ' : Ty} {Γ Γ' : Ctx} {o : Ausgang V l (τ :: Γ)}
    {o' : Ausgang (E.vertragE V) l (τ' :: Γ')} (h : E.AusRel hZ M o o') :
    E.AusRel hZ M o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp only [AusRel, Ausgang.schrumpf] at h ⊢ <;>
    first
    | exact ⟨h.1, E.envR_tail hZ _ _ h.2⟩
    | exact h
    | exact h.elim

theorem endRel_schrumpf {τ τ' : Ty} {Γ Γ' : Ctx} {o : EndAusgang V l (τ :: Γ)}
    {o' : EndAusgang (E.vertragE V) l (τ' :: Γ')} (h : E.EndRel hZ M o o') :
    E.EndRel hZ M o.schrumpf o'.schrumpf := by
  cases o <;> cases o' <;> simp only [EndRel, EndAusgang.schrumpf] at h ⊢ <;>
    first
    | exact ⟨h.1, E.envR_tail hZ _ _ h.2⟩
    | exact h
    | exact h.elim

theorem endRel_zuAusgang {Γ Γ' : Ctx} {o : EndAusgang V l Γ}
    {o' : EndAusgang (E.vertragE V) l Γ'} (h : E.EndRel hZ M o o') :
    E.AusRel hZ M o.zuAusgang o'.zuAusgang := by
  cases o <;> cases o' <;> simp only [EndRel, AusRel, EndAusgang.zuAusgang] at h ⊢ <;>
    first
    | exact h
    | exact h.elim

/-- Transporting the scope of the `D'`-side keeps the relation. -/
theorem ausRel_um {Γ Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (o : Ausgang V l Γ)
    (o' : Ausgang (E.vertragE V) l Γ₁) :
    E.AusRel hZ M o (castAus h o') ↔ E.AusRel hZ M o o' := by subst h; rfl

theorem endRel_um {Γ Γ₁ Γ₂ : Ctx} (h : Γ₁ = Γ₂) (o : EndAusgang V l Γ)
    (o' : EndAusgang (E.vertragE V) l Γ₁) :
    E.EndRel hZ M o (castEnd h o') ↔ E.EndRel hZ M o o' := by subst h; rfl

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


/-- **A mixed world beside its `D'`-move**: on the carriers `P` the mixed world holds the move's
    memory restricted; elsewhere both keep what they had. -/
theorem treu_misch {σ m : World D} {σ' W' : World D'} (hσ : E.Treu hZ σ.speicher σ')
    (P : D.Tab ⊕ D.Glob → Prop)
    (hin : ∀ c, P c → TraegerGleich m.speicher (E.speicherZ hZ W'.speicher) c)
    (hout : ∀ c, ¬ P c → TraegerGleich m.speicher σ.speicher c ∧
      TraegerGleich W'.speicher σ'.speicher (E.ortE c)) :
    E.Treu hZ m.speicher W' := by
  refine ⟨fun t k f => ?_, fun g => ?_⟩
  · by_cases hp : P (.inl t)
    · have e : m.slots t = (E.speicherZ hZ W'.speicher).slots t := hin _ hp
      show E.VRel hZ _ (m.slots t k f) (castW _ (W'.slots (E.tab t) k (E.feld t f)))
      rw [e]; exact E.vrel_valZ hZ _ _
    · obtain ⟨e1, e2⟩ := hout _ hp
      have e1 : m.slots t = σ.slots t := e1
      have e2 : W'.slots (E.tab t) = σ'.slots (E.tab t) := e2
      show E.VRel hZ _ (m.slots t k f) (castW _ (W'.slots (E.tab t) k (E.feld t f)))
      rw [e1, e2]; exact hσ.1 t k f
  · by_cases hp : P (.inr g)
    · have e : m.globs g = (E.speicherZ hZ W'.speicher).globs g := hin _ hp
      show E.VRel hZ _ (m.globs g) (castW _ (W'.globs (E.glob g)))
      rw [e]; exact E.vrel_valZ hZ _ _
    · obtain ⟨e1, e2⟩ := hout _ hp
      have e1 : m.globs g = σ.globs g := e1
      have e2 : W'.globs (E.glob g) = σ'.globs (E.glob g) := e2
      show E.VRel hZ _ (m.globs g) (castW _ (W'.globs (E.glob g)))
      rw [e1, e2]; exact hσ.2 g

/-! ## Keys -/

/-- `Φ` repeats the keys. -/
def Passt (Φ : Phi D D') (M : Keys D D') : Prop :=
  (∀ p ∈ M.haupt, Φ.haupt p.1 = p.2) ∧ (∀ p ∈ M.atom, Φ.atom p.1 = p.2) ∧
    (∀ p ∈ M.ruf, Φ.ruf p.1 = some p.2)

theorem passt_teil {Φ : Phi D D'} {M M' : Keys D D'} (h : Passt Φ M') (hs : Teil M M') : Passt Φ M :=
  ⟨fun p hp => h.1 p (hs.1 p hp), fun p hp => h.2.1 p (hs.2.1 p hp), fun p hp => h.2.2 p (hs.2.2 p hp)⟩

/-- **The current pair as a main key.** -/
theorem schluessel {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') :
    E.Inv hZ ⟨(σ, σ') :: M.haupt, M.atom, M.ruf⟩ σ σ' ∧ Teil M ⟨(σ, σ') :: M.haupt, M.atom, M.ruf⟩ ∧
      ∀ Φ, Passt Φ ⟨(σ, σ') :: M.haupt, M.atom, M.ruf⟩ → Φ.haupt σ = σ' :=
  ⟨h.merke E, ⟨fun _ hp => List.mem_cons_of_mem _ hp, fun _ hp => hp, fun _ hp => hp⟩,
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
    (h : E.Inv hZ M σ σ') (T : D.Tab ⊕ D.Glob → Prop) {T' : D'.Tab ⊕ D'.Glob → Prop}
    {A' : AUmwelt D'} (hA' : HavocA T' A') (hT : ∀ c, T' (E.ortE c) → T c)
    (Λ : List (Res D)) (Λ' : List (Res D')) (X : List (D.Tab ⊕ D.Glob)) :
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → leseA (E.aumweltΦ hZ Φ T A') σ Λ X = σ₁) ∧
      E.Inv hZ M₁ σ₁ (leseA A' σ' Λ' (X.map E.ortE)) := by
  cases X with
  | nil =>
      refine ⟨M, σ, teil_refl M, fun Φ _ => ?_, ?_⟩
      · show mischT T [] (σ.lese Λ []) _ = σ
        rw [mischT_nil, lese_nil]
      · show E.Inv hZ M σ (A' [] (σ'.lese Λ' []))
        rw [havocA_nil hA', lese_nil]; exact h
  | cons x X =>
      have hl := h.lese E Λ Λ' (x :: X)
      have hgr : σ.spur.length < (σ.lese Λ (x :: X)).spur.length := by
        rw [lese_laenge]; simp only [List.length_cons, Nat.lt_add_left_iff_pos, Nat.zero_lt_succ]
      have hk := hl.merkeA E (fun p hp => Nat.lt_of_le_of_lt (h.aKurz p hp) hgr)
      let σl := σ.lese Λ (x :: X)
      let σl' := σ'.lese Λ' ((x :: X).map E.ortE)
      let W' := A' ((x :: X).map E.ortE) σl'
      refine ⟨⟨M.haupt, (σl, σl') :: M.atom, M.ruf⟩, mischT T (x :: X) σl (E.speicherZ hZ W'.speicher),
        ⟨fun _ hp => hp, fun _ hp => List.mem_cons_of_mem _ hp, fun _ hp => hp⟩, ?_, ?_⟩
      · intro Φ hP
        show mischT T (x :: X) σl (E.speicherZ hZ (A' ((x :: X).map E.ortE) (Φ.atom σl)).speicher) = _
        rw [hP.2.1 _ List.mem_cons_self]
      · have ht : E.Treu hZ (mischT T (x :: X) σl (E.speicherZ hZ W'.speicher)).speicher W' :=
          E.treu_misch hk.treu (fun c => c ∈ x :: X ∧ T c) (fun c hc => mischT_innen σl _ hc)
            (fun c hc => ⟨mischT_aussen σl _ hc, (hA' _ σl').2 _ fun ⟨h1, h2⟩ =>
              hc ⟨E.mem_map_ortE.mp h1, hT c h2⟩⟩)
        refine ⟨ht, hk.eintrag, hk.kurz, fun p hp he => absurd he (Nat.ne_of_lt ?_), hk.funk,
          hk.aEintrag, hk.aKurz, hk.aFunk, hk.rKurz, hk.rFunk⟩
        exact Nat.lt_of_le_of_lt (h.kurz p hp) hgr

/-- **A lock move and the take.** The pair at the acquire as a main key, the `D'`-move's answer
    (the induced move answers the same there, the protected carriers of the image lock being the
    images), then the take event on both sides. -/
theorem umwelt_schritt {M : Keys D D'} {σ : World D} {σ' : World D'}
    (h : E.Inv hZ M σ σ') (S : SperrInv D) {S' : SperrInv D'} {U' : Umwelt D'} (hU' : HavocOk S' U')
    (hSo : ∀ L, S'.orte (E.lock L) = (S.orte L).map E.ortE) (L : D.Lock) :
    ∃ (M₁ : Keys D D') (σ₁ : World D), Teil M M₁ ∧
      (∀ Φ, Passt Φ M₁ → E.umweltΦ hZ Φ S U' L σ = σ₁) ∧
      E.Inv hZ M₁ (σ₁.nimmt L) ((U' (E.lock L) σ').nimmt (E.lock L)) := by
  obtain ⟨hk, hsub, hΦ⟩ := E.schluessel h
  let W' := U' (E.lock L) σ'
  refine ⟨_, mischU S L σ (E.speicherZ hZ W'.speicher), hsub, ?_, ?_⟩
  · intro Φ hP
    show mischU S L σ (E.speicherZ hZ (U' (E.lock L) (Φ.haupt σ)).speicher) = _
    rw [hΦ Φ hP]
  · have ht : E.Treu hZ (mischU S L σ (E.speicherZ hZ W'.speicher)).speicher W' :=
      E.treu_misch hk.treu (fun c => c ∈ S.orte L) (fun c hc => mischU_innen S L σ _ c hc)
        (fun c hc => ⟨mischU_aussen S L σ _ c hc, (hU' (E.lock L) σ').2.1 _ (by
          rw [hSo]; exact fun hm => hc (E.mem_map_ortE.mp hm))⟩)
    exact hk.wachs E (by simp only [World.nimmt, mischU_spur, List.length_cons, Nat.lt_add_one]) ht

/-- The memory of a `D'`-world beside a `D`-memory, restricted, is that memory. -/
theorem speicherZ_treu {s : Speicher D} {σ' : World D'} (h : E.Treu hZ s σ') :
    E.speicherZ hZ σ'.speicher = s := by
  cases s with
  | mk sl gl =>
    simp only [speicherZ]
    congr 1
    · funext t k f
      have := h.1 t k f
      exact E.valZ_vrel hZ _ this
    · funext g
      have := h.2 g
      exact E.valZ_vrel hZ _ this

/-- **A release on both sides**: the image lock's invariant is the lock's, over the image
    memory. -/
theorem freiH_rel {M : Keys D D'} {V : Vertrag D} {l : Bool} {Γ Γ' : Ctx}
    (S : SperrInv D) {S' : SperrInv D'}
    (hSi : ∀ L s', S'.inv (E.lock L) s' = S.inv L (E.speicherZ hZ s')) (L : D.Lock)
    {o : Ausgang V l Γ} {o' : Ausgang (E.vertragE V) l Γ'} (h : E.AusRel hZ M o o') :
    E.AusRel hZ M (freiH S L o) (freiH S' (E.lock L) o') := by
  have hb : ∀ {σ : World D} {σ' : World D'}, E.Inv hZ M σ σ' →
      S'.inv (E.lock L) σ'.speicher = S.inv L σ.speicher := fun h =>
    by rw [hSi, E.speicherZ_treu h.treu]
  cases o <;> cases o' <;> simp only [AusRel] at h <;> (try exact h.elim)
  · simp only [freiH, hb h.1]
    split
    · exact ⟨h.1.gibt E L (E.lock L), h.2⟩
    · exact (show LogikRel _ _ ∧ E.KeyOk hZ M from ⟨fun _ he => (by cases he), h.1.keyOk E⟩)
  · simp only [freiH]; exact ⟨h.1.gibt E L (E.lock L), h.2⟩
  · simp only [freiH]; exact ⟨h.1.gibt E L (E.lock L), h.2⟩
  · simp only [freiH, hb h.1]
    split
    · exact ⟨h.1.gibt E L (E.lock L), h.2⟩
    · exact (show LogikRel _ _ ∧ E.KeyOk hZ M from ⟨fun _ he => (by cases he), h.1.keyOk E⟩)
  · simp only [freiH, hb h.1]
    split
    · exact ⟨h.1.gibt E L (E.lock L), h.2⟩
    · exact (show LogikRel _ _ ∧ E.KeyOk hZ M from ⟨fun _ he => (by cases he), h.1.keyOk E⟩)
  · simp only [freiH]; exact h
  · simp only [freiH]; exact h

end Einbettung

end Gabbro.Grammatik.Einbettung
