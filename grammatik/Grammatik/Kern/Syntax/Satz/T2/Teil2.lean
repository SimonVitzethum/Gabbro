module

public import Grammatik.Kern.Syntax.Satz.T1
public import Grammatik.Kern.Syntax.Satz.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

theorem heldB_locks {bo : Option Int} {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hh : HeldB bo Λ h) : HeldB bo (Res.held L :: Λ) (L :: h) := by
  refine ⟨fun M hM => ?_, fun M hM hn => ?_⟩
  · rcases List.mem_cons.mp hM with hM | hM
    · cases hM; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hh.1 M hM)
  · rcases List.mem_cons.mp hM with rfl | hM
    · exact absurd List.mem_cons_self hn
    · exact hh.2 M hM (fun h => hn (List.mem_cons_of_mem _ h))

/-- A `locks L` of a body whose every lock ranks at least the floor
    (`c ≤ rang L`) takes a lock that is not held, above everything held. -/
theorem nicht_gehaltenB {bo : Option Int} {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) (hh : HeldB bo Λ h)
    (hc : ∀ c, bo = some c → c ≤ D.rang L) :
    (∀ M ∈ h, D.rang M < D.rang L) ∧ L ∉ h := by
  have key : ∀ M ∈ h, D.rang M < D.rang L := by
    intro M hM
    by_cases hΛ : Res.held M ∈ Λ
    · exact hr M hΛ
    · obtain ⟨c, hc', hlt⟩ := hh.2 M hM hΛ
      have := hc c hc'
      omega
  refine ⟨key, fun hL => ?_⟩
  have := key L hL
  omega

theorem orte_tab {Λ : List (Res D)} {t : D.Tab} (hL : darf D t Λ) : OrtDarf Λ (.inl t) := hL
theorem orte_glob {Λ : List (Res D)} {g : D.Glob} (hL : gdarf D g Λ) : OrtDarf Λ (.inr g) := hL

theorem orte_cons {Λ : List (Res D)} {o : D.Tab ⊕ D.Glob} {os : List (D.Tab ⊕ D.Glob)}
    (h1 : OrtDarf Λ o) (h2 : ∀ o ∈ os, OrtDarf Λ o) : ∀ o' ∈ o :: os, OrtDarf Λ o' := by
  intro o' h; simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact h1
  · exact h2 o' h

/-- Die Praemissen ueber die Umgebung, benannt: der Ruf haelt Rahmen und Spur seines Gerufenen
    (das ist der Satz eine Ebene tiefer, `rufAt_gut` unten), und die Hardware den Rahmen ihres
    `effects` und laesst Sperren und Spur, wie sie sind (H1 -- eine Annahme). Ein
    fortgegebener Grund (`why`) darf die gekreuzten Scopes freigeben, aber nur solche:
    kein benoetigtes Schloss (`spare`) und keines unter dem Boden (`rank`), sodass der
    Rufer seine Holdings hinueberrettet (`heldB_weiterRet` mit `RufPasst.hx`). -/
def GutR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt →
    ∀ σ', (R f σ ρ).welt = some σ' →
    match (R f σ ρ) with
    | .ok _ _ => Gut (D.schreibt f) (D.gschreibt f) σ σ'
    | .why _ _ => GutRetV (D.schreibt f) (D.gschreibt f) (D.signatur f).haelt
        (D.signatur f).boden σ σ'
    | .logik _ => True
    | .hardware _ => True

/-- Every handler outcome keeps the frame (`Gut` and `GutRetV` carry `Rahmen`). -/
theorem GutR.rahmen (hR : GutR R) {f : D.Fn} {σ : World D} {ρ : Env D (D.params f)}
    (hh : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt)
    {σ' : World D} (h : (R f σ ρ).welt = some σ') :
    Rahmen (D.schreibt f) (D.gschreibt f) σ σ' := by
  have h2 := hR f σ ρ hh σ' h
  cases he : R f σ ρ with
  | ok _ _ => rw [he] at h2; exact h2.1
  | why _ _ => rw [he] at h2; exact h2.1
  | logik _ => simp only [RufAusgang.welt, reduceCtorEq] at h
  | hardware _ => simp only [RufAusgang.welt, reduceCtorEq] at h

/-- The write events of one axiom over explicit carrier domains, in a fixed
    order (tables, then globals): one `zugriff`-with-`true` per declared table
    write, one `gzugriff`-with-`true` per declared global write -- the
    `schreibSlot`/`World.merke` write-event constructor. The domains ride
    along because carrier types are not enumerable (`stmtTraeger` in
    `Extraktion.lean` takes them for the same reason); `Λ`/`h` ride along
    because a recorded event must name its guards and the held locks. -/
def axiomSpur (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) : List (Ereignis D) :=
  (tabs.filter (D.aschreibt a)).map (fun t => Ereignis.zugriff t true Λ h) ++
    (globs.filter (D.agschreibt a)).map (fun g => Ereignis.gzugriff g true Λ h)

/-- Membership in `axiomSpur`: a declared table write or a declared global
    write, with the call's guards and held locks. -/
theorem axiomSpur_mem {tabs : List D.Tab} {globs : List D.Glob} {a : D.Ax}
    {Λ : List (Res D)} {h : List D.Lock} {e : Ereignis D}
    (hmem : e ∈ axiomSpur tabs globs a Λ h) :
    (∃ t, t ∈ tabs ∧ D.aschreibt a t = true ∧ e = Ereignis.zugriff t true Λ h) ∨
      (∃ g, g ∈ globs ∧ D.agschreibt a g = true ∧ e = Ereignis.gzugriff g true Λ h) := by
  simp only [axiomSpur, List.mem_append, List.mem_map] at hmem
  rcases hmem with ⟨t, htf, rfl⟩ | ⟨g, hgf, rfl⟩
  · obtain ⟨hmem, hwr⟩ := List.mem_filter.mp htf
    exact Or.inl ⟨t, hmem, hwr, rfl⟩
  · obtain ⟨hmem, hwr⟩ := List.mem_filter.mp hgf
    exact Or.inr ⟨g, hmem, hwr, rfl⟩

/-- Every `axiomSpur` event records the held locks. -/
theorem axiomSpur_zugriffMit (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) :
    ∀ e ∈ axiomSpur tabs globs a Λ h, e.zugriffMit h := by
  intro e hmem
  rcases axiomSpur_mem hmem with ⟨t, _, _, rfl⟩ | ⟨g, _, _, rfl⟩ <;>
    simp only [Ereignis.zugriffMit]

/-- Every `axiomSpur` event is good, when the guards hold it. -/
theorem axiomSpur_gut (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock)
    (hdt : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hdg : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hhi : HeldIn Λ h) :
    ∀ e ∈ axiomSpur tabs globs a Λ h, e.gut := by
  intro e hmem
  rcases axiomSpur_mem hmem with ⟨t, _, hwr, rfl⟩ | ⟨g, _, hwr, rfl⟩
  · exact ⟨hdt t hwr, hhi⟩
  · exact ⟨hdg g hwr, hhi⟩

/-- A declared table write is recorded in `axiomSpur`. -/
theorem axiomSpur_write_tab (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) (t : D.Tab)
    (hmem : t ∈ tabs) (hwr : D.aschreibt a t = true) :
    Ereignis.zugriff t true Λ h ∈ axiomSpur tabs globs a Λ h := by
  simp only [axiomSpur, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨hmem, hwr⟩, rfl⟩)

/-- A declared global write is recorded in `axiomSpur`. -/
theorem axiomSpur_write_glob (tabs : List D.Tab) (globs : List D.Glob) (a : D.Ax)
    (Λ : List (Res D)) (h : List D.Lock) (g : D.Glob)
    (hmem : g ∈ globs) (hwr : D.agschreibt a g = true) :
    Ereignis.gzugriff g true Λ h ∈ axiomSpur tabs globs a Λ h := by
  simp only [axiomSpur, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hmem, hwr⟩, rfl⟩)

/-- The oracle bound, conditional trace: the answer respects the declared
    footprint and keeps the held locks in every world; in worlds where the
    axiom's lock guards are held (the situation of every real call -- the
    `axiomCall`/`bindAxiom` guard premises `hd`/`hgd` plus `HeldGenau` give
    it at the call site), it records its declared writes as `axiomSpur`
    events over complete domains, with a mark-free guard trace it holds.
    In worlds where the guards are not held the trace is unconstrained:
    no typed execution reaches them. -/
def GutO (O : Orakel D) : Prop :=
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt ∧
    ((∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt) →
     (∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt) →
     ∃ tabs : List D.Tab, ∃ globs : List D.Glob, ∃ Λe : List (Res D),
      (∀ t, D.aschreibt a t = true → t ∈ tabs) ∧
      (∀ g, D.agschreibt a g = true → g ∈ globs) ∧
      (∀ t, D.aschreibt a t = true → darf D t Λe) ∧
      (∀ g, D.agschreibt a g = true → gdarf D g Λe) ∧
      (∀ m st, Res.marke m st ∉ Λe) ∧
      HeldIn Λe σ.haelt ∧
      (O.wirkt a σ ρ).1.spur = axiomSpur tabs globs a Λe σ.haelt ++ σ.spur)


end Gabbro.Grammatik
