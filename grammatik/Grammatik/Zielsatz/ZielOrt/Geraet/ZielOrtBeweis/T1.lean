/-
  File:      Grammatik/ZielOrtBeweis.lean
  Subject:   `ziel_ort` -- contracts hold at their place on every machine of
             the repaired concurrent call machine G, from the user's
             sequential obligations, the hardware assumption and decidable
             program facts.

  The proof is a REPLAY. Every frame of every thread carries a sequential
  run of its function's body, started at the frame's entry world:

  * the sequential world `σ` of the head frame agrees with the machine
    world on the frame's footprint (`GleichAuf (fussOrte P f) σ W`): the
    frame's own steps are sequential steps at `σ` (leaf locality, the
    residue step lemmas of `ZielOrtSem.lean`), and steps of OTHER threads
    never touch the footprint (the rely: every footprint carrier is guarded
    by a signature lock the frame holds for its whole life
    (`rufG_haelt_signatur`), exclusive across threads (`exklusivG`), or
    written by no function);
  * the calls the frame made are RECORDED with the machine's answers
    (`Eintrag`), each answer at a fresh trace position of the sequential
    world, so the record is a function of the call key and defines a
    contract-respecting handler (`rufAus`); the sequential run of the body
    with ANY handler that repeats the record reaches the frame's current
    residue (`KopfOk`), a suspended frame the pending call (`WarteOk`);
  * at a return, `KoerperGut` (the body triple) gives `ensures` in the
    sequential world, hence in the machine's (agreement on the footprint,
    which contains the `ensures` carriers); at a call, `KoerperGut`'s gated
    conjunct (no failed `requires`) gives the callee's `requires` in the
    sequential world, hence in the machine's (the callee's contract carriers
    are in the caller's footprint).
-/
module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtSem
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Recorded call answers and the handler they define -/

/-- A recorded call: callee, key world, parameters, answer world, value. -/
abbrev Eintrag (D : Deklaration) :=
  Σ g : D.Fn, World D × Env D (D.params g) × World D × ErgVal D (D.erg g)

/-- The recorded answers are a function of the call key. -/
def Funk (H : List (Eintrag D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (a a' : World D × ErgVal D (D.erg g)),
    (⟨g, σ, ρ, a.1, a.2⟩ : Eintrag D) ∈ H → (⟨g, σ, ρ, a'.1, a'.2⟩ : Eintrag D) ∈ H → a = a'

/-- Every recorded key lies strictly below trace length `N`. -/
def KurzH (N : Nat) (H : List (Eintrag D)) : Prop :=
  ∀ e ∈ H, e.2.1.spur.length < N

/-- Every recorded answer respects the callee's contract at its key. -/
def VertraegeOk (P : Programm D) (H : List (Eintrag D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (σa : World D) (v : ErgVal D (D.erg g)),
    (⟨g, σ, ρ, σa, v⟩ : Eintrag D) ∈ H → ReqAmEintritt P g σ ρ ∧ EnsAmRueck P g σ σa ρ v

/-- A handler repeats the record. -/
def Passt (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (H : List (Eintrag D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (σa : World D) (v : ErgVal D (D.erg g)),
    (⟨g, σ, ρ, σa, v⟩ : Eintrag D) ∈ H → R g σ ρ = .ok σa v

/-- The handler of a record: the recorded answer at a recorded key, an
    exhausted descent everywhere else. -/
noncomputable def rufAus (H : List (Eintrag D)) :
    ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ =>
    haveI := Classical.propDecidable
      (∃ a : World D × ErgVal D (D.erg g), (⟨g, σ, ρ, a.1, a.2⟩ : Eintrag D) ∈ H)
    if h : ∃ a : World D × ErgVal D (D.erg g), (⟨g, σ, ρ, a.1, a.2⟩ : Eintrag D) ∈ H
    then .ok (Classical.choose h).1 (Classical.choose h).2
    else .logik (.abstieg g)

theorem rufAus_passt {H : List (Eintrag D)} (hf : Funk H) : Passt (rufAus H) H := by
  intro g σ ρ σa v hmem
  have hex : ∃ a : World D × ErgVal D (D.erg g), (⟨g, σ, ρ, a.1, a.2⟩ : Eintrag D) ∈ H :=
    ⟨(σa, v), hmem⟩
  simp only [rufAus, dif_pos hex]
  have := hf g σ ρ _ (σa, v) (Classical.choose_spec hex) hmem
  rw [this]

theorem rufAus_ok {H : List (Eintrag D)} {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)}
    {σa : World D} {v : ErgVal D (D.erg g)} (h : rufAus H g σ ρ = .ok σa v) :
    (⟨g, σ, ρ, σa, v⟩ : Eintrag D) ∈ H := by
  unfold rufAus at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · cases h

theorem rufAus_respektiert {P : Programm D} {H : List (Eintrag D)} (hv : VertraegeOk P H) :
    RespektiertVertraege P (rufAus H) := by
  intro g σ ρ _ σ' v h
  exact (hv g σ ρ σ' v (rufAus_ok h)).2

theorem rufAus_ohneVorbedingung (H : List (Eintrag D)) : OhneVorbedingung (rufAus H) := by
  intro g σ ρ e h g' he
  unfold rufAus at h
  split at h
  · cases h
  · cases h
    cases he

/-- The gated handler repeats a record whose keys meet `requires`. -/
theorem torRuf_passt {P : Programm D} {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {H : List (Eintrag D)} (hp : Passt R H) (hv : VertraegeOk P H) : Passt (torRuf P R) H := by
  intro g σ ρ σa v hmem
  have hreq : wahr? (eval σ (P.requires g) σ ρ) = true := (hv g σ ρ σa v hmem).1
  simp only [torRuf, hreq, if_true]
  exact hp g σ ρ σa v hmem

theorem passt_append {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {H : List (Eintrag D)} {e : Eintrag D} (h : Passt R (H ++ [e])) : Passt R H :=
  fun g σ ρ σa v hmem => h g σ ρ σa v (List.mem_append_left _ hmem)

theorem funk_nil : Funk ([] : List (Eintrag D)) := fun _ _ _ _ _ h => absurd h List.not_mem_nil

theorem vertraegeOk_nil (P : Programm D) : VertraegeOk P ([] : List (Eintrag D)) :=
  fun _ _ _ _ _ h => absurd h List.not_mem_nil

theorem kurzH_nil (N : Nat) : KurzH N ([] : List (Eintrag D)) :=
  fun _ h => absurd h List.not_mem_nil

theorem kurzH_mono {N N' : Nat} {H : List (Eintrag D)} (h : KurzH N H) (hN : N ≤ N') :
    KurzH N' H :=
  fun e he => Nat.lt_of_lt_of_le (h e he) hN

/-- A new entry at a key no older entry has (its trace is longer) keeps the
    record a function. -/
theorem funk_append {H : List (Eintrag D)} (hf : Funk H) {N : Nat} (hk : KurzH N H)
    (e : Eintrag D) (he : N ≤ e.2.1.spur.length) : Funk (H ++ [e]) := by
  intro g σ ρ a a' h1 h2
  rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
  · exact hf g σ ρ a a' h1 h2
  · have := hk _ h1
    rw [List.mem_singleton] at h2
    subst h2
    exact absurd he (Nat.not_le.mpr this)
  · have := hk _ h2
    rw [List.mem_singleton] at h1
    subst h1
    exact absurd he (Nat.not_le.mpr this)
  · rw [List.mem_singleton] at h1 h2
    rw [← h1] at h2
    have := (Sigma.mk.inj h2).2
    have e2 := eq_of_heq this
    simp only [Prod.mk.injEq] at e2
    exact Prod.ext e2.2.2.1.symm e2.2.2.2.symm

/-! ## 2. Contracts carry along agreement on their carriers -/

theorem req_transfer {P : Programm D} {f : D.Fn} {σ σ' : World D} {ρ : Env D (D.params f)}
    (h : ReqAmEintritt P f σ ρ) (hg : GleichAuf (P.requires f).orte σ σ') :
    ReqAmEintritt P f σ' ρ := by
  have e := eval_gleichAuf (P.requires f) (fun _ ho => ho) hg ρ
  unfold ReqAmEintritt at h ⊢
  rw [← e]
  exact h

theorem ens_transfer {P : Programm D} {f : D.Fn} {s0 s0' σ σ' : World D}
    {ρ : Env D (D.params f)} {v : ErgVal D (D.erg f)}
    (h : EnsAmRueck P f s0 σ ρ v) (h0 : GleichAuf (P.ensures f).orte s0 s0')
    (h1 : GleichAuf (P.ensures f).orte σ σ') : EnsAmRueck P f s0' σ' ρ v := by
  have e := Extraktion.eval_liest_nur_orte (P.ensures f) (P.ensures f).orte (fun _ ho => ho)
    s0 s0' σ σ' (ergEnv (D.erg f) v ρ)
    (fun t ht k fl => congrFun (congrFun (h1.1 t ht) k) fl) (fun g hg => h1.2 g hg)
    (fun t ht k fl => congrFun (congrFun (h0.1 t ht) k) fl) (fun g hg => h0.2 g hg)
  unfold EnsAmRueck at h ⊢
  rw [← e]
  exact h

theorem zErg_gleich_logik {V : Vertrag D} {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {e : Logik D} (h : (zErg o).gleich (.logik e)) : o = .logik e := by
  cases o <;> simp_all [zErg, ZErg.gleich]

theorem zErg_gleich_zurueck {V : Vertrag D} {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {σ : World D} {v : ErgVal D V.erg} (h : (zErg o).gleich (.zurueck σ v)) :
    ∃ σ', o = .zurueck σ' v ∧ SG σ' σ := by
  cases o with
  | zurueck σ' v' =>
      obtain ⟨hs, hv⟩ := h
      subst hv
      exact ⟨σ', rfl, hs⟩
  | _ => simp only [ZErg.gleich, zErg] at h

theorem gleichAuf_SG {S : List (D.Tab ⊕ D.Glob)} {σ σ' : World D} (h : SG σ σ') :
    GleichAuf S σ σ' :=
  ⟨fun t _ => by rw [h.1], fun g _ => by rw [h.2]⟩

/-! ## 3. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat)

/-- **The replay of a head frame** `F` whose thread world is `W`: a record
    `H` of the calls it made (a function, answers respecting the callees'
    contracts, keys below the sequential trace), a sequential world `σ`
    agreeing with `W` on the footprint, the residue in the fragment, and:
    the body run sequentially from the entry world with ANY handler that
    repeats the record ends as the residue ends from `σ`. -/
def KopfOk (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (Eintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ Funk H ∧ VertraegeOk P H ∧ KurzH σ.spur.length H ∧
    GleichAuf (fussOrte P F.f) σ W ∧ F.rest.2.2.2.2.okZ P (fussOrte P F.f) ∧
    ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D F.f) O passes R (P.rumpf F.f) F.s0 F.rho)).gleich
        (semZ O passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G` (function, parameters, entry world): a record, the sequential key
    world `κ` of the pending call (the callee's `requires` holds there, and
    it agrees with the callee's machine entry world on the callee's contract
    carriers), and: for any handler repeating the record that answers the
    pending call with `(σa, v)`, the body ends as the frame's continuation
    ends from `σa` (plain call) or with `v` bound (bind-call). -/
def WarteOk (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (Eintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ Funk H ∧ VertraegeOk P H ∧ KurzH κ.spur.length H ∧
    F.rest.2.2.2.2.okZ P (fussOrte P F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
    ∀ R, Passt R H → ∀ (σa : World D) (v : ErgVal D (D.erg G.1)), R G.1 κ G.2.1 = .ok σa v →
      (F.wartend = false →
        (zErg (execEnd (V := vertragVon D F.f) O passes R (P.rumpf F.f) F.s0 F.rho)).gleich
          (semZ O passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ → ∀ he : D.erg G.1 = some τ,
        (zErg (execEnd (V := vertragVon D F.f) O passes R (P.rumpf F.f) F.s0 F.rho)).gleich
          (semZ O passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))

/-- Every suspended frame waits for the frame above it. -/
def StapelOk : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteOk P O passes F G ∧ StapelOk (RufSchluesselG F) rest

/-- The replay of a thread. -/
def FadenOk (z : RufFadenG D) (W : World D) : Prop :=
  KopfOk P O passes z.kopf W ∧ StapelOk P O passes (RufSchluesselG z.kopf) z.stapel

/-- The contracts hold at every logged event of one log. -/
def LogOk (log : List (RufEreignisF D)) : Prop :=
  ∀ ev ∈ log,
    (∀ (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D),
      ev = RufEreignisF.eintritt g rho s0 → ReqAmEintritt P g s0 rho) ∧
    (∀ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      ev = RufEreignisF.rueck g rho v s0 s1 → EnsAmRueck P g s0 s1 rho v)

/-- The global invariant: every thread is replayed, every log is kept. -/
def ZielInv (M : RufMaschineG D) : Prop :=
  (∀ t, FadenOk P O passes (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv
end Gabbro.Grammatik
