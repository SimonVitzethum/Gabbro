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
import Grammatik.ZielOrtSem

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
  | _ => simp [zErg, ZErg.gleich] at h

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

theorem logOk_eintritt {P : Programm D} {log : List (RufEreignisF D)} (h : LogOk P log)
    {g : D.Fn} {rho : Env D (D.params g)} {s0 : World D} (hr : ReqAmEintritt P g s0 rho) :
    LogOk P (RufEreignisF.eintritt g rho s0 :: log) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · refine ⟨fun g' rho' s0' he => ?_, fun _ _ _ _ _ he => by cases he⟩
    cases he
    exact hr
  · exact h ev hev

theorem logOk_rueck {P : Programm D} {log : List (RufEreignisF D)} (h : LogOk P log)
    {g : D.Fn} {rho : Env D (D.params g)} {v : ErgVal D (D.erg g)} {s0 s1 : World D}
    (he : EnsAmRueck P g s0 s1 rho v) :
    LogOk P (RufEreignisF.rueck g rho v s0 s1 :: log) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · refine ⟨fun _ _ _ h' => (by cases h'), fun g' rho' v' s0' s1' h' => ?_⟩
    cases h'
    exact he
  · exact h ev hev

section Hilfen

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem kopf_okZ {F : RufRahmenG D} {W : World D} (h : KopfOk P O passes F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okZ P (fussOrte P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step** keeps the replay: the stack and the key are
    kept, the residue moves by a sequential step at the sequential world. -/
theorem fadenOk_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenOk P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrte P z.kopf.f) σ W →
      r.okZ P (fussOrte P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrte P z.kopf.f) σ' W' ∧
        r'.okZ P (fussOrte P z.kopf.f) ∧
        ∀ R, (semZ O passes R r' σ' ρ').gleich (semZ O passes R r σ ρ)) :
    FadenOk P O passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, σ, hreq, hf, hv, hk, hg, hok, heq⟩, hS⟩ := hF
  have hok' : r.okZ P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).gleich (semZ O passes R r σ ρ) := by
    intro R hR
    have := heq R hR
    rw [hr] at this
    exact this
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  exact ⟨⟨H, σ', hreq, hf, hv, kurzH_mono hk hl, hg', hok'',
    fun R hR => ZErg.gleich_trans (heq' R hR) (ZErg.gleich_symm (hsem R))⟩, hS⟩

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenOk_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenOk P O passes z W)
    (hw : ∀ c ∈ fussOrte P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenOk P O passes z W' := by
  obtain ⟨⟨H, σ, hreq, hf, hv, hk, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, σ, hreq, hf, hv, hk, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok, heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

theorem lese_laenge (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    σ.spur.length ≤ (σ.lese Λ os).spur.length :=
  spur_laenge_erw (Erw.lese σ Λ os)

theorem fuss_rumpf (P : Programm D) (f : D.Fn) : endblockOrteP P (P.rumpf f) ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_left _ (List.mem_append_right _ ho)

theorem fuss_ens (P : Programm D) (f : D.Fn) : (P.ensures f).orte ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ho))

theorem fuss_req (P : Programm D) (f : D.Fn) : (P.requires f).orte ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ho))

/-- The carriers of an owed invariant are in the footprint. -/
theorem fuss_inv (P : Programm D) (f : D.Fn) {i : D.Inv} (hi : i ∈ D.invs)
    (hs : schuldet f i = true) : (P.invariante i).orte ⊆ fussOrte P f :=
  fun _ ho => List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, hs⟩, ho⟩)

end Hilfen

/-! ## 4. Calls and returns of the replay -/

/-- The answer world a return records: the machine's memory at the return,
    one trace event past the call key (a fresh position: the record stays a
    function of the key). -/
def antwortWelt (e0 : Ereignis D) (s1 κ : World D) : World D := ⟨s1.slots, s1.globs, e0 :: κ.spur⟩

section Rufe

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The return leg.** At a return of the head frame, the body's
    sequential run with the recorded handler returns the same value in a
    world agreeing with the machine's on the footprint; `KoerperGut` gives
    `ensures` there, hence at the machine's return world. -/
theorem pop_ens (hK : ∀ f, KoerperGut P O passes f) {G : RufRahmenG D} {W : World D}
    (hG : KopfOk P O passes G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrte P G.f)
    (hsem : ∀ R σ, semZ O passes R r σ ρ =
      .zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, σ, hreq, hf, hv, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAus H) (rufAus_passt hf)
  rw [hr] at h1
  simp only at h1
  rw [hsem] at h1
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h1
  have hE := (hK G.f (rufAus H) (rufAus_respektiert hv) (rufAus_ohneVorbedingung H) G.s0 G.rho
    hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrte P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P G.f h) ((gleichAuf_SG hsg).trans hgl))

/-- **The caller resumes.** After the callee `G` returned `v` in the
    machine world `s1` (with `ensures` there), the suspended frame `F`
    records the answer (the machine's memory, a fresh trace position) and
    becomes a replayed head frame with the continuation `r'` chosen by the
    pop (`hwahl`). -/
theorem pop_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteOk P O passes F G) (s1 : World D) (v : ErgVal D (D.erg G.1))
    (hens : EnsAmRueck P G.1 G.2.2 s1 G.2.1 v)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hok' : F.rest.2.2.2.2.okZ P (fussOrte P F.f) → r'.okZ P (fussOrte P F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (σa : World D)
      (X : ZErg (vertragVon D F.f)),
      (F.wartend = false → X.gleich (semZ O passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) →
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ → ∀ he : D.erg G.1 = some τ,
        X.gleich (semZ O passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc))) →
      X.gleich (semZ O passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfOk P O passes ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, κ, hreq, hf, hv, hk, hok, hreqκ, hglκ, hcont⟩ := hW
  have hmem : (⟨G.1, κ, G.2.1, antwortWelt e0 s1 κ, v⟩ : Eintrag D) ∈
      H ++ [⟨G.1, κ, G.2.1, antwortWelt e0 s1 κ, v⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, antwortWelt e0 s1 κ, v⟩], antwortWelt e0 s1 κ, hreq,
    funk_append hf hk _ (Nat.le_refl _), ?_, ?_, ?_, hok' hok, ?_⟩
  · intro g σ ρ σa w hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv g σ ρ σa w hm
    · rw [List.mem_singleton] at hm
      cases hm
      refine ⟨hreqκ, ens_transfer hens ?_ ?_⟩
      · exact GleichAuf.mono (fun _ h => List.mem_append_right _ h) hglκ.symm
      · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_succ_of_lt (hk e hm)
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · exact ⟨fun t _ => congrFun hW'.1.symm t, fun g _ => congrFun hW'.2.symm g⟩
  · intro R hR
    have hans := hR _ _ _ _ _ hmem
    obtain ⟨c1, c2⟩ := hcont R (passt_append hR) _ v hans
    exact hwahl R _ _ c1 c2

/-- **The call leg.** At a call of the head frame, the recorded handler
    gated by `requires` (`torRuf`) repeats the record; if the callee's
    `requires` failed at the sequential key world, the body's run with it
    would end in `logik (vorbedingung g)`, which `KoerperGut`'s caller duty
    excludes. So `requires` holds at the key world -- and at the machine's
    entry world, which agrees with it on the callee's contract carriers. -/
theorem push_req (hK : ∀ f, KoerperGut P O passes f) {F : RufRahmenG D}
    {H : List (Eintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : Funk H) (hv : VertraegeOk P H)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D F.f) O passes R (P.rumpf F.f) F.s0 F.rho)).gleich
        (semZ O passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ R (e : Logik D), R g κ ρk = .logik e → semZ O passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAus H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have h1 := heq _ (torRuf_passt (rufAus_passt hf) hv)
      rw [hlogik _ _ htor] at h1
      have hex := zErg_gleich_logik h1
      exact (hK F.f (rufAus H) (rufAus_respektiert hv) (rufAus_ohneVorbedingung H) F.s0 F.rho
        hreq).2 g hex

end Rufe

section Push

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- The residue a pending call leaves: how the call continues once the
    handler answers, for a plain call or a bind-call. -/
def PushWeiter (O : Orakel D) (passes : Nat) {V : Vertrag D} (g : D.Fn)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc) (rc : GRest D V lc Γc Λc)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (σa : World D)
    (v : ErgVal D (D.erg g)) : Prop :=
  (rc.wartend = false → semZ O passes R r σ ρ = semZ O passes R rc σa ρc) ∧
  (∀ (l' : Bool) (Γ' : Ctx) (Λ₁ Λ₂ : List (Res D)) (τ : Ty)
      (restb : Block D V l' (τ :: Γ') Λ₁ Λ₂) (k : GRest D V l' Γ' Λ₂) (ρc' : Env D Γ'),
    (⟨lc, Γc, Λc, ρc, rc⟩ :
      Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) =
      ⟨l', Γ', Λ₁, ρc', .wartet restb k⟩ →
    ∀ he : D.erg g = some τ,
      semZ O passes R r σ ρ = semZ O passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc'))

/-- **A push keeps the replay.** The head frame calls `g` with `args`; it
    becomes a suspended frame with the continuation `rc`, and the callee's
    frame becomes a fresh replayed head (empty record, sequential world =
    machine entry world). The callee's `requires` holds at the machine's
    entry world (`push_req`), for the log. -/
theorem push_ok (hK : ∀ f, KoerperGut P O passes f) (hFrag : ∀ f, (P.rumpf f).kOk = true)
    {z : RufFadenG D} {W : World D} (hF : FadenOk P O passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hS : r.okZ P (fussOrte P z.kopf.f) → args.orte ⊆ fussOrte P z.kopf.f ∧
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrte P z.kopf.f)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okZ P (fussOrte P z.kopf.f) → rc.okZ P (fussOrte P z.kopf.f))
    (hlogik : ∀ R σ (e : Logik D),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .logik e → semZ O passes R r σ ρ = .logik e)
    (hweiter : ∀ R σ (σa : World D) (v : ErgVal D (D.erg g)),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .ok σa v → PushWeiter O passes g r σ ρ ρc rc R σa v) :
    FadenOk P O passes
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ, W.lese Λ args.orte,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g),
            evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ, .ende (P.rumpf g)⟩⟩,
        (W.lese Λ args.orte).spur,
        RufEreignisF.eintritt g (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ)
          (W.lese Λ args.orte) :: z.log⟩
      (W.lese Λ args.orte) ∧
    ReqAmEintritt P g (W.lese Λ args.orte)
      (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ) := by
  obtain ⟨⟨H, σ, hreq, hf, hv, hk, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okZ P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ R, Passt R H →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).gleich (semZ O passes R r σ ρ) := by
    intro R hR
    have := heq R hR
    rw [hr] at this
    exact this
  obtain ⟨hargs, hctr⟩ := hS hok'
  have hgκ : GleichAuf (fussOrte P z.kopf.f) (σ.lese Λ args.orte) (W.lese Λ args.orte) :=
    hg.lese Λ Λ args.orte args.orte
  have hρk : evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ =
      evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ :=
    evalArgs_gleichAuf args (fun _ h => hargs h) hgκ ρ
  have hreqκ := push_req hK hreq hf hv r heq' g (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) (fun R e h => hlogik R σ e h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ args.orte)
      (W.lese Λ args.orte) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], W.lese Λ args.orte, hreq0, funk_nil, vertraegeOk_nil P, kurzH_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpf P g⟩, fun R _ => ZErg.gleich_refl _⟩,
    ⟨H, σ.lese Λ args.orte, hreq, hf, hv, kurzH_mono hk (lese_laenge _ _ _), hrc hok', hreqκ,
      hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R hR σa v hRa
  rw [← hρk] at hRa
  obtain ⟨w1, w2⟩ := hweiter R σ σa v hRa
  exact ⟨fun hnw => ZErg.gleich_trans (heq' R hR) (ZErg.gleich_of_eq (w1 hnw)),
    fun l' Γ' Λ₁ Λ₂ τ restb k ρc' h he => ZErg.gleich_trans (heq' R hR)
      (ZErg.gleich_of_eq (w2 l' Γ' Λ₁ Λ₂ τ restb k ρc' h he))⟩

end Push

/-! ## 5. The acting thread keeps its replay -/

section Akteur

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem teile2 {α : Type} {a b c S : List α} (h : a ++ b ++ c ⊆ S) :
    a ⊆ S ∧ b ⊆ S ∧ c ⊆ S := by
  simp only [List.append_subset] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem and_teile {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true _ _ |>.mp h

/-- **The acting thread keeps its replay and its log** -- every rule of G:
    the head-local steps of the fragment by the residue step lemmas at the
    sequential world, the pushes by `push_ok`, the pops by `pop_ens` and
    `pop_kopf`; every rule outside the fragment finds a head residue that is
    not in it. -/
theorem akteur (hK : ∀ f, KoerperGut P O passes f) (hFrag : ∀ f, (P.rumpf f).kOk = true)
    (e0 : Ereignis D) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (hF : FadenOk P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log) :
    FadenOk P O passes (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | blatt l Γ Λ Λ' s rest ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ' (.ende rest) σ'.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_ende_cons hok
    obtain ⟨σs, hes, hgs, hls⟩ := blatt_lokal P O passes s hks hleaf (fun o ho => hss ho) hg hstep
    exact ⟨σs, hls, hgs, hrest, fun R => ZErg.gleich_of_eq (semZ_blatt O passes R s rest σ σs ρ ρ'
      (by rw [istBlatt_R O passes R hleaf]; exact hes))⟩
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep hneu hkein =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ' (.dann rest k) σ'.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    obtain ⟨σs, hes, hgs, hls⟩ := blatt_lokal P O passes s hks hleaf (fun o ho => hss ho) hg hstep
    exact ⟨σs, hls, hgs, hrest, fun R => ZErg.gleich_of_eq (semZ_dannBlatt O passes R s rest k σ σs
      ρ ρ' (by rw [istBlatt_R O passes R hleaf]; exact hes))⟩
  | endeEntf l Γ Λ Λ' s rest ρ hent hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann (.cons s .nil) (.ende rest)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_ende_cons hok
    refine ⟨σ, Nat.le_refl _, hg, ⟨by simp [Block.kOk, hks], ?_, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_endeEntf O passes R s rest σ ρ)⟩
    simpa [blockOrteP] using hss
  | dannLeer l Γ Λ k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok.2.2, fun R => ZErg.gleich_of_eq (semZ_dannLeer O passes R k σ ρ)⟩
  | dannIteWahr l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann t (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    obtain ⟨ht, _⟩ := and_teile hks
    obtain ⟨hc, htS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨ht, htS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_iteWahr O passes R c t e rest k σ ρ hw')⟩
  | dannIteFalsch l Γ Λ Λ' Λ'' c t e rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann e (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    obtain ⟨_, he⟩ := and_teile hks
    obtain ⟨hc, _, heS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨he, heS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_iteFalsch O passes R c t e rest k σ ρ hw')⟩
  | dannOnOptionSome l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.dann p (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    obtain ⟨hp, _⟩ := and_teile hks
    obtain ⟨hc, hpS, _⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v := by
      rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨hp, hpS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_optSome O passes R o p a rest k σ ρ v hv')⟩
  | dannOnOptionNone l Γ Λ Λ' Λ'' n o p a rest k ρ hhead σ₁ hs₁ hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann a (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    obtain ⟨_, ha⟩ := and_teile hks
    obtain ⟨hc, _, haS⟩ := teile2 hss
    have hv' : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none := by
      rw [eval_gleichAuf o (fun _ h => hc h) (hg.lese Λ Λ o.orte o.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ o.orte, lese_laenge _ _ _, hg, ⟨ha, haS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_optNone O passes R o p a rest k σ ρ hv')⟩
  | dannOnTagSome l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ lo hi b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k))) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
        ⟨some (lo, hi), b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_kOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_tagSome O passes R v arms rest k σ ρ lo hi b nutz hw')⟩
  | dannOnTagNone l Γ Λ Λ' Λ'' cs v arms rest k ρ hhead σ₁ hs₁ b nutz hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (armEnv nutz ρ) (.dann b (.dann rest k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hw' : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩ := by
      rw [eval_gleichAuf v (fun _ h => hss.1 h) (hg.lese Λ Λ v.orte v.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ v.orte, lese_laenge _ _ _, hg,
      ⟨armWahlG_kOk' arms _ hw' hks, fun _ h => hss.2 (armWahlG_orteP' arms _ hw' h), hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_tagNone O passes R v arms rest k σ ρ b nutz hw')⟩
  | dannOnGrund l Γ Λ Λ' Λ'' n r arms rest k ρ hhead σ₁ hs₁ b hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann b (.dann rest k)) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    simp only [stmtOrteP, List.append_subset] at hss
    have hb : grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ) = b := by
      rw [eval_gleichAuf r (fun _ h => hss.1 h) (hg.lese Λ Λ r.orte r.orte) ρ, ← hs₁]; exact hw
    refine ⟨σ.lese Λ r.orte, lese_laenge _ _ _, hg, ⟨?_, ?_, hrest⟩, fun R => ?_⟩
    · rw [← hb]; exact grundWahlG_kOk arms _ hks
    · rw [← hb]; exact fun _ h => hss.2 (grundWahlG_orteP arms _ h)
    · rw [← hb]; exact ZErg.gleich_of_eq (semZ_grund O passes R r arms rest k σ ρ)
  | endeBind l Γ Λ τ e rest ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.ende rest) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss⟩ := hok
    simp only [endblockOrteP, List.append_subset] at hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2⟩, fun R => ?_⟩
    have h1 := semZ_endeBind O passes R e rest σ ρ
    rw [he'] at h1
    exact ZErg.gleich_of_eq h1
  | dannBind l Γ Λ Λ' Λ'' τ e rest k ρ hhead σ₁ hs₁ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons (eval σ₁ e σ₁ ρ) ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩, fun R => ?_⟩
    have h1 := semZ_dannBind O passes R e rest k σ ρ
    rw [he'] at h1
    exact ZErg.gleich_of_eq h1
  | dannNarrowOk l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead _ (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hes, _, hrS⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := by rw [he']; exact h
    refine ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩, fun R => ?_⟩
    have h1 := semZ_narrowOk O passes R e lo' hi' sonst rest k σ ρ h'
    have hz : (⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h'.1, h'.2⟩ :
        Wert D (.int lo' hi')) = ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩ := by
      simp only [he']
    rw [hz] at h1
    exact ZErg.gleich_of_eq h1
  | dannNarrowElse l Γ Λ Λ' Λ'' lo hi lo' hi' e sonst rest k ρ hhead σ₁ hs₁ h neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have he' : eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ = eval σ₁ e σ₁ ρ := by
      rw [hs₁]; exact eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ
    have h' : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') := by rw [he']; exact h
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg,
      ⟨by rw [Endblock.kOk_alsBlock]; exact hkS, by rw [blockOrteP_alsBlock]; exact hsS, hrk⟩,
      fun R => ZErg.gleich_of_eq ((semZ_alsBlock O passes R sonst k _ ρ).trans
        (semZ_narrowElse O passes R e lo' hi' sonst rest k σ ρ h'))⟩
  | dannPruefWahr l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann rest k) σ₁.spur (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hc, _, hrS⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_pruefWahr O passes R c sonst rest k σ ρ hw')⟩
  | dannPruefFalsch l Γ Λ Λ' Λ'' c sonst rest k ρ hhead σ₁ hs₁ hw neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hc, hsS, _⟩ := teile2 hss
    have hw' : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false := by
      rw [eval_gleichAuf c (fun _ h => hc h) (hg.lese Λ Λ c.orte c.orte) ρ, ← hs₁]; exact hw
    exact ⟨σ.lese Λ c.orte, lese_laenge _ _ _, hg,
      ⟨by rw [Endblock.kOk_alsBlock]; exact hkS, by rw [blockOrteP_alsBlock]; exact hsS, hrk⟩,
      fun R => ZErg.gleich_of_eq ((semZ_alsBlock O passes R sonst k _ ρ).trans
        (semZ_pruefFalsch O passes R c sonst rest k σ ρ hw'))⟩
  | dannBreaking l Γ Λ Λ' Λ'' i body rest k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann body (.dann rest k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_breaking O passes R i body rest k σ ρ)⟩
  | dannLocks l Γ Λ Λ'' L hr body rest k ρ hhead hself hrang hfrei =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann body (.frei L (.dann rest k)))
      (Ereignis.nimmt L (offen (M.faeden u).spur) :: (M.faeden u).spur) (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := okZ_dann_cons hok
    exact ⟨σ.nimmt L, Nat.le_succ _, hg, ⟨hks, hss, hrest⟩,
      fun R => semZ_locks O passes R L hr body rest k σ ρ⟩
  | freiGib l Γ Λ L k ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ k (Ereignis.gibt L :: (M.faeden u).spur)
      (fun σ hg hok => ?_), hL⟩
    exact ⟨σ.gibt L, Nat.le_succ _, hg, hok, fun R => ZErg.gleich_of_eq (semZ_frei O passes R L k σ ρ)⟩
  | schrumpfVergiss l Γ Λ τ k v ρ hhead =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
    exact ⟨σ, Nat.le_refl _, hg, hok, fun R => ZErg.gleich_of_eq (semZ_schrumpf O passes R k σ v ρ)⟩
  | dannExchange l Γ Λ Λ' g neuE hw hLg rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₂.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.cons_subset, List.append_subset] at hss
    obtain ⟨⟨hgS, hnS⟩, hrS⟩ := hss
    subst hs₂ hs₁
    have hgl := hg.lese Λ Λ (.inr g :: neuE.orte) (.inr g :: neuE.orte)
    have hglob : (σ.lese Λ (.inr g :: neuE.orte)).globs g =
        ((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g := hgl.2 g hgS
    have hval : eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
        (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) =
        eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ) :=
      eval_gleichAuf neuE (fun _ h => hnS h) hgl _
    refine ⟨(σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
        (eval ((M.weltVon u).lese Λ (.inr g :: neuE.orte)) neuE
          ((M.weltVon u).lese Λ (.inr g :: neuE.orte))
          (.cons (((M.weltVon u).lese Λ (.inr g :: neuE.orte)).globs g) ρ)),
      spur_laenge_erw ((Erw.lese _ _ _).trans (Erw.schreibGlob _ _ _ _)),
      gleichAuf_schreibGlob hgl g Λ Λ _, ⟨hks, hrS, hrest⟩, fun R => ?_⟩
    have h1 := semZ_exchange O passes R g neuE hw hLg rest k σ ρ
    rw [hglob, hval] at h1
    exact ZErg.gleich_of_eq h1
  | dannGleit l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨haS, hbS, hrS⟩ := teile2 hss
    have hgl := hg.lese Λ Λ (a.orte ++ b.orte) (a.orte ++ b.orte)
    have hv' : gleitPasst lo hi (gleitRechne op
        (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
        (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v := by
      rw [eval_gleichAuf a (fun _ h => haS h) hgl ρ, eval_gleichAuf b (fun _ h => hbS h) hgl ρ,
        ← hs₁]
      exact hv
    exact ⟨σ.lese Λ (a.orte ++ b.orte), lese_laenge _ _ _, hg, ⟨hks, hrS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_gleit O passes R op a b lo hi rest k σ ρ v hv')⟩
  | dannGleitLit l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) (M.faeden u).spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    exact ⟨σ, Nat.le_refl _, hg, ⟨hks, hss, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_gleitLit O passes R q lo hi rest k σ ρ v hv)⟩
  | dannGleitVon l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    simp only [blockOrteP, List.append_subset] at hss
    have hv' : gleitPasst lo hi (gleitAusInt (eval (σ.lese Λ e.orte) e
        (σ.lese Λ e.orte) ρ).n) = some v := by
      rw [eval_gleichAuf e (fun _ h => hss.1 h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hks, hss.2, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_gleitVon O passes R e lo hi rest k σ ρ v hv')⟩
  | dannGleitNarrowOk l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrest⟩ := hok
    obtain ⟨_, hkr⟩ := and_teile hks
    obtain ⟨hes, _, hrS⟩ := teile2 hss
    have hv' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v := by
      rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hv
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg, ⟨hkr, hrS, hrest⟩,
      fun R => ZErg.gleich_of_eq (semZ_gleitNarrowOk O passes R e lo hi sonst rest k σ ρ v hv')⟩
  | dannGleitNarrowElse l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    refine ⟨fadenOk_lokal hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur
      (fun σ hg hok => ?_), hL⟩
    obtain ⟨hks, hss, hrk⟩ := hok
    obtain ⟨hkS, _⟩ := and_teile hks
    obtain ⟨hes, hsS, _⟩ := teile2 hss
    have hn' : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none := by
      rw [eval_gleichAuf e (fun _ h => hes h) (hg.lese Λ Λ e.orte e.orte) ρ, ← hs₁]; exact hn
    exact ⟨σ.lese Λ e.orte, lese_laenge _ _ _, hg,
      ⟨by rw [Endblock.kOk_alsBlock]; exact hkS, by rw [blockOrteP_alsBlock]; exact hsS, hrk⟩,
      fun R => ZErg.gleich_of_eq ((semZ_alsBlock O passes R sonst k _ ρ).trans
        (semZ_gleitNarrowElse O passes R e lo hi sonst rest k σ ρ hn'))⟩
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := push_ok hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okZ_ende_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact ⟨hss.1, List.append_subset.mpr hss.2⟩)
      ρ (.ende rest) (fun hok => (okZ_ende_cons hok).2.2)
      (fun R σ e h => semZ_ruf_logik O passes R g args hp hr rest σ ρ e h)
      (fun R σ σa v h => ⟨fun _ => semZ_ruf O passes R g args hp hr rest σ ρ σa v h,
        fun _ _ _ _ _ _ _ _ he => by cases he⟩)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := push_ok hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := okZ_dann_cons hok
        simp only [stmtOrteP, List.append_subset] at hss
        exact ⟨hss.1, List.append_subset.mpr hss.2⟩)
      ρ (.dann rest k) (fun hok => (okZ_dann_cons hok).2.2)
      (fun R σ e h => semZ_rufDann_logik O passes R g args hp hr rest k σ ρ e h)
      (fun R σ σa v h => ⟨fun _ => semZ_rufDann O passes R g args hp hr rest k σ ρ σa v h,
        fun _ _ _ _ _ _ _ _ he => by cases he⟩)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0 hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    obtain ⟨hFad, hReq⟩ := push_ok hK hFrag hF hhead g args
      (fun hok => by
        obtain ⟨_, hss, _⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hss.1.1, List.append_subset.mpr hss.1.2⟩)
      ρ (.wartet rest k)
      (fun hok => by
        obtain ⟨hks, hss, hk⟩ := hok
        simp only [blockOrteP, List.append_subset] at hss
        exact ⟨hks, hss.2, hk⟩)
      (fun R σ e h => semZ_bindCall_logik O passes R g args he hp hr rest k σ ρ e h)
      (fun R σ σa v h => ⟨fun hw => by simp [GRest.wartend] at hw,
        fun _ _ _ _ _ _ _ _ heq he' => by
          cases heq
          exact semZ_bindCall O passes R g args he hp hr rest k σ ρ σa v h⟩)
    exact ⟨hFad, logOk_eintritt hL hReq⟩
  -- pops
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopf_okZ hF.1 hhead
    have hens := pop_ens hK hF.1 hhead e hok.2 (fun R σ => semZ_rueck O passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨pop_kopf e0 hWc _ _ hens caller.rest.2.2.2.1 caller.rest.2.2.2.2 id
      (fun R σa X h1 _ => h1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩, logOk_rueck hL hens⟩
  | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
      hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okZ_ende_cons (kopf_okZ hF.1 hhead)
    have hens := pop_ens hK hF.1 hhead e hok.2.1
      (fun R σ => semZ_rueckCons O passes R e hperm rest σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨pop_kopf e0 hWc _ _ hens caller.rest.2.2.2.1 caller.rest.2.2.2.2 id
      (fun R σa X h1 _ => h1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩, logOk_rueck hL hens⟩
  | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
      neu hneu hnw =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okZ_dann_cons (kopf_okZ hF.1 hhead)
    have hens := pop_ens hK hF.1 hhead e hok.2.1
      (fun R σ => semZ_dannRet O passes R e hperm rest k σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    refine ⟨⟨pop_kopf e0 hWc _ _ hens caller.rest.2.2.2.1 caller.rest.2.2.2.2 id
      (fun R σa X h1 _ => h1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩, logOk_rueck hL hens⟩
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := kopf_okZ hF.1 hhead
    have hens := pop_ens hK hF.1 hhead e hok.2 (fun R σ => semZ_rueck O passes R e hperm σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ := by
      rcases hcaller with h | ⟨n, err, h⟩
      · exact h
      · obtain ⟨_, _, _, _, _, _, hokc, _⟩ := hWc
        rw [h] at hokc
        exact hokc.elim
    refine ⟨⟨pop_kopf e0 hWc _ _ hens (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by rw [hc] at hokc; exact ⟨hokc.1, hokc.2.1, hokc.2.2⟩)
      (fun R σa X _ h2 => h2 l Γ Λ Λ' τ restb k ρc hc he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
      hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okZ_dann_cons (kopf_okZ hF.1 hhead)
    have hens := pop_ens hK hF.1 hhead e hok.2.1
      (fun R σ => semZ_dannRet O passes R e hperm restk kk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ := by
      rcases hcaller with h | ⟨n, err, h⟩
      · exact h
      · obtain ⟨_, _, _, _, _, _, hokc, _⟩ := hWc
        rw [h] at hokc
        exact hokc.elim
    refine ⟨⟨pop_kopf e0 hWc _ _ hens (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by rw [hc] at hokc; exact ⟨hokc.1, hokc.2.1, hokc.2.2⟩)
      (fun R σa X _ h2 => h2 l Γ Λ Λ' τ restb k ρc hc he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
      s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
    subst hfg hs0 hs1 hv
    subst hrho
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hok := okZ_ende_cons (kopf_okZ hF.1 hhead)
    have hens := pop_ens hK hF.1 hhead e hok.2.1
      (fun R σ => semZ_rueckCons O passes R e hperm restk σ ρ)
    have hSt := hF.2
    rw [hpop] at hSt
    obtain ⟨hWc, hSt'⟩ := hSt
    have hc : caller.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ := by
      rcases hcaller with h | ⟨n, err, h⟩
      · exact h
      · obtain ⟨_, _, _, _, _, _, hokc, _⟩ := hWc
        rw [h] at hokc
        exact hokc.elim
    refine ⟨⟨pop_kopf e0 hWc _ _ hens (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
      (fun hokc => by rw [hc] at hokc; exact ⟨hokc.1, hokc.2.1, hokc.2.2⟩)
      (fun R σa X _ h2 => h2 l Γ Λ Λ' τ restb k ρc hc he) _ ⟨rfl, rfl⟩, hSt'⟩,
      logOk_rueck hL hens⟩
  -- every other rule: the head residue is outside the fragment
  | _ =>
    exact absurd (kopf_okZ hF.1 ‹(M.faeden u).kopf.rest = _›)
      (by simp [GRest.okZ, Block.kOk, Stmt.kOk, Endblock.kOk])

end Akteur

/-! ## 6. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for the replay.** A step of thread `u` leaves the footprint
    of every live head frame of another thread `t` alone: a footprint
    carrier is guarded by a signature lock of the head function, which `t`
    holds (`rufG_haelt_signatur`) and `u` therefore does not (`exklusivG`),
    or no function writes it (`FussOrtOk`). -/
theorem andere_ok (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenOk P O passes (M.faeden t) (M.weltVon t)) :
    FadenOk P O passes (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenOk_speicher hF (fun c hc => ?_)
  rcases fussOrtB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** Every thread's start frame: empty
    record, sequential world = entry world, `requires` by `StartGut`. -/
theorem zielInv_start (hFrag : ∀ f, (P.rumpf f).kOk = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInv P O passes (RufStartG P sp init) := by
  have hz : ∀ t, (RufStartG P sp init).faeden t =
      ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
        Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
        startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
    intro t
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
    cases init t
    rfl
  refine ⟨fun t => ?_, fun t => ?_⟩
  · unfold RufMaschineG.weltVon
    rw [hz t]
    refine ⟨⟨[], sp.welt [], hStart t, funk_nil, vertraegeOk_nil P, kurzH_nil _,
      GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpf P _⟩, fun R _ => ZErg.gleich_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant. -/
theorem zielInv_schritt (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (hK : ∀ f, KoerperGut P O passes f)
    (hFrag : ∀ f, (P.rumpf f).kOk = true) (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInv P O passes M) :
    ZielInv P O passes M' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteur hK hFrag e0 hs (hI.1 t) (hI.2 t)).1
    · exact andere_ok hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteur hK hFrag e0 hs (hI.1 t) (hI.2 t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **ZIEL AM ORT -- contracts hold at their place on every machine of the
    repaired concurrent call machine G.**

    Premises, by class:
    * (a) user obligations: `KoerperGut P O passes f` for every function
      (the body's Hoare triple over the SEQUENTIAL semantics with any
      contract-respecting handler, and its caller duty), `StartGut` (the
      start functions' `requires` at the start memory) and `StartExklusiv`
      (no two threads start in functions holding a common lock -- the boot
      assignment);
    * (b) hardware: `GutO O`;
    * (c) decidable program facts over a complete member list `fs`: the
      fragment (`programmImFragment`) and the footprint check (`fussOrtB`:
      every carrier a function reads, or its contract or a direct callee's
      contract mentions, is guarded by a lock the function holds by
      signature, or written by no function);
    * the declaration declares a table, a global or a lock (`e0`: an event
      exists; it gives each recorded call answer a fresh trace position).

    Conclusion: on EVERY machine reachable from the start machine, at every
    `eintritt` of every thread log the callee's `requires` holds with the
    actual parameters at the actual entry world, and at every `rueck` the
    `ensures` holds with the actual entry world, return world, parameters
    and result. -/
theorem ziel_ort (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragment P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGut P O passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  have hFragF : ∀ f, (P.rumpf f).kOk = true :=
    fun f => (List.all_eq_true.mp hFrag) f (hvoll f)
  intro M hr
  have hI : ZielInv P O passes M := by
    induction hr with
    | start => exact zielInv_start hFragF sp init hStart
    | schritt M M' u hr' hs ih =>
        exact zielInv_schritt hO hvoll hFuss hK hFragF e0 sp init hex hr' hs ih
  exact fun t ev hev => hI.2 t ev hev

end Ziel

/-! ## CUTS:

  What is proved: `ziel_ort` -- over the repaired G, for every program in
  the fragment whose footprint check passes, whose bodies satisfy
  `KoerperGut`, whose start assignment is exclusive and meets `StartGut`,
  with an oracle satisfying `GutO`, every reachable machine satisfies
  `VertragAmOrtG`. Premises and their use: `GutO` (rely, held locks),
  `hvoll` (member list complete: fragment and footprint per function),
  `programmImFragment` (every residue in the fragment: `okZ`),
  `fussOrtB` (the rely covers the footprint: `andere_ok`), `KoerperGut`
  (the return leg `pop_ens` and the call leg `push_req`), `StartGut`
  (`zielInv_start`), `StartExklusiv` (`exklusivG` in the rely), `e0`
  (fresh trace positions for the record: `pop_kopf`).

  What is NOT covered:

  - Declarations without any table, global and lock (no `e0`). There the
    world has no memory and a single trace, the record's keys collapse to
    (callee, parameters), and a replay needs that two returns of a callee
    with equal parameters return equal values -- a determinism lemma for
    G that is not proved here. (Closed for the lock-invariant replay that
    the goal uses, 2026-09-14: `Begruendet`, `begruendet_eindeutig`,
    SperreBeweis.lean §0b -- the determinism obtained from the replay
    itself; this older replay keeps `e0`.)
  - Bodies outside the fragment `kOk` (loops, `leave`/`next`, the error
    channel, indirect calls, axioms, the oracle forms).
  - `schreiberHaeltB` (the static writer discipline of `ZielOrt.lean`) is
    NOT a premise: the repaired G enforces the writer discipline
    dynamically (every write carries its guards in the static holdings and
    demands `HeldGenau`), and requiring it statically would make every
    guarded carrier that is written at all the property of ONE thread
    forever (a writer's start function would hold the guard by signature).
-/

#print axioms Gabbro.Grammatik.pop_ens
#print axioms Gabbro.Grammatik.pop_kopf
#print axioms Gabbro.Grammatik.push_req
#print axioms Gabbro.Grammatik.push_ok
#print axioms Gabbro.Grammatik.akteur
#print axioms Gabbro.Grammatik.andere_ok
#print axioms Gabbro.Grammatik.ziel_ort

end Gabbro.Grammatik
