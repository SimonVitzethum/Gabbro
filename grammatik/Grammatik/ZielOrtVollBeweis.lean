/-
  File:      Grammatik/ZielOrtVollBeweis.lean
  Subject:   `ziel_ort_voll` -- contracts hold at their place on every machine
             of the repaired concurrent call machine G, for programs whose
             bodies use loops (`traverse`, `retry`, `forever` with its
             budget), the exits `leave`/`next`, the error channel
             (`return` of a reason, `let … else`) and axiom calls.

  The proof is the replay of `ZielOrtBeweis.lean`, widened in four places.

  * The frame semantics is `semV` (`ZielOrtVollSem.lean`): every residue of
    G has a meaning, the loop residues by the sequential loop functions.
  * The body's frame result is PREDICTED by the residue (`ZErg.folgt`),
    not equal to it: G replaces a residue by an end block in some steps,
    and where that end block leaves a loop, G is stuck and predicts nothing.
  * The record of a frame's calls keeps REASON answers too (`EintragV`):
    a callee that returns a reason pops into its caller's `else` block, and
    the caller's replay continues there with the reason bound.
  * Axiom calls are recorded like calls (`AxEintrag`): the sequential run
    uses an oracle that repeats the machine's answers (`orakelAus`) at
    fresh keys. The recorded answer world takes the axiom's declared
    carriers from the machine and everything else from the sequential key
    world, so the recorded oracle respects every axiom's declared frame
    (`RahmenO`). The user obligation for a body that calls an axiom is its
    Hoare triple for EVERY oracle that respects the declared frames
    (`KoerperGutV`): the axiom's answer and its effect inside its frame are
    hardware, the triple may assume nothing else about them.

  What contracts say about reason returns: nothing (`RespektiertVertraege`
  and `EnsAmRueck` are about normal returns). The statement for reasons is
  the machine's own: the logged `grund` event carries the reason the callee
  returned and the caller's `else` block runs with that reason bound
  (`rufG_grund_treu`, `ZielOrtVoll.lean`). The theorem `ziel_ort_voll` is
  in `ZielOrtVoll.lean`, its witness `ziel_ort_voll_zeuge` in
  `ZielOrtVollZeuge.lean`.
-/
import Grammatik.ZielOrtVollSem
import Grammatik.ZielOrtBeweis

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The user obligation: the body triple against the declared frames -/

/-- An oracle respects the declared frame of every axiom: an axiom changes
    only the tables and globals it declares to write. -/
def RahmenO (O : Orakel D) : Prop :=
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1

theorem gutO_rahmenO {O : Orakel D} (hO : GutO O) : RahmenO O := fun a σ ρ => (hO a σ ρ).1

/-- **The user obligation of one function, with axiom calls.** The body
    triple and the caller duty of `KoerperGut`, for EVERY oracle that
    respects the declared axiom frames: what an axiom answers, and what it
    writes inside its frame, is hardware. For a body without axiom calls
    the oracle is never consulted and this is `KoerperGut` itself
    (`koerperGutV_of_kOk`). -/
def KoerperGutV (P : Programm D) (passes : Nat) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → KoerperGut P O' passes f

/-! ## 2. Records: call answers (normal and reason) and axiom answers -/

/-- A recorded call: callee, key world, parameters, answer. -/
abbrev EintragV (D : Deklaration) :=
  Σ g : D.Fn, World D × Env D (D.params g) × RufAusgang g

def FunkV (H : List (EintragV D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (a a' : RufAusgang g),
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H → (⟨g, σ, ρ, a'⟩ : EintragV D) ∈ H → a = a'

def KurzV (N : Nat) (H : List (EintragV D)) : Prop :=
  ∀ e ∈ H, e.2.1.spur.length < N

/-- Every recorded call met the callee's `requires` at its key, every
    recorded normal answer meets its `ensures`, no answer is a logic
    failure. -/
def VertraegeOkV (P : Programm D) (H : List (EintragV D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (a : RufAusgang g),
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H →
      ReqAmEintritt P g σ ρ ∧ (∀ σa v, a = .ok σa v → EnsAmRueck P g σ σa ρ v) ∧
        ∀ e, a ≠ .logik e

def PasstV (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (H : List (EintragV D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (a : RufAusgang g),
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H → R g σ ρ = a

noncomputable def rufAusV (H : List (EintragV D)) :
    ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g :=
  fun g σ ρ =>
    haveI := Classical.propDecidable (∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H)
    if h : ∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H then Classical.choose h
    else .logik (.abstieg g)

theorem rufAusV_passt {H : List (EintragV D)} (hf : FunkV H) : PasstV (rufAusV H) H := by
  intro g σ ρ a hmem
  have hex : ∃ a : RufAusgang g, (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H := ⟨a, hmem⟩
  simp only [rufAusV, dif_pos hex]
  exact hf g σ ρ _ a (Classical.choose_spec hex) hmem

theorem rufAusV_mem {H : List (EintragV D)} {g : D.Fn} {σ : World D} {ρ : Env D (D.params g)}
    {a : RufAusgang g} (h : rufAusV H g σ ρ = a) (hne : ∀ e, a ≠ .logik e) :
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H := by
  unfold rufAusV at h
  split at h
  · rename_i hex
    rw [← h]
    exact Classical.choose_spec hex
  · exact absurd h.symm (hne _)

theorem rufAusV_respektiert {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkV P H) :
    RespektiertVertraege P (rufAusV H) := by
  intro g σ ρ _ σ' v h
  exact (hv g σ ρ _ (rufAusV_mem h (fun e he => by cases he))).2.1 σ' v rfl

theorem rufAusV_ohneVorbedingung {P : Programm D} {H : List (EintragV D)}
    (hv : VertraegeOkV P H) : OhneVorbedingung (rufAusV H) := by
  intro g σ ρ e h g' he
  unfold rufAusV at h
  split at h
  · rename_i hex
    exact (hv g σ ρ _ (Classical.choose_spec hex)).2.2 e h
  · cases h
    cases he

theorem torRuf_passtV {P : Programm D}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {H : List (EintragV D)} (hp : PasstV R H) (hv : VertraegeOkV P H) :
    PasstV (torRuf P R) H := by
  intro g σ ρ a hmem
  have hreq : wahr? (eval σ (P.requires g) σ ρ) = true := (hv g σ ρ a hmem).1
  simp only [torRuf, hreq, if_true]
  exact hp g σ ρ a hmem

theorem passtV_append {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    {H : List (EintragV D)} {e : EintragV D} (h : PasstV R (H ++ [e])) : PasstV R H :=
  fun g σ ρ a hmem => h g σ ρ a (List.mem_append_left _ hmem)

theorem funkV_nil : FunkV ([] : List (EintragV D)) := fun _ _ _ _ _ h => absurd h List.not_mem_nil

theorem vertraegeOkV_nil (P : Programm D) : VertraegeOkV P ([] : List (EintragV D)) :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

theorem kurzV_nil (N : Nat) : KurzV N ([] : List (EintragV D)) :=
  fun _ h => absurd h List.not_mem_nil

theorem kurzV_mono {N N' : Nat} {H : List (EintragV D)} (h : KurzV N H) (hN : N ≤ N') :
    KurzV N' H :=
  fun e he => Nat.lt_of_lt_of_le (h e he) hN

theorem funkV_append {H : List (EintragV D)} (hf : FunkV H) {N : Nat} (hk : KurzV N H)
    (e : EintragV D) (he : N ≤ e.2.1.spur.length) : FunkV (H ++ [e]) := by
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
    have e2 := eq_of_heq (Sigma.mk.inj h2).2
    simp only [Prod.mk.injEq] at e2
    exact e2.2.2.symm

/-! ### Axiom answers -/

/-- A recorded axiom answer: axiom, key world, arguments, answer world and
    raw answer. -/
abbrev AxEintrag (D : Deklaration) :=
  Σ a : D.Ax, World D × Env D (D.aparams a) × (World D × Int)

def FunkA (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x x' : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → (⟨a, σ, ρ, x'⟩ : AxEintrag D) ∈ HA → x = x'

def KurzA (N : Nat) (HA : List (AxEintrag D)) : Prop :=
  ∀ e ∈ HA, e.2.1.spur.length < N

/-- Every recorded answer world lies in the axiom's declared frame around
    its key world. -/
def RahmenA (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → Rahmen (D.aschreibt a) (D.agschreibt a) σ x.1

def PasstA (O' : Orakel D) (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → O'.wirkt a σ ρ = x

/-- The oracle of a record: the recorded answer at a recorded key, the
    machine's oracle everywhere else. -/
noncomputable def orakelAus (O : Orakel D) (HA : List (AxEintrag D)) : Orakel D where
  wirkt := fun a σ ρ =>
    haveI := Classical.propDecidable (∃ x : World D × Int, (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA)
    if h : ∃ x : World D × Int, (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA then Classical.choose h
    else O.wirkt a σ ρ
  regLies := O.regLies
  regSchreib := O.regSchreib
  sichtbar := O.sichtbar

theorem orakelAus_passt (O : Orakel D) {HA : List (AxEintrag D)} (hf : FunkA HA) :
    PasstA (orakelAus O HA) HA := by
  intro a σ ρ x hmem
  have hex : ∃ x : World D × Int, (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA := ⟨x, hmem⟩
  simp only [orakelAus, dif_pos hex]
  exact hf a σ ρ _ x (Classical.choose_spec hex) hmem

theorem orakelAus_rahmen {O : Orakel D} (hO : GutO O) {HA : List (AxEintrag D)}
    (hr : RahmenA HA) : RahmenO (orakelAus O HA) := by
  intro a σ ρ
  simp only [orakelAus]
  split
  · rename_i hex
    exact hr a σ ρ _ (Classical.choose_spec hex)
  · exact (hO a σ ρ).1

theorem passtA_append {O' : Orakel D} {HA : List (AxEintrag D)} {e : AxEintrag D}
    (h : PasstA O' (HA ++ [e])) : PasstA O' HA :=
  fun a σ ρ x hmem => h a σ ρ x (List.mem_append_left _ hmem)

theorem funkA_nil : FunkA ([] : List (AxEintrag D)) := fun _ _ _ _ _ h => absurd h List.not_mem_nil

theorem rahmenA_nil : RahmenA ([] : List (AxEintrag D)) := fun _ _ _ _ h => absurd h List.not_mem_nil

theorem kurzA_nil (N : Nat) : KurzA N ([] : List (AxEintrag D)) :=
  fun _ h => absurd h List.not_mem_nil

theorem kurzA_mono {N N' : Nat} {HA : List (AxEintrag D)} (h : KurzA N HA) (hN : N ≤ N') :
    KurzA N' HA :=
  fun e he => Nat.lt_of_lt_of_le (h e he) hN

theorem funkA_append {HA : List (AxEintrag D)} (hf : FunkA HA) {N : Nat} (hk : KurzA N HA)
    (e : AxEintrag D) (he : N ≤ e.2.1.spur.length) : FunkA (HA ++ [e]) := by
  intro a σ ρ x x' h1 h2
  rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
  · exact hf a σ ρ x x' h1 h2
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
    have e2 := eq_of_heq (Sigma.mk.inj h2).2
    simp only [Prod.mk.injEq] at e2
    exact e2.2.2.symm

/-- The recorded answer world of an axiom call: the axiom's declared
    carriers from the machine's answer world `σ₂`, every other carrier from
    the sequential key world `κ`, one fresh trace event past `κ`. -/
def axWelt (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) : World D :=
  ⟨fun t => if D.aschreibt a t = true then σ₂.slots t else κ.slots t,
   fun g => if D.agschreibt a g = true then σ₂.globs g else κ.globs g, e0 :: κ.spur⟩

theorem axWelt_rahmen (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) :
    Rahmen (D.aschreibt a) (D.agschreibt a) κ (axWelt e0 a κ σ₂) := by
  refine ⟨fun t ht k f => ?_, fun g hg => ?_⟩
  · show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) k f = κ.slots t k f
    rw [if_neg (by simp [ht])]
  · show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = κ.globs g
    rw [if_neg (by simp [hg])]

/-- The recorded answer world agrees with the machine's answer world on
    every carrier on which the key world agreed with the machine's call
    world: declared carriers come from the machine, the others are kept by
    both (the machine's oracle respects the frame, `GutO`). -/
theorem axWelt_gleichAuf {S : List (D.Tab ⊕ D.Glob)} (e0 : Ereignis D) (a : D.Ax)
    {κ σ₁ σ₂ : World D} (hg : GleichAuf S κ σ₁)
    (hr : Rahmen (D.aschreibt a) (D.agschreibt a) σ₁ σ₂) :
    GleichAuf S (axWelt e0 a κ σ₂) σ₂ := by
  refine ⟨fun t ht => ?_, fun g hg' => ?_⟩
  · show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
    split
    · rfl
    · rename_i hw
      rw [hg.1 t ht]
      funext k f
      exact (hr.1 t (by simpa using hw) k f).symm
  · show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
    split
    · rfl
    · rename_i hw
      rw [hg.2 g hg']
      exact (hr.2 g (by simpa using hw)).symm

/-! ## 3. The replay invariants -/

section Inv

variable (P : Programm D) (passes : Nat)

/-- **The replay of a head frame** `F` whose thread world is `W`: records of
    its calls `H` and its axiom calls `HA` (functions of their keys, keys
    below the sequential trace, call answers respecting the callees'
    contracts, axiom answers inside their frames), a sequential world `σ`
    agreeing with `W` on the footprint, the residue in the fragment; and
    for ANY handler and ANY oracle repeating the records, the residue run
    from `σ` predicts the body's result. -/
def KopfV (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ KurzA σ.spur.length HA ∧
    GleichAuf (fussOrte P F.f) σ W ∧ F.rest.2.2.2.2.okV P (fussOrte P F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- How a suspended frame `F` continues once its pending call to `g` is
    answered with `a`, predicted for the body's result `X`: a normal answer
    resumes the frame (plain call) or binds the value (`let`, with or
    without `else`); a reason answer runs the `else` block with the reason
    bound. -/
def FortV (F : RufRahmenG D) (g : D.Fn) (X : ZErg (vertragVon D F.f))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D) :
    RufAusgang g → Prop
  | .ok σa v =>
      (F.wartend = false → X.folgt (semV O' passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        (F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.grund n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semV O' passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .grund σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.grund n :: Γ) Λ)
        (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
        (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ →
        ∀ hn : D.gruende g = n,
          X.folgt (semV O' passes R (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σa
            (.cons (Fin.cast hn r) ρc))
  | _ => True

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G`: records, the sequential key world `κ` of the pending call (the
    callee's `requires` holds there; it agrees with the callee's machine
    entry world on the callee's contract carriers), and for any handler and
    oracle repeating the records, the continuation after the handler's
    answer to the pending call predicts the body's result. -/
def WarteV (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkV P H ∧ KurzV κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ KurzA κ.spur.length HA ∧
    F.rest.2.2.2.2.okV P (fussOrte P F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA →
      FortV passes F G.1
        (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)) R O'
        (R G.1 κ G.2.1)

def StapelV : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteV P passes F G ∧ StapelV (RufSchluesselG F) rest

def FadenV (z : RufFadenG D) (W : World D) : Prop :=
  KopfV P passes z.kopf W ∧ StapelV P passes (RufSchluesselG z.kopf) z.stapel

def ZielInvV (M : RufMaschineG D) : Prop :=
  (∀ t, FadenV P passes (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv

theorem logOk_grund {P : Programm D} {log : List (RufEreignisF D)} (h : LogOk P log)
    {g : D.Fn} {rho : Env D (D.params g)} {r : Fin (D.gruende g)} {s0 s1 : World D} :
    LogOk P (RufEreignisF.grund g rho r s0 s1 :: log) := by
  intro ev hev
  rcases List.mem_cons.mp hev with rfl | hev
  · refine ⟨fun g' rho' s0' h' => ?_, fun g' rho' v' s0' s1' h' => ?_⟩ <;> cases h'
  · exact h ev hev

/-- `FortV` is monotone in the predicted result. -/
theorem fortV_mono {passes : Nat} {F : RufRahmenG D} {g : D.Fn} {X Y : ZErg (vertragVon D F.f)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {O' : Orakel D}
    (hXY : X.folgt Y) : ∀ {a : RufAusgang g}, FortV passes F g Y R O' a → FortV passes F g X R O' a
  | .ok _ _, h => ⟨fun hw => ZErg.folgt_trans hXY (h.1 hw),
      fun l Γ Λ Λ' τ restb k ρc hc he => ZErg.folgt_trans hXY (h.2 l Γ Λ Λ' τ restb k ρc hc he)⟩
  | .grund _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErg.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 4. The steps of the replay -/

section Schritte

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem kopfV_okV {F : RufRahmenG D} {W : World D} (h : KopfV P passes F W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D F.f) l Γ Λ} (hr : F.rest = ⟨l, Γ, Λ, ρ, r⟩) :
    r.okV P (fussOrte P F.f) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hok, _⟩ := h
  rw [hr] at hok
  exact hok

/-- **A head-local step without a new record** keeps the replay: the
    residue moves by a step of the frame semantics whose new prediction
    refines the old one. -/
theorem fadenV_lokal {z : RufFadenG D} {W W' : World D} (hF : FadenV P passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (hstep : ∀ σ : World D, GleichAuf (fussOrte P z.kopf.f) σ W →
      r.okV P (fussOrte P z.kopf.f) →
      ∃ σ', σ.spur.length ≤ σ'.spur.length ∧ GleichAuf (fussOrte P z.kopf.f) σ' W' ∧
        r'.okV P (fussOrte P z.kopf.f) ∧
        ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
          (semV O' passes R r σ ρ).folgt (semV O' passes R r' σ' ρ')) :
    FadenV P passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩ W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hS⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  obtain ⟨σ', hl, hg', hok'', hsem⟩ := hstep σ hg hok'
  refine ⟨⟨H, HA, σ', hreq, hf, hv, kurzV_mono hk hl, hfa, hra, kurzA_mono hka hl, hg', hok'',
    fun R O' hR hA => ?_⟩, hS⟩
  have h1 := heq R O' hR hA
  rw [hr] at h1
  exact ZErg.folgt_trans h1 (hsem R O')

/-- Memory moved outside the head's footprint keeps the replay. -/
theorem fadenV_speicher {z : RufFadenG D} {W W' : World D} (hF : FadenV P passes z W)
    (hw : ∀ c ∈ fussOrte P z.kopf.f, TraegerGleich W'.speicher W.speicher c) :
    FadenV P passes z W' := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hS⟩ := hF
  refine ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, ⟨fun t ht => ?_, fun g hg' => ?_⟩, hok,
    heq⟩, hS⟩
  · exact (hg.1 t ht).trans (hw (.inl t) ht).symm
  · exact (hg.2 g hg').trans (hw (.inr g) hg').symm

/-- **The return leg.** -/
theorem popV_ens (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f) {G : RufRahmenG D}
    {W : World D} (hG : KopfV P passes G W) {lr : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {r : GRest D (vertragVon D G.f) lr Γ Λ} (hr : G.rest = ⟨lr, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (he : e.orte ⊆ fussOrte P G.f)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), (semV O' passes R r σ ρ).gleich
        (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho
      (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) := by
  obtain ⟨H, HA, σ, hreq, hf, hv, _, hfa, hra, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (rufAusV_passt hf) (orakelAus_passt O hfa)
  rw [hr] at h1
  simp only at h1
  have h2 := ZErg.folgt_zurueck (ZErg.folgt_trans h1 (ZErg.folgt_of_gleich (hsem _ _ σ)))
  obtain ⟨σ'', hex, hsg⟩ := zErg_gleich_zurueck h2
  have hE := (hK G.f (orakelAus O HA) (orakelAus_rahmen hO hra) (rufAusV H)
    (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) G.s0 G.rho hreq).1 σ'' _ hex
  have hgl : GleichAuf (fussOrte P G.f) (σ.lese Λ e.orte) (W.lese Λ e.orte) :=
    hg.lese Λ Λ e.orte e.orte
  rw [evalErg_gleichAuf e (fun _ h => he h) hgl ρ] at hE
  exact ens_transfer hE (GleichAuf.refl _ _)
    (GleichAuf.mono (fun _ h => fuss_ens P G.f h) ((gleichAuf_SG hsg).trans hgl))

/-- **The call leg.** -/
theorem pushV_req (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f) {F : RufRahmenG D}
    {H : List (EintragV D)} {HA : List (AxEintrag D)} {σ : World D}
    (hreq : ReqAmEintritt P F.f F.s0 F.rho) (hf : FunkV H) (hv : VertraegeOkV P H)
    (hfa : FunkA HA) (hra : RahmenA HA)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    (r : GRest D (vertragVon D F.f) l Γ Λ)
    (heq : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA →
      (zErg (execEnd (V := vertragVon D F.f) O' passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semV O' passes R r σ ρ))
    (g : D.Fn) (κ : World D) (ρk : Env D (D.params g))
    (hlogik : ∀ (O' : Orakel D) R (e : Logik D), R g κ ρk = .logik e →
      semV O' passes R r σ ρ = .logik e) :
    ReqAmEintritt P g κ ρk := by
  cases hq : wahr? (eval κ (P.requires g) κ ρk) with
  | true => exact hq
  | false =>
      exfalso
      have htor : torRuf P (rufAusV H) g κ ρk = .logik (.vorbedingung g) := by
        simp only [torRuf, hq]
        rfl
      have h1 := heq _ (orakelAus O HA) (torRuf_passtV (rufAusV_passt hf) hv)
        (orakelAus_passt O hfa)
      rw [hlogik _ _ _ htor] at h1
      have hex := zErg_gleich_logik (ZErg.folgt_logik h1)
      exact (hK F.f (orakelAus O HA) (orakelAus_rahmen hO hra) (rufAusV H)
        (rufAusV_respektiert hv) (rufAusV_ohneVorbedingung hv) F.s0 F.rho hreq).2 g hex

/-- **The caller resumes** after its pending call to `G` was answered by
    `mk` (a normal answer, whose `ensures` holds at the machine's return
    world `s1`, or a reason): the answer is recorded at the pending key with
    the machine's memory and a fresh trace position, and the frame becomes a
    replayed head with the continuation `r'` chosen by the pop. -/
theorem popV_kopf (e0 : Ereignis D) {F : RufRahmenG D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D}
    (hW : WarteV P passes F G) (s1 : World D) (mk : World D → RufAusgang G.1)
    (hmk : (∃ v, (∀ σa, mk σa = .ok σa v) ∧ EnsAmRueck P G.1 G.2.2 s1 G.2.1 v) ∨
      (∃ r, ∀ σa, mk σa = .grund σa r))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ' : Env D Γ) (r' : GRest D (vertragVon D F.f) l Γ Λ)
    (hok' : F.rest.2.2.2.2.okV P (fussOrte P F.f) → r'.okV P (fussOrte P F.f))
    (hwahl : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (σa : World D) (X : ZErg (vertragVon D F.f)),
      FortV passes F G.1 X R O' (mk σa) → X.folgt (semV O' passes R r' σa ρ'))
    (W' : World D) (hW' : W'.slots = s1.slots ∧ W'.globs = s1.globs) :
    KopfV P passes ⟨F.f, F.rho, F.s0, ⟨l, Γ, Λ, ρ', r'⟩⟩ W' := by
  obtain ⟨H, HA, κ, hreq, hf, hv, hk, hfa, hra, hka, hok, hreqκ, hglκ, hcont⟩ := hW
  have hmem : (⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩ : EintragV D) ∈
      H ++ [⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩] :=
    List.mem_append_right _ List.mem_cons_self
  refine ⟨H ++ [⟨G.1, κ, G.2.1, mk (antwortWelt e0 s1 κ)⟩], HA, antwortWelt e0 s1 κ, hreq,
    funkV_append hf hk _ (Nat.le_refl _), ?_, ?_, hfa, hra,
    kurzA_mono hka (Nat.le_succ _), ?_, hok' hok, ?_⟩
  · intro g σ ρ a hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hv g σ ρ a hm
    · rw [List.mem_singleton] at hm
      cases hm
      refine ⟨hreqκ, ?_, ?_⟩
      · intro σa w hw
        rcases hmk with ⟨v, hv', hens⟩ | ⟨rr, hr'⟩
        · rw [hv'] at hw
          cases hw
          refine ens_transfer hens ?_ ?_
          · exact GleichAuf.mono (fun _ h => List.mem_append_right _ h) hglκ.symm
          · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
        · rw [hr'] at hw
          cases hw
      · intro e he
        rcases hmk with ⟨v, hv', _⟩ | ⟨rr, hr'⟩
        · rw [hv'] at he; cases he
        · rw [hr'] at he; cases he
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_succ_of_lt (hk e hm)
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · exact ⟨fun t _ => congrFun hW'.1.symm t, fun g _ => congrFun hW'.2.symm g⟩
  · intro R O' hR hA
    have hans := hR _ _ _ _ hmem
    have hc := hcont R O' (passtV_append hR) hA
    rw [hans] at hc
    exact hwahl R O' _ _ hc

/-- **A push keeps the replay.** The head frame calls `g` with `args`; it
    becomes a suspended frame with the continuation `rc`, and the callee's
    frame becomes a fresh replayed head. The callee's `requires` holds at
    the machine's entry world (`pushV_req`), for the log. -/
theorem pushV_ok (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenV P passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (g : D.Fn) (args : Args D Γ Λ (D.params g))
    (hS : r.okV P (fussOrte P z.kopf.f) → args.orte ⊆ fussOrte P z.kopf.f ∧
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrte P z.kopf.f)
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okV P (fussOrte P z.kopf.f) → rc.okV P (fussOrte P z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) R σ (e : Logik D),
      R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        .logik e → semV O' passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) R σ,
      FortV passes ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semV O' passes R r σ ρ) R O'
        (R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ))) :
    FadenV P passes
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
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O' passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semV O' passes R r σ ρ) := by
    intro R O' hR hA
    have := heq R O' hR hA
    rw [hr] at this
    exact this
  obtain ⟨hargs, hctr⟩ := hS hok'
  have hgκ : GleichAuf (fussOrte P z.kopf.f) (σ.lese Λ args.orte) (W.lese Λ args.orte) :=
    hg.lese Λ Λ args.orte args.orte
  have hρk : evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ =
      evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ :=
    evalArgs_gleichAuf args (fun _ h => hargs h) hgκ ρ
  have hreqκ := pushV_req hO hK hreq hf hv hfa hra r heq' g (σ.lese Λ args.orte)
    (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
    (fun O' R e h => hlogik O' R σ e h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ args.orte)
      (W.lese Λ args.orte) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ args.orte, hreq0, funkV_nil, vertraegeOkV_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpf P g⟩, fun R O' _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ args.orte, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA
  have hw := hweiter O' R σ
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA) hw

/-- **A push through a read set `os` and a parameter function `rhoF`** --
    the shape of an indirect call, whose callee `g` the pointer read at the
    key names (the sequential side only needs it at worlds agreeing with the
    machine world on the footprint, `hlogik`, `hweiter`). -/
theorem pushV_gen (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true)
    {z : RufFadenG D} {W : World D} (hF : FadenV P passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (os : List (D.Tab ⊕ D.Glob)) (g : D.Fn) (rhoF : World D → Env D (D.params g))
    (hS : r.okV P (fussOrte P z.kopf.f) →
      (P.requires g).orte ++ (P.ensures g).orte ⊆ fussOrte P z.kopf.f)
    (hrho : r.okV P (fussOrte P z.kopf.f) → ∀ σ : World D,
      GleichAuf (fussOrte P z.kopf.f) σ W → rhoF (σ.lese Λ os) = rhoF (W.lese Λ os))
    {lc : Bool} {Γc : Ctx} {Λc : List (Res D)} (ρc : Env D Γc)
    (rc : GRest D (vertragVon D z.kopf.f) lc Γc Λc)
    (hrc : r.okV P (fussOrte P z.kopf.f) → rc.okV P (fussOrte P z.kopf.f))
    (hlogik : ∀ (O' : Orakel D) R σ (e : Logik D), GleichAuf (fussOrte P z.kopf.f) σ W →
      R g (σ.lese Λ os) (rhoF (σ.lese Λ os)) = .logik e → semV O' passes R r σ ρ = .logik e)
    (hweiter : ∀ (O' : Orakel D) R σ, GleichAuf (fussOrte P z.kopf.f) σ W →
      FortV passes ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ g
        (semV O' passes R r σ ρ) R O' (R g (σ.lese Λ os) (rhoF (σ.lese Λ os)))) :
    FadenV P passes
      ⟨⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩ :: z.stapel,
        ⟨g, rhoF (W.lese Λ os), W.lese Λ os,
          ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhoF (W.lese Λ os),
            .ende (P.rumpf g)⟩⟩,
        (W.lese Λ os).spur,
        RufEreignisF.eintritt g (rhoF (W.lese Λ os)) (W.lese Λ os) :: z.log⟩
      (W.lese Λ os) ∧
    ReqAmEintritt P g (W.lese Λ os) (rhoF (W.lese Λ os)) := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok, heq⟩, hSt⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok; exact hok
  have heq' : ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D),
      PasstV R H → PasstA O' HA →
      (zErg (execEnd (V := vertragVon D z.kopf.f) O' passes R (P.rumpf z.kopf.f) z.kopf.s0
        z.kopf.rho)).folgt (semV O' passes R r σ ρ) := by
    intro R O' hR hA
    have := heq R O' hR hA
    rw [hr] at this
    exact this
  have hctr := hS hok'
  have hgκ : GleichAuf (fussOrte P z.kopf.f) (σ.lese Λ os) (W.lese Λ os) := hg.lese Λ Λ os os
  have hρk : rhoF (σ.lese Λ os) = rhoF (W.lese Λ os) := hrho hok' σ hg
  have hreqκ := pushV_req hO hK hreq hf hv hfa hra r heq' g (σ.lese Λ os) (rhoF (σ.lese Λ os))
    (fun O' R e h => hlogik O' R σ e hg h)
  rw [hρk] at hreqκ
  have hctrκ : GleichAuf ((P.requires g).orte ++ (P.ensures g).orte) (σ.lese Λ os)
      (W.lese Λ os) := GleichAuf.mono (fun _ h => hctr h) hgκ
  have hreq0 := req_transfer hreqκ
    (GleichAuf.mono (fun _ h => List.mem_append_left _ h) hctrκ)
  refine ⟨⟨⟨[], [], W.lese Λ os, hreq0, funkV_nil, vertraegeOkV_nil P, kurzV_nil _,
    funkA_nil, rahmenA_nil, kurzA_nil _,
    GleichAuf.refl _ _, ⟨hFrag g, fuss_rumpf P g⟩, fun R O' _ _ => ZErg.folgt_refl _⟩,
    ⟨H, HA, σ.lese Λ os, hreq, hf, hv, kurzV_mono hk (lese_laenge _ _ _), hfa, hra,
      kurzA_mono hka (lese_laenge _ _ _), hrc hok', hreqκ, hctrκ, ?_⟩, hSt⟩, hreq0⟩
  intro R O' hR hA
  have hw := hweiter O' R σ hg
  rw [hρk] at hw
  exact fortV_mono (F := ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨lc, Γc, Λc, ρc, rc⟩⟩)
    (heq' R O' hR hA) hw

end Schritte

/-! ## 5. Leaves and axiom calls -/

/-- A statement is an axiom call. -/
def Stmt.istAxiom {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .axiomCall .. => true
  | _ => false

/-- A leaf other than an axiom call consults neither the oracle nor the
    call handler. -/
theorem blatt_orakel (O O' : Orakel D) (passes : Nat)
    (R R' : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R s σ ρ = execStmt O' passes R' s σ ρ := by
  cases s <;> first | rfl | (simp [Stmt.istBlatt] at hb; done) |
    (simp [Stmt.istAxiom] at ha; done)

/-- **Leaf locality, for any oracle and handler.** A leaf other than an
    axiom call, run at a world agreeing with the machine world on a
    footprint covering its carriers, ends where the machine's run ends (in
    environment, and in memory on the footprint), for every oracle and
    handler; its trace only grows. -/
theorem blatt_lokalV (P : Programm D) (O : Orakel D) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAxiom = false) {S : List (D.Tab ⊕ D.Glob)} (hS : stmtOrteP P s ⊆ S)
    {σ W : World D} (hg : GleichAuf S σ W) {ρ : Env D Γ} {W' : World D} {ρ' : Env D Γ}
    (h : execStmt O passes keinRuf s W ρ = .ok W' ρ') :
    ∃ σ', (∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
        execStmt O' passes R s σ ρ = .ok σ' ρ') ∧ GleichAuf S σ' W' ∧
      σ.spur.length ≤ σ'.spur.length := by
  have hk : s.kOk = true := by
    cases s <;> first | rfl | (simp [Stmt.istBlatt] at hb; done) |
      (simp [Stmt.istAxiom] at ha; done) | (simp [execStmt] at h; done)
  obtain ⟨σ', h1, h2, h3⟩ := blatt_lokal P O passes s hk hb (fun o ho => hS ho) hg h
  exact ⟨σ', fun O' R => by rw [blatt_orakel O' O passes R keinRuf hb ha]; exact h1, h2, h3⟩

/-- What an `ok` run of an axiom call statement is. -/
theorem axiomCall_ok_inv {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (ρ' : Env D Γ)
    (hst : execStmt O passes R (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ =
      .ok σ' ρ') :
    σ' = (O.wirkt a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).1 ∧ ρ' = ρ ∧
    ∃ u : ErgVal D (D.aerg a), einpassenErg (D.aerg a) (O.wirkt a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)).2 = some u := by
  simp only [execStmt, axiomAntwort] at hst
  split at hst
  · rename_i σx u hx
    cases hst
    simp only [Prod.mk.injEq] at hx
    exact ⟨hx.1.symm, rfl, u, hx.2⟩
  · cases hst

/-! ## 6. The steps of the replay that record an answer or pop -/

section Schritte2

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **An axiom step keeps the replay.** The answer of the machine's oracle
    (`xm`, in the axiom's frame around the machine's call world) is recorded
    at the sequential key, with the answer world `axWelt`: the declared
    carriers from the machine, the rest from the key world, a fresh trace
    position. -/
theorem fadenV_ax (e0 : Ereignis D) {z : RufFadenG D} {W : World D} (hF : FadenV P passes z W)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    {l' : Bool} {Γ' : Ctx} {Λ' : List (Res D)} (ρ' : Env D Γ')
    (r' : GRest D (vertragVon D z.kopf.f) l' Γ' Λ') (spur' : List (Ereignis D))
    (a : D.Ax) (args : Args D Γ Λ (D.aparams a))
    (hok : r.okV P (fussOrte P z.kopf.f) → r'.okV P (fussOrte P z.kopf.f))
    (xm : World D × Int) (hxm : Rahmen (D.aschreibt a) (D.agschreibt a) (W.lese Λ args.orte) xm.1)
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D),
      O'.wirkt a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) =
        (axWelt e0 a (σ.lese Λ args.orte) xm.1, xm.2) →
      (semV O' passes R r σ ρ).folgt
        (semV O' passes R r' (axWelt e0 a (σ.lese Λ args.orte) xm.1) ρ')) :
    FadenV P passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l', Γ', Λ', ρ', r'⟩⟩, spur', z.log⟩
      (xm.1.speicher.welt spur') := by
  obtain ⟨⟨H, HA, σ, hreq, hf, hv, hk, hfa, hra, hka, hg, hok0, heq⟩, hS⟩ := hF
  have hok' : r.okV P (fussOrte P z.kopf.f) := by rw [hr] at hok0; exact hok0
  have hlen : σ.spur.length ≤ (σ.lese Λ args.orte).spur.length := lese_laenge _ _ _
  refine ⟨⟨H, HA ++ [⟨a, σ.lese Λ args.orte,
      evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ,
      (axWelt e0 a (σ.lese Λ args.orte) xm.1, xm.2)⟩],
    axWelt e0 a (σ.lese Λ args.orte) xm.1, hreq, hf, hv,
    kurzV_mono hk (Nat.le_trans hlen (Nat.le_succ _)), funkA_append hfa hka _ hlen, ?_, ?_, ?_,
    hok hok', ?_⟩, hS⟩
  · intro a' σk ρk x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hra a' σk ρk x hm
    · rw [List.mem_singleton] at hm
      cases hm
      exact axWelt_rahmen e0 a _ _
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hka e hm) (Nat.le_trans hlen (Nat.le_succ _))
    · rw [List.mem_singleton] at hm
      subst hm
      exact Nat.lt_succ_self _
  · have h1 := axWelt_gleichAuf e0 a (hg.lese Λ Λ args.orte args.orte) hxm
    exact ⟨fun t ht => h1.1 t ht, fun g hg' => h1.2 g hg'⟩
  · intro R O' hR hA
    have h1 := heq R O' hR (passtA_append hA)
    rw [hr] at h1
    exact ZErg.folgt_trans h1 (hsem O' R σ (hA _ _ _ _ (List.mem_append_right _ List.mem_cons_self)))

/-- **A leaf step keeps the replay**: a non-axiom leaf by leaf locality, an
    axiom call by recording its answer (`fadenV_ax`). -/
theorem fadenV_blatt (e0 : Ereignis D) (hO : GutO O) {z : RufFadenG D} {W : World D}
    (hF : FadenV P passes z W) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D z.kopf.f) l Γ Λ} (hr : z.kopf.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (s : Stmt D (vertragVon D z.kopf.f) l Γ Λ Λ') (K : GRest D (vertragVon D z.kopf.f) l Γ Λ')
    (hsem : ∀ (O' : Orakel D) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
      (σ : World D), semV O' passes R r σ ρ = weiterZ O' passes R K (execStmt O' passes R s σ ρ))
    (hok : r.okV P (fussOrte P z.kopf.f) →
      stmtOrteP P s ⊆ fussOrte P z.kopf.f ∧ K.okV P (fussOrte P z.kopf.f))
    (hleaf : s.istBlatt = true) (σ' : World D) (ρ' : Env D Γ)
    (hstep : execStmt O passes keinRuf s W ρ = .ok σ' ρ') :
    FadenV P passes
      ⟨z.stapel, ⟨z.kopf.f, z.kopf.rho, z.kopf.s0, ⟨l, Γ, Λ', ρ', K⟩⟩, σ'.spur, z.log⟩
      (σ'.speicher.welt σ'.spur) := by
  cases hax : s.istAxiom with
  | false =>
      refine fadenV_lokal hF hr ρ' K σ'.spur (fun σ hg hok' => ?_)
      obtain ⟨hs, hK⟩ := hok hok'
      obtain ⟨σs, hes, hgs, hls⟩ := blatt_lokalV P O passes s hleaf hax hs hg hstep
      refine ⟨σs, hls, ⟨fun t ht => hgs.1 t ht, fun g hg' => hgs.2 g hg'⟩, hK, fun R O' => ?_⟩
      rw [hsem, hes]
      exact ZErg.folgt_refl _
  | true =>
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          obtain ⟨e1, e2, u, hu⟩ := axiomCall_ok_inv O passes keinRuf a args h hw hg hd hgd W ρ σ' ρ'
            hstep
          subst e2
          have hfr := (hO a (W.lese Λ args.orte)
            (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).1
          rw [← e1] at hfr
          refine fadenV_ax e0 hF hr ρ' K σ'.spur a args (fun h' => (hok h').2)
            (σ', (O.wirkt a (W.lese Λ args.orte)
              (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ')).2) hfr ?_
          intro O' R σ hw
          rw [hsem]
          apply ZErg.folgt_of_eq
          simp only [execStmt, axiomAntwort, hw]
          simp only [hu]
          rfl
      | _ => simp [Stmt.istAxiom] at hax

end Schritte2

/-! ## CUTS:

  What is proved: the user obligation `KoerperGutV` (the body triple for
  every oracle respecting the declared axiom frames, `RahmenO`); the
  records of call answers with reason answers (`EintragV`, `rufAusV` is a
  contract-respecting handler that never blames a caller) and of axiom
  answers (`AxEintrag`, `orakelAus` respects every declared frame under
  `GutO`); the recorded axiom answer world `axWelt` (inside the frame
  around the key, agreeing with the machine's answer on the footprint);
  the replay invariants `KopfV`/`WarteV`/`FortV`/`FadenV` and the steps
  that keep them: head-local (`fadenV_lokal`), memory outside the footprint
  (`fadenV_speicher`), return (`popV_ens`), call (`pushV_req`,
  `pushV_ok`), resume after a normal or reason answer (`popV_kopf`),
  axiom answer (`fadenV_ax`), leaf (`fadenV_blatt`).

  What is NOT here: the rule-by-rule step and the theorem
  (`ZielOrtVoll.lean`). The oracle's register and visibility answers
  (`regLies`, `sichtbar`) are not recorded: the fragment excludes the forms
  that consult them (see the CUTS of `ZielOrtVoll.lean` for why).
-/

#print axioms Gabbro.Grammatik.popV_kopf
#print axioms Gabbro.Grammatik.pushV_ok
#print axioms Gabbro.Grammatik.fadenV_blatt

end Gabbro.Grammatik
