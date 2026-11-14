module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollSem
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis

@[expose] public section



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
  ∀ e ∈ H, e.2.1.rang < N

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
    (e : EintragV D) (he : N ≤ e.2.1.rang) : FunkV (H ++ [e]) := by
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

/-- **The records are functional up to read events.** The replay oracle answers the world WITHOUT
    its read events (`Orakel`), so two records whose keys differ only by reads would have to get one
    answer: no two keys of one axiom and one argument list have one erasure unless they are one
    record (`funkA_append` keeps them apart by the rank, `KurzA`). Every recorded answer world puts
    its events on top of its key's trace (an answer of the outside never unwrites the past). -/
def FunkA (HA : List (AxEintrag D)) : Prop :=
  (∀ (a : D.Ax) (σ σ' : World D) (ρ : Env D (D.aparams a)) (x x' : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → (⟨a, σ', ρ, x'⟩ : AxEintrag D) ∈ HA →
      σ.ohneLese = σ'.ohneLese → σ = σ' ∧ x = x') ∧
  ∀ e ∈ HA, ∃ neu : List (Ereignis D), e.2.2.2.1.spur = neu ++ e.2.1.spur

/-- Every key's rank (its trace without reads) is below `N`. -/
def KurzA (N : Nat) (HA : List (AxEintrag D)) : Prop :=
  ∀ e ∈ HA, e.2.1.rang < N

/-- Every recorded answer world lies in the axiom's declared frame around
    its key world. -/
def RahmenA (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → Rahmen (D.aschreibt a) (D.agschreibt a) σ x.1

def PasstA (O' : Orakel D) (HA : List (AxEintrag D)) : Prop :=
  ∀ (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) (x : World D × Int),
    (⟨a, σ, ρ, x⟩ : AxEintrag D) ∈ HA → O'.wirkt a σ ρ = x

/-- The sequential oracle reads the machine's loaded image (`Orakel.zeiger`): a recorded raw
    answer of `fnptr` type decodes to the same function in the replay (G1 repair). -/
def ZeigerGleich (O O' : Orakel D) : Prop := O'.zeiger = O.zeiger

/-- A recorded answer as the outside gives it: the answer world's memory, and as its trace the
    events on top of the key's trace. -/
def antwortAus (κ w : World D) : World D :=
  ⟨w.slots, w.globs, w.spur.take (w.spur.length - κ.spur.length)⟩

/-- The recorded answer lands on its key as recorded. -/
theorem antwortAus_auf {κ w : World D} {neu : List (Ereignis D)} (h : w.spur = neu ++ κ.spur) :
    (antwortAus κ w).auf κ = w := by
  obtain ⟨s, g, sp⟩ := w
  change sp = neu ++ κ.spur at h
  subst h
  show (⟨s, g, (neu ++ κ.spur).take ((neu ++ κ.spur).length - κ.spur.length) ++ κ.spur⟩ : World D) =
    ⟨s, g, neu ++ κ.spur⟩
  rw [List.length_append, Nat.add_sub_cancel, List.take_left' rfl]

/-- The question the replay oracle looks up: a record of `a` with the arguments `ρ` whose key has the
    erasure `ε`. -/
def AxFrage (HA : List (AxEintrag D)) (a : D.Ax) (ε : World D) (ρ : Env D (D.aparams a)) : Prop :=
  ∃ κx : World D × (World D × Int), (⟨a, κx.1, ρ, κx.2⟩ : AxEintrag D) ∈ HA ∧ κx.1.ohneLese = ε

/-- **The oracle of a record**: asked (without reads) at the erasure of a recorded key, the recorded
    answer; the machine's oracle everywhere else. -/
noncomputable def orakelAus (O : Orakel D) (HA : List (AxEintrag D)) : Orakel D where
  wirktL := fun a ε ρ =>
    haveI := Classical.propDecidable (AxFrage HA a ε ρ)
    if h : AxFrage HA a ε ρ then
      (antwortAus (Classical.choose h).1 (Classical.choose h).2.1, (Classical.choose h).2.2)
    else O.wirktL a ε ρ
  regLiesL := O.regLiesL
  regSchreib := O.regSchreib
  sichtbarL := O.sichtbarL
  zeiger := O.zeiger

/-- At a world whose erasure is a recorded key's: the chosen record. -/
theorem orakelAus_wirkt_frage (O : Orakel D) (HA : List (AxEintrag D)) {a : D.Ax} {σ : World D}
    {ρ : Env D (D.aparams a)} (h : AxFrage HA a σ.ohneLese ρ) :
    (orakelAus O HA).wirkt a σ ρ =
      ((antwortAus (Classical.choose h).1 (Classical.choose h).2.1).auf σ, (Classical.choose h).2.2) := by
  simp only [Orakel.wirkt, orakelAus, dif_pos h]

/-- Elsewhere: the machine's oracle. -/
theorem orakelAus_wirkt_sonst (O : Orakel D) (HA : List (AxEintrag D)) {a : D.Ax} {σ : World D}
    {ρ : Env D (D.aparams a)} (h : ¬ AxFrage HA a σ.ohneLese ρ) :
    (orakelAus O HA).wirkt a σ ρ = O.wirkt a σ ρ := by
  simp only [Orakel.wirkt, orakelAus, dif_neg h]

/-- **The chosen record answers in the memory of the recorded answer**, at every world with its
    key's erasure; the answer is the recorded one. -/
theorem orakelAus_frage_speicher (O : Orakel D) (HA : List (AxEintrag D)) {a : D.Ax} {σ : World D}
    {ρ : Env D (D.aparams a)} (h : AxFrage HA a σ.ohneLese ρ) :
    ((orakelAus O HA).wirkt a σ ρ).1.slots = (Classical.choose h).2.1.slots ∧
      ((orakelAus O HA).wirkt a σ ρ).1.globs = (Classical.choose h).2.1.globs ∧
      ((orakelAus O HA).wirkt a σ ρ).2 = (Classical.choose h).2.2 := by
  rw [orakelAus_wirkt_frage O HA h]
  exact ⟨rfl, rfl, rfl⟩

theorem orakelAus_passt (O : Orakel D) {HA : List (AxEintrag D)} (hf : FunkA HA) :
    PasstA (orakelAus O HA) HA := by
  intro a σ ρ x hmem
  have hex : AxFrage HA a σ.ohneLese ρ := ⟨(σ, x), hmem, rfl⟩
  obtain ⟨hcm, hce⟩ := Classical.choose_spec hex
  obtain ⟨hκ, hx⟩ := hf.1 a _ σ ρ _ x hcm hmem hce
  obtain ⟨neu, hneu⟩ := hf.2 _ hmem
  have hneu' : x.1.spur = neu ++ σ.spur := hneu
  rw [orakelAus_wirkt_frage O HA hex, hκ, hx]
  exact Prod.ext (antwortAus_auf hneu') rfl

theorem orakelAus_rahmen {O : Orakel D} (hO : GutO O) {HA : List (AxEintrag D)}
    (hr : RahmenA HA) : RahmenO (orakelAus O HA) := by
  intro a σ ρ
  by_cases h : AxFrage HA a σ.ohneLese ρ
  · obtain ⟨hcm, hce⟩ := Classical.choose_spec h
    obtain ⟨hs, hg, _⟩ := orakelAus_frage_speicher O HA h
    have hR := hr a _ ρ _ hcm
    have hs0 : (Classical.choose h).1.slots = σ.slots := World.slots_of_ohneLese hce
    have hg0 : (Classical.choose h).1.globs = σ.globs := World.globs_of_ohneLese hce
    refine ⟨fun t ht k f => ?_, fun g' hg' => ?_⟩
    · rw [hs, ← hs0]
      exact hR.1 t ht k f
    · rw [hg, ← hg0]
      exact hR.2 g' hg'
  · rw [orakelAus_wirkt_sonst O HA h]
    exact (hO a σ ρ).1

theorem passtA_append {O' : Orakel D} {HA : List (AxEintrag D)} {e : AxEintrag D}
    (h : PasstA O' (HA ++ [e])) : PasstA O' HA :=
  fun a σ ρ x hmem => h a σ ρ x (List.mem_append_left _ hmem)

theorem funkA_nil : FunkA ([] : List (AxEintrag D)) :=
  ⟨fun _ _ _ _ _ _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem rahmenA_nil : RahmenA ([] : List (AxEintrag D)) := fun _ _ _ _ h => absurd h List.not_mem_nil

theorem kurzA_nil (N : Nat) : KurzA N ([] : List (AxEintrag D)) :=
  fun _ h => absurd h List.not_mem_nil

theorem kurzA_mono {N N' : Nat} {HA : List (AxEintrag D)} (h : KurzA N HA) (hN : N ≤ N') :
    KurzA N' HA :=
  fun e he => Nat.lt_of_lt_of_le (h e he) hN

/-- **A fresh record keeps the records functional**: its key's rank is at least `N`, above every
    earlier key's, so no earlier key has its erasure; its answer world puts its events on top of
    its key's trace. -/
theorem funkA_append {HA : List (AxEintrag D)} (hf : FunkA HA) {N : Nat} (hk : KurzA N HA)
    (e : AxEintrag D) (he : N ≤ e.2.1.rang) (hs : ∃ neu : List (Ereignis D), e.2.2.2.1.spur = neu ++ e.2.1.spur) :
    FunkA (HA ++ [e]) := by
  refine ⟨fun a σ σ' ρ x x' h1 h2 hε => ?_, fun e' he' => ?_⟩
  · rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
    · exact hf.1 a σ σ' ρ x x' h1 h2 hε
    · have h3 : σ.rang < N := hk _ h1
      rw [List.mem_singleton] at h2
      subst h2
      have hr : σ.rang = σ'.rang := World.rang_eq hε
      have h4 : N ≤ σ'.rang := he
      omega
    · have h3 : σ'.rang < N := hk _ h2
      rw [List.mem_singleton] at h1
      subst h1
      have hr : σ.rang = σ'.rang := World.rang_eq hε
      have h4 : N ≤ σ.rang := he
      omega
    · rw [List.mem_singleton] at h1 h2
      rw [← h1] at h2
      have e2 := eq_of_heq (Sigma.mk.inj h2).2
      simp only [Prod.mk.injEq] at e2
      exact ⟨e2.1.symm, e2.2.2.symm⟩
  · rcases List.mem_append.mp he' with he' | he'
    · exact hf.2 e' he'
    · rw [List.mem_singleton] at he'
      subst he'
      exact hs

/-- The recorded answer world of an axiom call: the axiom's declared
    carriers from the machine's answer world `σ₂`, every other carrier from
    the sequential key world `κ`, one fresh trace event past `κ` (not a read: the rank grows). -/
def axWelt (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) : World D :=
  ⟨fun t => if D.aschreibt a t = true then σ₂.slots t else κ.slots t,
   fun g => if D.agschreibt a g = true then σ₂.globs g else κ.globs g, nichtLese e0 :: κ.spur⟩

/-- The recorded answer world is one rank past its key. -/
theorem axWelt_rang (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) : (axWelt e0 a κ σ₂).rang = κ.rang + 1 :=
  rang_nichtLese_cons e0 κ.spur

theorem axWelt_rang_lt (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) : κ.rang < (axWelt e0 a κ σ₂).rang := by
  rw [axWelt_rang]
  exact Nat.lt_succ_self _

theorem axWelt_rang_le (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) : κ.rang ≤ (axWelt e0 a κ σ₂).rang :=
  Nat.le_of_lt (axWelt_rang_lt e0 a κ σ₂)

/-- The recorded answer world puts its event on top of its key's trace. -/
theorem axWelt_spur (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) :
    ∃ neu : List (Ereignis D), (axWelt e0 a κ σ₂).spur = neu ++ κ.spur :=
  ⟨[nichtLese e0], rfl⟩

theorem axWelt_rahmen (e0 : Ereignis D) (a : D.Ax) (κ σ₂ : World D) :
    Rahmen (D.aschreibt a) (D.agschreibt a) κ (axWelt e0 a κ σ₂) := by
  refine ⟨fun t ht k f => ?_, fun g hg => ?_⟩
  · show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) k f = κ.slots t k f
    rw [if_neg (by simp only [ht, Bool.false_eq_true, not_false_eq_true])]
  · show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = κ.globs g
    rw [if_neg (by simp only [hg, Bool.false_eq_true, not_false_eq_true])]

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

end Gabbro.Grammatik
