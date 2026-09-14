/-
  File:      Grammatik/Nichtinterferenz/Fluss.lean
  Subject:   THE DECIDABLE FLOW CONDITION `flussB` AND NONINTERFERENCE FROM IT
             (`abwicklung_aus_fluss`, `nichtinterferenz`,
             `nichtinterferenz_planer`, `nichtinterferenz_zeitplan`).

  The labels of a program (`FlussEtiketten`): a domain per carrier, a domain
  per axiom (foreign body, device driver), and the domain of every ENTRY
  ROOT (`wurzel f = some d`: `f` may start a thread of domain `d`).

  `flussB` checks, for every labelled root `r` of domain `d` and every
  function `g` its call graph reaches (`reachB`, closure checked by
  `abgB`):
    * READS: every carrier `g`'s body reads -- every expression's `orte`,
      the device carriers of its register reads, the awaited/exchanged
      globals -- has a label that may flow to `d` (`nE` at
      `zuDom lab d`); every axiom it calls has a label that may flow to `d`;
    * WRITES: every carrier `g`'s signature may write (`TraegerSchreibt`,
      the frame the machine enforces, axioms included) has a label `d` may
      flow to ("no write down").

  EXPLICIT AND IMPLICIT FLOWS. A write of an `A`-derived value into a
  `B`-observable carrier (explicit), and a write into a `B`-observable
  carrier under a branch or loop whose condition reads `A` data (implicit),
  both need ONE thread that reads `A` and writes a `B`-observable carrier:
  its domain `d` must admit `A → d` (read) and `d → B` (write), hence
  `A → B` by transitivity. `flussB` refuses both, at thread granularity:
  it is the footprint form of the statement-level rule (every write, its
  expression reads and its enclosing conditions, `dokumente/NICHTINTERFERENZ.md`).
  What the thread-granular form does NOT admit, and the statement-level
  form would: one thread that handles both domains (a dispatcher reading
  `A` and writing `B` on paths that never mix them). That refinement needs
  a program-counter label per thread and is outside this proof.
-/
import Grammatik.Nichtinterferenz.Invariante

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The flow labels of a program**: carriers, axioms, entry roots. -/
structure FlussEtiketten (D : Deklaration) (Dom : Type) where
  lab : D.Tab ⊕ D.Glob → Dom
  labAx : D.Ax → Dom
  wurzel : D.Fn → Option Dom

section Fluss

variable {Dom : Type} (π : Politik Dom)

/-- The carriers whose label may flow to `d`. -/
def zuDom (lab : D.Tab ⊕ D.Glob → Dom) (d : Dom) : D.Tab ⊕ D.Glob → Bool :=
  fun c => π.darf (lab c) d

/-- The axioms whose label may flow to `d`. -/
def axZuDom (labAx : D.Ax → Dom) (d : Dom) : D.Ax → Bool := fun a => π.darf (labAx a) d

variable [DecidableEq D.Fn]

/-- The flow check for one root `r` of domain `d`. -/
def wurzelB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (L : FlussEtiketten D Dom) (r : D.Fn) (d : Dom) : Bool :=
  abgB P fs (reachB P fs r) &&
  fs.all fun g => !(reachB P fs r g) ||
    (nE (zuDom π L.lab d) (axZuDom π L.labAx d) (P.rumpf g) &&
      cs.all fun c => !(TraegerSchreibt g c) || π.darf d (L.lab c))

/-- **The flow condition `flussB`**, decided over the member lists of the
    functions `fs` and the carriers `cs`. -/
def flussB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob))
    (L : FlussEtiketten D Dom) : Bool :=
  fs.all fun r => match L.wurzel r with
    | none => true
    | some d => wurzelB π P fs cs L r d

/-- What `wurzelB` decides. -/
theorem wurzelB_ok {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hvollC : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {L : FlussEtiketten D Dom} {r : D.Fn} {d : Dom} (h : wurzelB π P fs cs L r d = true) :
    AbgK P fs (reachB P fs r) ∧
      ∀ g, reachB P fs r g = true →
        nE (zuDom π L.lab d) (axZuDom π L.labAx d) (P.rumpf g) = true ∧
        ∀ c, TraegerSchreibt g c = true → π.darf d (L.lab c) = true := by
  simp only [wurzelB, Bool.and_eq_true] at h
  refine ⟨abgB_ok hvoll h.1, fun g hg => ?_⟩
  have h1 := (List.all_eq_true.mp h.2) g (hvoll g)
  simp only [hg, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h1
  refine ⟨h1.1, fun c hc => ?_⟩
  have h2 := (List.all_eq_true.mp h1.2) c (hvollC c)
  simp only [hc, Bool.not_true, Bool.false_or] at h2
  exact h2

/-- What `flussB` decides, per thread: the thread's root is labelled `fdom t`. -/
theorem flussB_faden {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hvollC : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    {L : FlussEtiketten D Dom} (h : flussB π P fs cs L = true) {r : D.Fn} {d : Dom}
    (hr : L.wurzel r = some d) :
    AbgK P fs (reachB P fs r) ∧
      ∀ g, reachB P fs r g = true →
        nE (zuDom π L.lab d) (axZuDom π L.labAx d) (P.rumpf g) = true ∧
        ∀ c, TraegerSchreibt g c = true → π.darf d (L.lab c) = true := by
  have h1 := (List.all_eq_true.mp h) r (hvoll r)
  rw [hr] at h1
  exact wurzelB_ok π hvoll hvollC h1

end Fluss

section Satz

variable {Dom : Type} (π : Politik Dom) [DecidableEq D.Fn]
  (P : Programm D) (O : Orakel D) (passes : Nat)
  (init : Faden → Σ f : D.Fn, Env D (D.params f)) {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)}
  (L : FlussEtiketten D Dom) (fdom : Faden → Dom)

/-- The labels the metatheorem reads: carriers from the program labels,
    threads from their roots. -/
def etiketten : Etiketten D Dom := ⟨L.lab, fdom⟩

/-- **The unwinding conditions from the flow condition
    (`abwicklung_aus_fluss`).** `flussB` holds; every thread starts in a
    root labelled with its domain; the oracle keeps every axiom inside its
    frame (`GutO`), registers are local (`RegLokal`), and the hardware
    answers the axioms that may flow to `B` from `B`-visible data only
    (`OrakelTreu`). Then local respect and step consistency hold for
    observer `B` on every machine reachable from any start. -/
theorem abwicklung_aus_fluss (hvoll : ∀ g : D.Fn, g ∈ fs) (hvollC : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hfl : flussB π P fs cs L = true) (hW : ∀ t, L.wurzel (init t).1 = some (fdom t))
    (B : Dom) (hO : GutO O) (hRL : RegLokal O)
    (hOT : OrakelTreu (zuDom π L.lab B) (axZuDom π L.labAx B) O) :
    AbwicklungG π (etiketten L fdom) B P O passes init := by
  have hF := fun t => flussB_faden π hvoll hvollC hfl (hW t)
  let K : Faden → D.Fn → Bool := fun t => reachB P fs (init t).1
  have hAbg : ∀ t, AbgK P fs (K t) := fun t => (hF t).1
  have hWu : ∀ t, K t (init t).1 = true := fun t => reachB_wurzel P fs _
  have hInv : ∀ {sp : Speicher D} {M : RufMaschineG D},
      RufErreichbarG P O passes (RufStartG P sp init) M →
      ∀ t, MerkInvG (fun f => K t f = true) (fun _ => rufM fs (K t)) (M.faeden t) :=
    fun hr => merkInvG_erreichbar (O := O) (pa := passes) _ init
      (fun t f => K t f = true) (fun t _ => rufM fs (K t))
      (fun t => merkAbg_rufM hvoll (hAbg t)) hWu hr
  have hKnr : ∀ {sp : Speicher D} {M : RufMaschineG D},
      RufErreichbarG P O passes (RufStartG P sp init) M →
      ∀ t, KNR (zuDom π L.lab (fdom t)) (axZuDom π L.labAx (fdom t)) (M.faeden t).kern :=
    fun hr => knr_erreichbar P O passes _ init hvoll K hAbg hWu
      (fun t => zuDom π L.lab (fdom t)) (fun t => axZuDom π L.labAx (fdom t))
      (fun t g hg => ((hF t).2 g hg).1) hr
  refine ⟨fun M M' f hM hvis hs => ?_, fun M N M' N' f hM hN hvis hMN hs₁ hs₂ => ?_⟩
  · -- local respect
    obtain ⟨sp, hr⟩ := hM
    refine ⟨fun c hc => ?_, fun t ht => ?_⟩
    · have hkopf := ((hInv hr f) _ List.mem_cons_self).1
      have hw : TraegerSchreibt (M.faeden f).kopf.f c = false := by
        cases hwc : TraegerSchreibt (M.faeden f).kopf.f c with
        | false => rfl
        | true =>
            exfalso
            have h1 := ((hF f).2 _ hkopf).2 c hwc
            have h2 : π.darf (fdom f) B = true := π.trans _ _ _ h1 hc
            have h3 : sichtbarF π (etiketten L fdom) B f = false := hvis
            simp only [sichtbarF, etiketten] at h3
            rw [h2] at h3
            exact Bool.false_ne_true h3.symm
      have := schritt_traeger hO hs c (Or.inr hw)
      cases c with
      | inl t => exact this.symm
      | inr g => exact this.symm
    · have htf : t ≠ f := by
        rintro rfl
        rw [ht] at hvis
        exact Bool.false_ne_true hvis.symm
      rw [rufSchrittG_fremd hs t htf]
  · -- step consistency
    obtain ⟨sp₁, hr₁⟩ := hM
    have e₁ := schrittK_von P O passes hs₁
    have e₂ := schrittK_von P O passes hs₂
    rw [hMN.2 f hvis] at e₁
    have hvis' : π.darf (fdom f) B = true := hvis
    have hk := hKnr hr₁ f
    rw [hMN.2 f hvis] at hk
    have hrel := schrittK_rel (S := zuDom π L.lab (fdom f)) (T := zuDom π L.lab B)
      (Ax := axZuDom π L.labAx (fdom f)) (AxT := axZuDom π L.labAx B)
      (fun c hc => π.trans _ _ _ hc hvis') (fun a ha => π.trans _ _ _ ha hvis')
      P O passes hOT hRL (N.faeden f).kern (hk _ List.mem_cons_self) hMN.1
    obtain ⟨hk', hsp'⟩ := hrel _ _ e₁ e₂
    refine ⟨hsp', fun t ht => ?_⟩
    by_cases htf : t = f
    · subst htf
      exact hk'
    · rw [rufSchrittG_fremd hs₁ t htf, rufSchrittG_fremd hs₂ t htf]
      exact hMN.2 t ht

/-- **NONINTERFERENCE (`nichtinterferenz`).** For a program that passes the
    flow condition, every observer domain `B`, two runs of machine G with
    the SAME schedule `fs'` from start memories that agree on every
    carrier whose label may flow to `B` (the same `B`-inputs) show `B` the
    same observation -- the `B`-visible memory and the state of every
    `B`-visible thread -- at every index. -/
theorem nichtinterferenz (hvoll : ∀ g : D.Fn, g ∈ fs) (hvollC : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hfl : flussB π P fs cs L = true) (hW : ∀ t, L.wurzel (init t).1 = some (fdom t))
    (B : Dom) (hO : GutO O) (hRL : RegLokal O)
    (hOT : OrakelTreu (zuDom π L.lab B) (axZuDom π L.labAx B) O)
    (sp₁ sp₂ : Speicher D) (hsp : SpeicherGleich (sichtbarC π (etiketten L fdom) B) sp₁ sp₂)
    (ms ns : Nat → RufMaschineG D) (fs' : Nat → Faden) (n : Nat)
    (hm : LaufG P O passes (RufStartG P sp₁ init) ms fs' n)
    (hn : LaufG P O passes (RufStartG P sp₂ init) ns fs' n) :
    ∀ k, k ≤ n → beob π (etiketten L fdom) B (ms k) = beob π (etiketten L fdom) B (ns k) :=
  ni_aus_abwicklung π (etiketten L fdom) B P O passes init
    (abwicklung_aus_fluss π P O passes init L fdom hvoll hvollC hfl hW B hO hRL hOT)
    sp₁ sp₂ hsp ms ns fs' n hm hn

/-- **NONINTERFERENCE WITH A SCHEDULER (`nichtinterferenz_planer`).** The
    schedule is produced by a scheduler `plan k M` whose choice depends only
    on what `B` observes. The two runs take the same thread at every step
    and show `B` the same observation. -/
theorem nichtinterferenz_planer (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hvollC : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hfl : flussB π P fs cs L = true) (hW : ∀ t, L.wurzel (init t).1 = some (fdom t))
    (B : Dom) (hO : GutO O) (hRL : RegLokal O)
    (hOT : OrakelTreu (zuDom π L.lab B) (axZuDom π L.labAx B) O)
    (plan : Nat → RufMaschineG D → Faden)
    (hplan : ∀ k M N, beob π (etiketten L fdom) B M = beob π (etiketten L fdom) B N →
      plan k M = plan k N)
    (sp₁ sp₂ : Speicher D) (hsp : SpeicherGleich (sichtbarC π (etiketten L fdom) B) sp₁ sp₂)
    (ms ns : Nat → RufMaschineG D) (n : Nat)
    (hm0 : ms 0 = RufStartG P sp₁ init) (hn0 : ns 0 = RufStartG P sp₂ init)
    (hm : ∀ k, k < n → RufSchrittG P O passes (ms k) (plan k (ms k)) (ms (k + 1)))
    (hn : ∀ k, k < n → RufSchrittG P O passes (ns k) (plan k (ns k)) (ns (k + 1))) :
    ∀ k, k ≤ n → beob π (etiketten L fdom) B (ms k) = beob π (etiketten L fdom) B (ns k) ∧
      (k < n → plan k (ms k) = plan k (ns k)) :=
  ni_planer π (etiketten L fdom) B P O passes init
    (abwicklung_aus_fluss π P O passes init L fdom hvoll hvollC hfl hW B hO hRL hOT)
    plan hplan sp₁ sp₂ hsp ms ns n hm0 hn0 hm hn

/-- **NONINTERFERENCE UNDER A FIXED TIMETABLE (`nichtinterferenz_zeitplan`)**
    -- the partition scheduler of seL4's information-flow configuration. -/
theorem nichtinterferenz_zeitplan (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hvollC : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs)
    (hfl : flussB π P fs cs L = true) (hW : ∀ t, L.wurzel (init t).1 = some (fdom t))
    (B : Dom) (hO : GutO O) (hRL : RegLokal O)
    (hOT : OrakelTreu (zuDom π L.lab B) (axZuDom π L.labAx B) O) (tafel : Nat → Faden)
    (sp₁ sp₂ : Speicher D) (hsp : SpeicherGleich (sichtbarC π (etiketten L fdom) B) sp₁ sp₂)
    (ms ns : Nat → RufMaschineG D) (n : Nat)
    (hm : LaufG P O passes (RufStartG P sp₁ init) ms tafel n)
    (hn : LaufG P O passes (RufStartG P sp₂ init) ns tafel n) :
    ∀ k, k ≤ n → beob π (etiketten L fdom) B (ms k) = beob π (etiketten L fdom) B (ns k) :=
  ni_zeitplan π (etiketten L fdom) B P O passes init
    (abwicklung_aus_fluss π P O passes init L fdom hvoll hvollC hfl hW B hO hRL hOT)
    tafel sp₁ sp₂ hsp ms ns n hm hn

end Satz

end Gabbro.Grammatik
