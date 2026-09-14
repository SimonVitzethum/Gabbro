/-
  File:      Grammatik/ZielOrtMehrfaden.lean
  Subject:   SEVERAL ACTIVE THREADS WITH THREAD-LOCAL CARRIERS --
             `ziel_ort_mehrfaden`, the flagship (`ziel_ort_sperre_inv`) with a
             footprint condition that demands a guard only for carriers that
             one started thread reaches and a DIFFERENT started thread
             writes (SATZKARTE §14.6, §16.1).

  Until now a carrier touched by only one thread still needed a signature
  lock or a lock invariant, unless every other thread was idle
  (`ziel_ort_einfaden`). The generic replay of the flagship
  (`zielInvS_erreichbarL`) already took any set of "local" carriers `lok`
  with the rely `LokOk` (no step of another thread moves a local carrier of
  a frame). What was missing is a `lok` that describes thread-local carriers
  and the proof of `LokOk` for it; that needs to know, per thread, which
  functions can run on it -- a machine invariant G did not carry.

  * **Call graph per thread.** `K t : D.Fn → Bool`, closed under the calls
    of the bodies it admits (`AbgK`: every direct callee in `K t`, every
    function of the signature of an indirect call in `K t`) and containing
    the start function of `t`. `reachB` computes the reachable set from a
    start function; `abgB` decides the closure.
  * **Machine invariant.** `merkInvG_erreichbar` (`FadenMerkmal.lean`): on
    every reachable machine every frame of thread `t` runs a function of
    `K t` (the residue-to-body relation for calls, proved rule by rule).
  * **The footprint condition.** `GetrenntK P K c`: no thread reaches `c` in
    a footprint while a DIFFERENT thread can write it. `lokK P K` is that
    predicate; `FussS P S (lokK P K)` asks every footprint carrier to be
    signature-guarded, protected by a lock invariant, or thread-local in
    this sense. Decided for programs whose threads from `N` on are idle by
    `fussMehrB` (`fussMehrB_ok`).
  * **The rely** `lokOk_mehr`: a step of thread `u` writes only carriers its
    head function may write; that function is in `K u`; a frame of `t ≠ u`
    runs a function of `K t`; a thread-local carrier is therefore not
    written.
-/
import Grammatik.ZielOrtInv
import Grammatik.FadenMerkmal

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The flagship, generic in the local carriers -/

/-- **The flagship with table invariants, for any set of local carriers
    with the rely `LokOk`.** `ziel_ort_sperre_inv` is its instance at
    `freiB fs`; `ziel_ort_mehrfaden` its instance at the thread-local
    carriers. -/
theorem ziel_ort_sperre_invL (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      (VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M := by
  have hZ := zielInvS_erreichbarL P O passes Q S lok sp init e0 hO hRL hQ hlok hS hFragS hFS
    hLok hK hStart hSstart hex
  intro M hr
  refine ⟨?_, ?_⟩
  · have hI0 := hZ M hr
    have hP : KeinLogikHaltG O passes M :=
      fun t => fadenS_prueft hO hRL hQ hS hSstart hK hFS t (hI0.1.1 t)
    exact ⟨fun t ev hev => hI0.1.2 t ev hev, hI0.2, hP,
      fun t hH hA => schritt_an_pruefung t (hP t) hH hA⟩
  · induction hr with
    | start =>
        intro t ev hev g rho v s0 s1 h
        subst h
        simp [RufStartG] at hev
    | schritt M M' u hr' hs ih =>
        have hZ' := (hZ M hr').1
        intro t ev hev
        by_cases ht : t = u
        · subst ht
          rcases invLog_schritt hO hRL hQ hS hSstart hI hFS (hZ'.1 t).1 hs ev hev with h | h
          · exact ih t ev h
          · exact h
        · rw [rufSchrittG_fremd hs t ht] at hev
          exact ih t ev hev

/-! ## 2. The call graph of a thread -/

/-- The feature set "calls only into `Z`": a direct callee must be in `Z`,
    an indirect call's signature must have all its functions (of the
    member list) in `Z`; `locks` are not restricted. -/
def rufM (fs : List D.Fn) (Z : D.Fn → Bool) : Merkmal D :=
  ⟨Z, fun n => fs.all fun g => !(decide (D.sig g = n)) || Z g, fun _ => true⟩

theorem rufZiel_rufM {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) {Z : D.Fn → Bool}
    {g : D.Fn} (h : RufZiel (rufM fs Z) g) : Z g = true := by
  rcases h with h | h
  · exact h
  · have h1 := (List.all_eq_true.mp h) g (hvoll g)
    simpa using h1

/-- **The call graph of `Z` is closed**: every function in `Z` calls only
    into `Z`. -/
def AbgK (P : Programm D) (fs : List D.Fn) (Z : D.Fn → Bool) : Prop :=
  ∀ f, Z f = true → mE (rufM fs Z) (P.rumpf f) = true

/-- The closure, decided over the member list. -/
def abgB (P : Programm D) (fs : List D.Fn) (Z : D.Fn → Bool) : Bool :=
  fs.all fun f => !(Z f) || mE (rufM fs Z) (P.rumpf f)

theorem abgB_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {Z : D.Fn → Bool} (h : abgB P fs Z = true) : AbgK P fs Z := by
  intro f hf
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  simp only [hf, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem merkAbg_rufM {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {Z : D.Fn → Bool} (h : AbgK P fs Z) :
    MerkAbg P (fun f => Z f = true) (fun _ => rufM fs Z) :=
  fun f hf => ⟨h f hf, fun _ hg => rufZiel_rufM hvoll hg⟩

section Erreich

variable [DecidableEq D.Fn]

/-- `f`'s body calls `g` (directly, or through `g`'s signature). -/
def ruftB (P : Programm D) (f g : D.Fn) : Bool :=
  !(mE ⟨fun h => !(decide (h = g)), fun n => !(decide (n = D.sig g)), fun _ => true⟩ (P.rumpf f))

/-- One more round of the call graph. -/
def erreichSchritt (P : Programm D) (fs : List D.Fn) (Z : D.Fn → Bool) : D.Fn → Bool :=
  fun g => Z g || fs.any fun f => Z f && ruftB P f g

/-- The functions reachable from `wurzel` in `n` rounds. -/
def erreichB (P : Programm D) (fs : List D.Fn) (wurzel : D.Fn) : Nat → D.Fn → Bool
  | 0 => fun g => decide (g = wurzel)
  | n + 1 => erreichSchritt P fs (erreichB P fs wurzel n)

/-- **The call graph of a thread**: the functions reachable from its start
    function (as many rounds as there are functions). Its closure is
    checked, not assumed: `abgB P fs (reachB P fs w)`. -/
def reachB (P : Programm D) (fs : List D.Fn) (wurzel : D.Fn) : D.Fn → Bool :=
  erreichB P fs wurzel fs.length

theorem reachB_wurzel (P : Programm D) (fs : List D.Fn) (w : D.Fn) : reachB P fs w w = true := by
  unfold reachB
  induction fs.length with
  | zero => simp [erreichB]
  | succ n ih => simp [erreichB, erreichSchritt, ih]

end Erreich

/-! ## 3. Thread-local carriers and the rely -/

/-- **A carrier is thread-local**: no thread reaches it in a footprint
    while a DIFFERENT thread can write it. -/
def GetrenntK (P : Programm D) (K : Faden → D.Fn → Bool) (c : D.Tab ⊕ D.Glob) : Prop :=
  ∀ t u, t ≠ u → ∀ f, K t f = true → c ∈ fussOrteG P f →
    ∀ g, K u g = true → TraegerSchreibt g c = false

/-- The thread-local carriers, as a local-carrier predicate. -/
noncomputable def lokK (P : Programm D) (K : Faden → D.Fn → Bool) (c : D.Tab ⊕ D.Glob) : Bool :=
  @decide (GetrenntK P K c) (Classical.propDecidable _)

theorem lokK_ok {P : Programm D} {K : Faden → D.Fn → Bool} {c : D.Tab ⊕ D.Glob}
    (h : lokK P K c = true) : GetrenntK P K c := by
  unfold lokK at h
  exact @of_decide_eq_true _ (Classical.propDecidable _) h

theorem lokK_of {P : Programm D} {K : Faden → D.Fn → Bool} {c : D.Tab ⊕ D.Glob}
    (h : GetrenntK P K c) : lokK P K c = true := by
  unfold lokK
  exact @decide_eq_true _ (Classical.propDecidable _) h

section Rely

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for thread-local carriers**: on every reachable machine, a
    step of thread `u` leaves every thread-local carrier of every frame of
    every other thread alone. -/
theorem lokOk_mehr (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool) (hAbg : ∀ t, AbgK P fs (K t))
    (hWurzel : ∀ t, K t (init t).1 = true) :
    LokOk P O passes (lokK P K) sp init := by
  intro M M' u hr hs t htu F hF c hc hl
  have hInv := merkInvG_erreichbar (O := O) (pa := passes) sp init (fun t f => K t f = true)
    (fun t _ => rufM fs (K t)) (fun t => merkAbg_rufM hvoll (hAbg t)) hWurzel hr
  have hFt := (hInv t F hF).1
  have hUk := (hInv u _ List.mem_cons_self).1
  exact schritt_traeger hO hs c (Or.inr (lokK_ok hl t u htu F.f hFt (sicher_mem.mp hc).1 _ hUk))

end Rely

/-! ## 4. The theorem -/

/-- **ZIEL AM ORT FUER MEHRERE FAEDEN -- the flagship with thread-local
    carriers.** The premises of `ziel_ort_sperre_inv`, with the footprint
    check replaced by: every footprint carrier of every function is
    signature-guarded, protected by the invariant of one of its guards, or
    THREAD-LOCAL (`GetrenntK`: reached by one thread's call graph only
    among the threads that can write it), for per-thread call graphs `K`
    that are closed (`AbgK`) and contain each thread's start function.
    Several threads may be ACTIVE; a driver thread may keep private tables
    unguarded while sharing locked state with the others. The conclusion
    is that of `ziel_ort_sperre_inv`. -/
theorem ziel_ort_mehrfaden (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ f : D.Fn, InvGutS P passes Q S f) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      (VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
        ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
          AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M') ∧
      InvAmOrtG P M :=
  ziel_ort_sperre_invL P O passes Q S (lokK P K) sp init e0 hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) hK hStart hSstart hex hI

/-! ## 5. The old check is a special case -/

/-- The footprint property is monotone in the local carriers. -/
theorem fussS_mono {P : Programm D} {S : SperrInv D} {lok lok' : D.Tab ⊕ D.Glob → Bool}
    {f : D.Fn} (hl : ∀ c, c ∈ fussOrteG P f → lok c = true → lok' c = true)
    (h : FussS P S lok f) : FussS P S lok' f := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases h.1 c hc with h1 | h1
    · refine Or.inl ?_
      simp only [Bool.or_eq_true] at h1 ⊢
      exact h1.imp id (hl c (fuss_teilG P f hc))
    · exact Or.inr h1
  · have h1 := h.2 c hc
    simp only [Bool.or_eq_true] at h1 ⊢
    exact h1.imp id (hl c (List.mem_append_right _ hc))

/-- **`ziel_ort_sperre_inv` is the instance with one call graph for all
    threads**: a carrier written by no function is thread-local for every
    `K`. -/
theorem fussS_frei_mehr {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (K : Faden → D.Fn → Bool) {f : D.Fn}
    (h : FussS P S (freiB fs) f) : FussS P S (lokK P K) f :=
  fussS_mono (fun c _ hc => lokK_of fun _ _ _ _ _ _ g _ => freiB_ok hvoll hc g) h

/-! ## 6. A decidable check for finitely many active threads -/

/-- Thread-locality of `c`, decided over the threads below `N` and the
    member list. -/
def getrenntB (P : Programm D) (fs : List D.Fn) (K : Faden → D.Fn → Bool) (N : Nat)
    (c : D.Tab ⊕ D.Glob) : Bool :=
  (List.range N).all fun t => (List.range N).all fun u =>
    decide (t = u) || (fs.all fun f => !(K t f) || !(istIn (fussOrteG P f) c)) ||
      (fs.all fun g => !(K u g) || !(TraegerSchreibt g c))

/-- A thread is idle for the check: every function its call graph admits has
    an empty footprint and writes nothing. -/
def StummK (P : Programm D) (Z : D.Fn → Bool) : Prop :=
  ∀ f, Z f = true → fussOrteG P f = [] ∧ ∀ c, TraegerSchreibt f c = false

theorem getrenntB_ok {P : Programm D} {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {K : Faden → D.Fn → Bool} {N : Nat} (hN : ∀ t, N ≤ t → StummK P (K t))
    {c : D.Tab ⊕ D.Glob} (h : getrenntB P fs K N c = true) : GetrenntK P K c := by
  intro t u htu f hf hc g hg
  by_cases ht : N ≤ t
  · rw [(hN t ht f hf).1] at hc
    exact absurd hc List.not_mem_nil
  by_cases hu : N ≤ u
  · exact (hN u hu g hg).2 c
  have h1 := (List.all_eq_true.mp ((List.all_eq_true.mp h) t (List.mem_range.mpr (by omega))))
    u (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd h1 htu
  · have h2 := (List.all_eq_true.mp h1) f (hvoll f)
    have h3 : istIn (fussOrteG P f) c = true := istIn_iff.mpr hc
    rw [hf, h3] at h2
    simp at h2
  · have h2 := (List.all_eq_true.mp h1) g (hvoll g)
    rw [hg] at h2
    simpa using h2

/-- **The footprint check with thread-local carriers**, decided. -/
def fussMehrB (P : Programm D) (S : SperrInv D) (fs : List D.Fn) (K : Faden → D.Fn → Bool)
    (N : Nat) : Bool :=
  fs.all fun f =>
    (fussOrte P f).all (fun c =>
      sigB f c || getrenntB P fs K N c || (waechterVon c).any fun L => istIn (S.orte L) c) &&
    ((P.rumpf f).regs.flatMap D.rtraeger).all (fun c => sigB f c || getrenntB P fs K N c)

theorem fussMehrB_ok {P : Programm D} {S : SperrInv D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {K : Faden → D.Fn → Bool} {N : Nat}
    (hN : ∀ t, N ≤ t → StummK P (K t)) (h : fussMehrB P S fs K N = true) (f : D.Fn) :
    FussS P S (lokK P K) f := by
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  simp only [Bool.and_eq_true] at h1
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have h2 := (List.all_eq_true.mp h1.1) c hc
    simp only [Bool.or_eq_true] at h2
    rcases h2 with (h2 | h2) | h2
    · exact Or.inl (by simp [h2])
    · exact Or.inl (by simp [lokK_of (getrenntB_ok hvoll hN h2)])
    · obtain ⟨L, hL, hc'⟩ := List.any_eq_true.mp h2
      exact Or.inr ⟨L, waechterVon_mem.mp hL, istIn_iff.mp hc'⟩
  · have h2 := (List.all_eq_true.mp h1.2) c hc
    simp only [Bool.or_eq_true] at h2 ⊢
    rcases h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (lokK_of (getrenntB_ok hvoll hN h2))

#print axioms Gabbro.Grammatik.ziel_ort_sperre_invL
#print axioms Gabbro.Grammatik.lokOk_mehr
#print axioms Gabbro.Grammatik.ziel_ort_mehrfaden
#print axioms Gabbro.Grammatik.fussMehrB_ok

end Gabbro.Grammatik
