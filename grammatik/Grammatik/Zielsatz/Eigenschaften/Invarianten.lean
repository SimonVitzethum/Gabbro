/-
  File:      Grammatik/Zielsatz/Invarianten.lean -- the invariant legs of `Ziel`/`ZielF`
             (Opus agent D, 2026-09-26): `invRuhe`, `invSicht`, `sperrWechsel`,
             `sperrSicht` and `ZielF.spawnSicht`, PROVED.

  THE GAP. `Spec.lean`'s NOT CLAIMED list read "invariants at entry or while locks are held
  (claimed at returns only)". `Ziel` said: every table/group invariant a function owes holds
  at each of its logged returns (`invRueck`, `invGrund`), and every FREE lock has its
  invariant in memory (`sperrInv`). Nothing said what a function sees at its entry, what the
  acquirer of a lock starts from, or what another thread sees while a lock is held.

  WHAT IS TRUE, and why the literal "at every entry" is not:
  * A table/group invariant is owed by every function whose effects write one of its
    carriers (`schuldet`). Inside such a function it may be broken -- that is the point of a
    body. A function CALLED from inside a writer therefore may see it broken at its entry, so
    "at every entry" is false in general. What holds is: the invariant is intact at EVERY
    machine where no unfinished thread is inside a writer of it (`InvRuheG`), provided it
    reads only its carriers (`InvTraeger`) and held at the start. That covers every entry
    reached outside every writer, every thread start and spawn, and every machine at which the
    program's writers are all finished or not running. A thread holding a guard of the
    invariant and outside every writer sees it intact whatever the others do (`InvSichtG`).
  * A lock invariant: every step that acquires `L` starts from, and ends in, a memory where it
    holds, and every release leaves one (`SperrWechselG`). WHILE HELD, the holder may break
    it; "other threads never observe it broken" means exactly: every step that accesses a
    protected carrier holds `L`, and while a thread holds `L` no other step moves it
    (`SperrSichtG`). A held lock's invariant is observed by its holder alone. That is the only
    sense "while held" can have in G: the invariant is a predicate over shared memory, and
    the holder's writes ARE shared memory at once -- so the claim is about observation points,
    and it is exactly that.

  THE PROOF of `invRuhe` (induction over G runs, `invRuhe_erreichbar`). A step of thread `u`
  that is outside every writer moves no carrier of `i` (`schritt_traeger`: a step changes only
  what its head function may write). A step that ends the last active writer frame is either
  a POP -- read off the call log: every step appends at most one event
  (`schritt_logArt`, over the 70 rules), and the log determines the key stack
  (`rufLogPasstG_eind`), so the popped frame is the one whose `rueck`/`grund` event was just
  logged (`schritt_schluessel`), and `invRueck`/`invGrund` give the invariant at that event's
  world, which carries the memory the step leaves -- or the thread FINISHES at the writer's
  own return, and `StartEndeG` gives it there (`fertig_inv`).
-/
module
public import Grammatik.Zielsatz.Eigenschaften.InvariantenBasis
public import Grammatik.Zielsatz.Kern.Spec
@[expose] public section


namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}
/-! ## 4. Observation: through an invariant's guard, and at lock moves -/

section Sicht

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem invSicht_aus (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {i : D.Inv} (hJ : InvZu M i → InvHaelt P i (M.speicher.welt [])) (t : Faden)
    (ht : ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false)
    (hL : ∃ cb ∈ D.traeger i, ∃ L, Sum.inl L ∈ Sum.elim D.braucht D.gbraucht cb ∧ L ∈ offen (M.faeden t).spur) :
    InvHaelt P i (M.speicher.welt []) := by
  obtain ⟨cb, hcb, L, hLb, hLt⟩ := hL
  refine hJ fun u _ F hF => ?_
  by_cases hut : u = t
  · subst hut; exact ht F hF
  · refine Bool.eq_false_iff.mpr fun hs => ?_
    have hLF : L ∈ D.haelt F.f := D.invarianten_gehalten (D.sig F.f) i hs cb hcb L hLb
    have hLu := rufG_haelt_signatur hO sp init hr u F hF L hLF
    exact exklusivG hO sp init hex hr t u (fun e => hut e.symm) L hLt hLu

theorem sperrWechsel_aus (hO : GutO O) {S : SperrInv D} (hS : SperrInvOk S) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hSG : ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M → SperrInvG S M)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    SperrWechselG P O passes S M := by
  intro u M' L hs
  have hr' : RufErreichbarG P O passes (RufStartG P sp init) M' := .schritt _ _ _ hr hs
  refine ⟨fun hn hj => ?_, fun hj hn => ?_⟩
  · have hfrei : ∀ t, L ∉ offen (M.faeden t).spur := by
      intro t
      by_cases htu : t = u
      · subst htu; exact hn
      · rw [← rufSchrittG_fremd hs t htu]
        exact exklusivG hO sp init hex hr' u t (fun e => htu e.symm) L hj
    have h1 := hSG M hr L hfrei
    refine ⟨h1, ?_⟩
    rw [hS.2 L M'.speicher M.speicher fun c hc =>
      schritt_traeger hO hs c (Or.inl ⟨L, hS.1 L c hc, hn⟩)]
    exact h1
  · refine hSG M' hr' L fun t => ?_
    by_cases htu : t = u
    · subst htu; exact hn
    · rw [rufSchrittG_fremd hs t htu]
      exact exklusivG hO sp init hex hr u t (fun e => htu e.symm) L hj

theorem sperrSicht_aus (hO : GutO O) {S : SperrInv D} (hS : SperrInvOk S) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    SperrSichtG P O passes S M := by
  intro u M' hs L c hc
  exact ⟨fun hz => (zugriff_haelt sp init hO hex hr hs (hS.1 L c hc) hz).1,
    fun t htu hLt => relyG hO sp init hex hr hs t (fun e => htu e.symm) c L (hS.1 L c hc) hLt⟩

end Sicht
/-! ## 5. The legs, packaged for `ziel_aus`, and the frame half of OFFEN O11 -/

section Beine

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The leg `invRuhe`**, from the return legs at every reachable machine. -/
theorem invRuheG_aus (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hIR : ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M →
      InvAmOrtG P M ∧ InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    InvRuheG P (RufStartG P sp init) M :=
  fun _ hi hT h0 hZ => invRuhe_erreichbar hO sp init hIR hi hT h0 hr hZ

/-- **The leg `invSicht`**: `invRuhe` plus lock exclusivity and `U003` (a writer holds every
    guard of the invariant by signature). -/
theorem invSichtG_aus (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hIR : ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M →
      InvAmOrtG P M ∧ InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    InvSichtG P (RufStartG P sp init) M :=
  fun _ hi hT h0 t ht hL =>
    invSicht_aus hO sp init hex hr (invRuhe_erreichbar hO sp init hIR hi hT h0 hr) t ht hL

/-- **The frame half of OFFEN O11, in the model**: an invariant that NO function writes
    (`schuldet` false everywhere) holds at every reachable machine, given the start. Every
    other invariant is owed at every return of every writer (`LogikPflicht`: `InvGutS`,
    `InvGutGrund` for every function) -- so in the model no invariant is booked by nobody.
    The Rust side of the same fact is `N496`. -/
theorem inv_ohne_schreiber (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hIR : ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M →
      InvAmOrtG P M ∧ InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M)
    {i : D.Inv} (hi : i ∈ D.invs) (hT : InvTraeger P i) (h0 : InvHaelt P i (sp.welt []))
    (hw : ∀ f, schuldet f i = false)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    InvHaelt P i (M.speicher.welt []) :=
  invRuhe_erreichbar hO sp init hIR hi hT h0 hr fun _ _ F _ => hw F.f

/-- A thread-machine step that makes a dormant slot live is a spawn: it does not move the G
    state. -/
theorem faden_spawn_m {K K' : FadenMaschine D} {t : Faden}
    (hs : FadenSchritt P O passes K K') (h0 : K.lebt t = false) (h1 : K'.lebt t = true) :
    K'.m = K.m := by
  cases hs with
  | lauf f M' _ _ _ =>
      have h : K.lebt t = true := h1
      rw [h0] at h
      cases h
  | start => rfl
  | kind => rfl
  | join => rfl

end Beine

#print axioms Gabbro.Grammatik.Zielsatz.schritt_logArt
#print axioms Gabbro.Grammatik.Zielsatz.rufLogPasstG_eind
#print axioms Gabbro.Grammatik.Zielsatz.schritt_schluessel
#print axioms Gabbro.Grammatik.Zielsatz.fertig_abschluss
#print axioms Gabbro.Grammatik.Zielsatz.fertig_inv
#print axioms Gabbro.Grammatik.Zielsatz.invRuhe_erreichbar
#print axioms Gabbro.Grammatik.Zielsatz.invSicht_aus
#print axioms Gabbro.Grammatik.Zielsatz.sperrWechsel_aus
#print axioms Gabbro.Grammatik.Zielsatz.sperrSicht_aus
#print axioms Gabbro.Grammatik.Zielsatz.inv_ohne_schreiber
#print axioms Gabbro.Grammatik.Zielsatz.faden_spawn_m

end Gabbro.Grammatik.Zielsatz
