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
  own return, and `StartEndeG` gives it there (`fertig_retKopf`).
-/
import Grammatik.Zielsatz.Spec

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The call log moves by at most one event per step -/

section Log

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **Every step appends at most ONE call-log event**, and a return event's world carries the
    memory the step leaves behind. -/
theorem schritt_logArt {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') :
    (M'.faeden u).log = (M.faeden u).log ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D),
      (M'.faeden u).log = RufEreignisF.eintritt g rho s0 :: (M.faeden u).log) ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      (M'.faeden u).log = RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log ∧
        s1.speicher = M'.speicher) ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
      (M'.faeden u).log = RufEreignisF.grund g rho r s0 s1 :: (M.faeden u).log ∧
        s1.speicher = M'.speicher) := by
  cases hs <;> (try simp only [rufUpdateG_self]) <;> first
    | exact Or.inl trivial
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, rfl, speicher_welt_speicher _ _⟩))

end Log

/-- A log determines its key stack. -/
theorem rufLogPasstG_eind :
    ∀ {ks ks' : List (Σ f : D.Fn, Env D (D.params f) × World D)} {log : List (RufEreignisF D)},
      RufLogPasstG ks log → RufLogPasstG ks' log → ks = ks' := by
  intro ks ks' log h
  induction h generalizing ks' with
  | leer => intro h'; cases h'; rfl
  | eintritt ks log f rho s0 h ih =>
      intro h'
      cases h' with
      | eintritt _ _ _ _ _ h2 => rw [ih h2]
  | rueck ks log f rho s0 v s1 h ih =>
      intro h'
      cases h' with
      | rueck _ _ _ _ _ _ _ h2 =>
          have := ih h2
          exact (List.cons.inj this).2
  | grund ks log f rho s0 r s1 h ih =>
      intro h'
      cases h' with
      | grund _ _ _ _ _ _ _ h2 =>
          have := ih h2
          exact (List.cons.inj this).2

/-! ## 2. The key stack a step leaves -/

section Schluessel

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **How a step moves a thread's key stack**: unchanged, one frame pushed, or the head frame
    popped with a logged return whose world carries the memory the step leaves. -/
theorem schritt_schluessel (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M M' : RufMaschineG D} {u : Faden}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    (hs : RufSchrittG P O passes M u M') :
    RufFadenSchluesselG (M'.faeden u) = RufFadenSchluesselG (M.faeden u) ∨
    (∃ k, RufFadenSchluesselG (M'.faeden u) = k :: RufFadenSchluesselG (M.faeden u)) ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (v : ErgVal D (D.erg g)) (s0 s1 : World D),
      RufFadenSchluesselG (M.faeden u) = ⟨g, rho, s0⟩ :: RufFadenSchluesselG (M'.faeden u) ∧
      RufEreignisF.rueck g rho v s0 s1 ∈ (M'.faeden u).log ∧ s1.speicher = M'.speicher) ∨
    (∃ (g : D.Fn) (rho : Env D (D.params g)) (r : Fin (D.gruende g)) (s0 s1 : World D),
      RufFadenSchluesselG (M.faeden u) = ⟨g, rho, s0⟩ :: RufFadenSchluesselG (M'.faeden u) ∧
      RufEreignisF.grund g rho r s0 s1 ∈ (M'.faeden u).log ∧ s1.speicher = M'.speicher) := by
  have h0 := rufErreichbarG_passt P O passes sp init M hr u
  have h1 := rufErreichbarG_passt P O passes sp init M' (.schritt _ _ _ hr hs) u
  unfold RufFadenPasstG at h0 h1
  rcases schritt_logArt hs with he | ⟨g, rho, s0, he⟩ | ⟨g, rho, v, s0, s1, he, hsp⟩ |
      ⟨g, rho, r, s0, s1, he, hsp⟩
  · rw [he] at h1
    exact Or.inl (rufLogPasstG_eind h1 h0)
  · rw [he] at h1
    generalize RufFadenSchluesselG (M'.faeden u) = ks at h1 ⊢
    cases h1 with
    | eintritt _ _ _ _ _ h2 => exact Or.inr (Or.inl ⟨_, by rw [rufLogPasstG_eind h2 h0]⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨g, rho, v, s0, s1, ?_, by rw [he]; exact List.mem_cons_self,
      hsp⟩))
    rw [he] at h1
    generalize RufFadenSchluesselG (M'.faeden u) = ks at h1 ⊢
    cases h1 with
    | rueck _ _ _ _ _ _ _ h2 => exact (rufLogPasstG_eind h2 h0).symm
  · refine Or.inr (Or.inr (Or.inr ⟨g, rho, r, s0, s1, ?_, by rw [he]; exact List.mem_cons_self,
      hsp⟩))
    rw [he] at h1
    generalize RufFadenSchluesselG (M'.faeden u) = ks at h1 ⊢
    cases h1 with
    | grund _ _ _ _ _ _ _ h2 => exact (rufLogPasstG_eind h2 h0).symm

end Schluessel

/-! ## 3. Table and group invariants outside every writer -/

theorem invZu_schluessel {z : RufFadenG D} {i : D.Inv} :
    (∀ F ∈ z.kopf :: z.stapel, schuldet F.f i = false) ↔
      ∀ k ∈ RufFadenSchluesselG z, schuldet k.1 i = false := by
  unfold RufFadenSchluesselG
  constructor
  · intro h k hk
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hk
    exact h F hF
  · intro h F hF
    exact h _ (List.mem_map.mpr ⟨F, hF, rfl⟩)

theorem invHaelt_speicher (P : Programm D) (i : D.Inv) {σ σ' : World D}
    (h : σ.speicher = σ'.speicher) : InvHaelt P i σ ↔ InvHaelt P i σ' := by
  unfold InvHaelt
  rw [eval_gleichAuf (P.invariante i) (fun _ h => h) (GleichAuf.vonSpeicher h) .nil]

section Ruhe

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- A finished thread (empty stack, head at a return) stands at a VALUE return: a start frame
    never stands at a reason return (`KeinStartGrundG`). -/
theorem fertig_retKopf {M : RufMaschineG D} {t : Faden} (hF : FertigG M t)
    (hK : KeinStartGrundG M) :
    ∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ ∧ RetKopf e r := by
  obtain ⟨hst, han⟩ := hF
  have hK' := hK t hst
  generalize (M.faeden t).kopf.rest = R at han hK' ⊢
  obtain ⟨l, Γ, Λ, ρ, r⟩ := R
  have hKt := hK' l Γ Λ ρ r rfl
  simp only at han
  cases r with
  | ende e' =>
      cases e' with
      | ret e hp => exact ⟨_, _, _, _, _, e, rfl, hp, Or.inl rfl⟩
      | retGrund g hp => exact absurd ⟨g, hp, Or.inl rfl⟩ hKt
      | cons s rest =>
          cases s with
          | ret e hp => exact ⟨_, _, _, _, _, e, rfl, hp, Or.inr (Or.inl ⟨rest, rfl⟩)⟩
          | retGrund g hp => exact absurd ⟨g, hp, Or.inr (Or.inl ⟨rest, rfl⟩)⟩ hKt
          | _ => simp [GRest.anRueck, Endblock.istRueck, Stmt.istRueck] at han
      | _ => simp [GRest.anRueck, Endblock.istRueck] at han
  | dann b k =>
      cases b with
      | cons s rest =>
          cases s with
          | ret e hp => exact ⟨_, _, _, _, _, e, rfl, hp, Or.inr (Or.inr ⟨_, rest, k, rfl⟩)⟩
          | retGrund g hp => exact absurd ⟨g, hp, Or.inr (Or.inr ⟨_, rest, k, rfl⟩)⟩ hKt
          | _ => simp [GRest.anRueck, Block.istRueck, Stmt.istRueck] at han
      | _ => simp [GRest.anRueck, Block.istRueck] at han
  | _ => simp [GRest.anRueck] at han

/-- **A TABLE INVARIANT HOLDS WHEREVER NO UNFINISHED THREAD IS INSIDE A WRITER.** -/
theorem invRuhe_erreichbar (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hIR : ∀ M, RufErreichbarG P O passes (RufStartG P sp init) M →
      InvAmOrtG P M ∧ InvAmGrundG P M ∧ StartEndeG P M ∧ KeinStartGrundG M)
    {i : D.Inv} (hi : i ∈ D.invs) (hT : InvTraeger P i) (h0 : InvHaelt P i (sp.welt [])) :
    ∀ {M : RufMaschineG D}, RufErreichbarG P O passes (RufStartG P sp init) M →
      InvZu M i → InvHaelt P i (M.speicher.welt []) := by
  intro M hr
  induction hr with
  | start => intro _; exact h0
  | schritt M M' u hr hs ih =>
      intro hZ'
      have hr' : RufErreichbarG P O passes (RufStartG P sp init) M' := .schritt _ _ _ hr hs
      have hwelt : ∀ s1 : World D, s1.speicher = M'.speicher →
          InvHaelt P i s1 → InvHaelt P i (M'.speicher.welt []) := fun s1 hs1 h =>
        (invHaelt_speicher P i (hs1.trans (speicher_welt_speicher _ _).symm)).mp h
      by_cases hU : ∀ F ∈ (M.faeden u).kopf :: (M.faeden u).stapel, schuldet F.f i = false
      · -- nothing of `u` owes `i`: the step leaves the carriers of `i` alone
        have hZ : InvZu M i := by
          intro t hFt F hF
          by_cases htu : t = u
          · subst htu; exact hU F hF
          · have he := rufSchrittG_fremd hs t htu
            refine hZ' t (fun h => hFt ?_) F (by rw [he]; exact hF)
            unfold FertigG at h ⊢
            rw [he] at h
            exact h
        have hIH := ih hZ
        have hkopf : schuldet (M.faeden u).kopf.f i = false := hU _ List.mem_cons_self
        have hgl : GleichAuf (P.invariante i).orte (M'.speicher.welt []) (M.speicher.welt []) := by
          refine ⟨fun tb htb => ?_, fun g hg => ?_⟩
          · obtain ⟨t', ht', he⟩ := hT _ htb
            cases he
            have hw : TraegerSchreibt (M.faeden u).kopf.f (Sum.inl tb) = false := by
              show D.schreibt (M.faeden u).kopf.f tb = false
              unfold schuldet at hkopf
              exact Bool.eq_false_iff.mpr fun hw =>
                Bool.false_ne_true (hkopf ▸ List.any_eq_true.mpr ⟨tb, ht', hw⟩)
            exact schritt_traeger hO hs (.inl tb) (Or.inr hw)
          · obtain ⟨_, _, he⟩ := hT _ hg
            cases he
        unfold InvHaelt at hIH ⊢
        rw [eval_gleichAuf (P.invariante i) (fun _ h => h) hgl .nil]
        exact hIH
      · -- a frame of `u` owed `i`: it is either the head of a now FINISHED `u`, or popped
        have hne : ¬ ∀ k ∈ RufFadenSchluesselG (M.faeden u), schuldet k.1 i = false :=
          fun h => hU (invZu_schluessel.mpr h)
        obtain ⟨k0, hk0, hs0⟩ : ∃ k0 ∈ RufFadenSchluesselG (M.faeden u), schuldet k0.1 i = true :=
          Classical.byContradiction fun hn =>
            hne fun k hk => Bool.eq_false_iff.mpr fun h => hn ⟨k, hk, h⟩
        by_cases hk : k0 ∈ RufFadenSchluesselG (M'.faeden u)
        · -- the owing frame survives: `u` must be finished, at a return of that frame
          by_cases hFu : FertigG M' u
          · have hst := hFu.1
            have hkk : k0 = RufSchluesselG (M'.faeden u).kopf := by
              unfold RufFadenSchluesselG at hk
              rw [hst] at hk
              exact List.mem_singleton.mp hk
            obtain ⟨-, -, hSE, hKS⟩ := hIR M' hr'
            obtain ⟨l, Γ, Λ, ρ, r, e, hrest, hret⟩ := fertig_retKopf hFu hKS
            have hI := (hSE u hst l Γ Λ ρ r e hrest hret).2
            refine hwelt _ ?_ (hI i hi ?_)
            · show (M'.weltVon u).speicher = M'.speicher
              exact speicher_welt_speicher _ _
            · rw [hkk] at hs0; exact hs0
          · exact absurd hs0 (by
              rw [(invZu_schluessel (z := M'.faeden u)).mp (hZ' u hFu) k0 hk]; decide)
        · rcases schritt_schluessel sp init hr hs with he | ⟨k, he⟩ |
              ⟨g, rho, v, s0, s1, he, hmem, hsp⟩ | ⟨g, rho, r, s0, s1, he, hmem, hsp⟩
          · exact absurd (he ▸ hk0) hk
          · exact absurd (he ▸ List.mem_cons_of_mem _ hk0) hk
          · rw [he] at hk0
            rcases List.mem_cons.mp hk0 with rfl | hk'
            · exact hwelt s1 hsp ((hIR M' hr').1 u _ hmem g rho v s0 s1 rfl i hi hs0)
            · exact absurd hk' hk
          · rw [he] at hk0
            rcases List.mem_cons.mp hk0 with rfl | hk'
            · exact hwelt s1 hsp ((hIR M' hr').2.1 u _ hmem g rho r s0 s1 rfl i hi hs0)
            · exact absurd hk' hk

end Ruhe

/-! ## 4. Observation: through an invariant's guard, and at lock moves -/

section Sicht

variable {P : Programm D} {O : Orakel D} {passes : Nat}

theorem invSicht_aus (hO : GutO O) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {i : D.Inv} (hJ : InvZu M i → InvHaelt P i (M.speicher.welt [])) (t : Faden)
    (ht : ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, schuldet F.f i = false)
    (hL : ∃ tb ∈ D.traeger i, ∃ L, Sum.inl L ∈ D.braucht tb ∧ L ∈ offen (M.faeden t).spur) :
    InvHaelt P i (M.speicher.welt []) := by
  obtain ⟨tb, htb, L, hLb, hLt⟩ := hL
  refine hJ fun u _ F hF => ?_
  by_cases hut : u = t
  · subst hut; exact ht F hF
  · refine Bool.eq_false_iff.mpr fun hs => ?_
    have hLF : L ∈ D.haelt F.f := D.invarianten_gehalten (D.sig F.f) i hs tb htb L hLb
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
#print axioms Gabbro.Grammatik.Zielsatz.fertig_retKopf
#print axioms Gabbro.Grammatik.Zielsatz.invRuhe_erreichbar
#print axioms Gabbro.Grammatik.Zielsatz.invSicht_aus
#print axioms Gabbro.Grammatik.Zielsatz.sperrWechsel_aus
#print axioms Gabbro.Grammatik.Zielsatz.sperrSicht_aus
#print axioms Gabbro.Grammatik.Zielsatz.inv_ohne_schreiber
#print axioms Gabbro.Grammatik.Zielsatz.faden_spawn_m

end Gabbro.Grammatik.Zielsatz
