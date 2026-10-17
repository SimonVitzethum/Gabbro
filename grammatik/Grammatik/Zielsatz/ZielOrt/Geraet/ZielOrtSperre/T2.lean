/- Part 2 of 2 of `ZielOrtSperre` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtSperre.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. The other threads, the start, the invariant on every reachable machine -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **The rely for the replay**: a step of thread `u` leaves the stable
    carriers of the head frame of every other thread alone. -/
theorem andereS (hO : GutO O) (hS : SperrInvOk S) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hLok : LokOk P O passes lok sp init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) :
    FadenS P O passes Q S lok (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  exact fadenS_speicher hF (fun c hc =>
    stabilS_rely hO hS sp init hex hLok hr hs t htu _ List.mem_cons_self c hc)

/-- **The start machine is replayed.** -/
theorem zielInvS_start
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hStart : StartGut P sp init) :
    ZielInvS P O passes Q S lok (RufStartG P sp init) := by
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
    exact ⟨⟨[], [], [], sp.welt [], hStart t, funkV_nil, vertraegeOkR_nil P, kurzVB_nil _,
      funkA_nil, rahmenA_nil, vertragA_nil _ Q, kurzAB_nil _, funkU_nil, invU_nil S, kurzUB_nil _,
      GleichAuf.vonSpeicher rfl, ⟨hFragS _, fuss_rumpfG P _⟩,
      fun R O' U _ _ _ _ => ZErgG.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- **One step keeps the replay, the log and the machine lock invariant.**
    The acting thread by `akteurS` (fed by the machine lock invariant at
    the acquire), the other threads by the rely; a lock that the step
    releases has its invariant at the new memory by the release check the
    obligation proves (`kopfS_frei_inv`). -/
theorem zielInvS_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    (hLok : LokOk P O passes lok sp init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvS P O passes Q S lok M)
    (hSG : SperrInvG S M) :
    ZielInvS P O passes Q S lok M' ∧ SperrInvG S M' := by
  have hRS := rufG_rahmenS hO hS sp init hex hLok hr
  have hA := akteurS hO hRL hQ hlok hS hsp hK hFragS hFS hs (hI.1 u) (hI.2 u) (hRS u) hSG
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact hA.1
    · exact andereS hO hS sp init hex hLok hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact hA.2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t
  · refine sperrInvG_schritt hO hS hs hSG (fun L hL hL' => ?_)
    rcases freigabe_schrittG hO hs with hgr | ⟨l, Γ, Λ, L', k, ρ, hhead, hsp', hoff⟩ |
        ⟨Γ, Λ, Λ1, L', rest, k, ρ, h, x, hhead, hsp', hoff⟩
    · exact absurd (hgr L hL) hL'
    · have hLL : L = L' := by
        refine Classical.byContradiction fun hne => hL' ?_
        rw [hoff]
        exact (List.mem_erase_of_ne hne).mpr hL
      subst hLL
      rw [hsp']
      exact kopfS_frei_inv hO hRL hQ hS hsp hK (hI.1 u).1 L List.mem_cons_self hhead
        (fun O' U R σ hi => semH_frei_falsch S O' U passes R L k σ ρ hi)
    · have hLL : L = L' := by
        refine Classical.byContradiction fun hne => hL' ?_
        rw [hoff]
        exact (List.mem_erase_of_ne hne).mpr hL
      subst hLL
      rw [hsp']
      exact kopfS_frei_inv hO hRL hQ hS hsp hK (hI.1 u).1 L
        ((Block.held_iff rest L).mp List.mem_cons_self) hhead
        (fun O' U R σ hi => semH_peelFrei_falsch S O' U passes R L rest k σ ρ h x hi)

/-- **The replay invariant and the machine lock invariant on every
    reachable machine**, generic in the local carriers `lok`. -/
theorem zielInvS_erreichbarL (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ZielInvS P O passes Q S lok M ∧ SperrInvG S M := by
  intro M hr
  induction hr with
  | start => exact ⟨zielInvS_start hFragS sp init hStart, sperrInvG_start P S sp init hsp⟩
  | schritt M M' u hr' hs ih =>
      exact zielInvS_schritt hO hRL hQ hlok hS hsp hK hFragS hFS init hex hLok hr' hs ih.1 ih.2

/-- **The replay invariant and the machine lock invariant on every
    reachable machine**, for the local carriers written by no function. -/
theorem zielInvS_erreichbar (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ZielInvS P O passes Q S (freiB fs) M ∧ SperrInvG S M := by
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  exact zielInvS_erreichbarL P O passes Q S (freiB fs) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFS) hFS (lokOk_frei hO hvoll sp init) hK hStart hsp hex

/-- **A replayed thread is stopped at no `logik` check** (as
    `fadenR_prueft`). -/
theorem fadenS_prueft (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f) {M : RufMaschineG D}
    (t : Faden) (hF : FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) :
    PrueftG O passes M t := by
  have hK' := hF.1
  refine ⟨fun l Γ Λ ρ tb inv body ks k hr => ?_, fun l Γ Λ ρ a n inv body k hr => ?_,
    fun l Γ Λ Λx ρ tb inv body is k rest hl i hr => ?_,
    fun l Γ Λ Λ' ρ s K hb hr e he => ?_, fun l Γ Λ Λ' Λ'' ρ s rst k hb hr e he => ?_⟩
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semH_trav_falsch
    rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hok.1 h') h)
      (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semH_ewig_falsch
    rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hok.1 h') h)
      (hg.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    have hg' := gleichAuf_stabil_iff (fun L => Block.held_iff rest L) hg
    refine wahr_of_nicht_falsch fun hw => hno .schleife ?_
    apply semH_leaveTrav_falsch
    rw [eval_gleichAuf inv (fun _ h => expr_stabil (hFS _) inv (fun _ h' => hok.2.2.1 h') h)
      (hg'.lese Λ Λ inv.orte inv.orte) ρ]
    exact hw
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨_, hss, _⟩ := okS_ende_cons hok
    have hss' := orte_stabil (hFS _) (s.blatt_darf P hb) hss
    have h' := blatt_logik P s hb hss' hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    show zErgG (execEndH S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) (.cons s K) σ ρ) = _
    simp only [execEndH, execStmtH_blatt S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) s hb,
      h', zErgG]
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hK' hr
    obtain ⟨_, hss, _⟩ := okS_dann_cons hok
    have hss' := orte_stabil (hFS _) (s.blatt_darf P hb) hss
    have h' := blatt_logik P s hb hss' hg O (orakelAus O HA) passes keinRuf (rufAusL H) ρ e he
    refine hno e ?_
    rw [semH_dann_cons, execStmtH_blatt S (orakelAus O HA) (umweltAus S sp HU) passes (rufAusL H) s hb,
      h']
    exact weiterH_logik _ _ _ _ _ _ e

end Ziel
/-! ## 3. The goal theorem -/

/-- **ZIEL AM ORT MIT SPERRINVARIANTEN -- THE goal theorem.** Over the
    repaired machine G, for every program in the widened fragment
    (`programmImFragmentG`) whose footprint check WITH LOCK INVARIANTS passes
    (`fussSperreB`: every footprint carrier is guarded by a signature lock,
    written by no function, or protected by the invariant of one of its
    guards), for a well-formed family of lock invariants `S` that holds at
    the start memory, from an exclusive start (no two threads START holding
    the same lock) that meets the entry contracts, with an oracle that keeps
    the declared axiom frames and the held locks (`GutO`), answers registers
    and `awaits` from the declared carriers (`RegLokal`) and meets the
    declared axiom ensures `Q`, and whose every function meets the user
    obligation `KoerperGutS` -- the SEQUENTIAL body triple, caller duty and
    no `logik` outcome, where each `locks L` may assume `S.inv L` of the
    protected carriers and must re-establish it at the release -- EVERY
    reachable machine satisfies
    * `VertragAmOrtG`: `requires` at every logged entry, `ensures` at every
      logged return, with the actual values -- also for contracts over
      carriers that are only protected by `locks` blocks (verdict probes B,
      C);
    * `SperrInvG`: the invariant of every lock that no thread holds holds in
      the live memory;
    * `KeinLogikHaltG`: no thread is stopped at a `logik` check of G;
    * progress at the checks (as `ziel_ort_ganz`).

    Premises, by class: (a) user logic `KoerperGutS` (per function, over the
    SEQUENTIAL semantics with acquire moves and release checks), `StartGut`,
    the lock invariants at the start memory (`hSstart`); (b) hardware `GutO`,
    `RegLokal`, `AxVertragO Q`; (c) decidable program facts `hvoll`,
    `programmImFragmentG`, `fussSperreB`, `StartExklusiv` (N240 for constant
    starts), `AxEnsLokal Q`, and the family's well-formedness `SperrInvOk`
    (its first half decidable; its second -- the invariant reads only the
    listed carriers -- by construction for an invariant written over them).
    No event is needed (`Begruendet`, SperreBeweis.lean §0b). -/
theorem ziel_ort_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ SperrInvG S M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  have hFS : ∀ f, FussS P S (freiB fs) f := fussSperreB_ok hvoll hFuss
  have hI := zielInvS_erreichbar P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss
    hK hStart hSstart hex M hr
  have hP : KeinLogikHaltG O passes M :=
    fun t => fadenS_prueft hO hRL hQ hS hSstart hK hFS t (hI.1.1 t)
  exact ⟨fun t ev hev => hI.1.2 t ev hev, hI.2, hP, fun t hH hA => schritt_an_pruefung t (hP t) hH hA⟩

/-- **Progress at every check, UNCONDITIONALLY** (held-set relaxation,
    2026-09-13): the rules of G now demand `HeldIn` of the head's holdings,
    which holds on every reachable machine (`rufG_haelt_statisch`), so the
    `HeldGenau` hypothesis of the progress conjunct of `ziel_ort_sperre` is
    no longer needed: on every reachable machine a thread standing at a
    `logik` check can step. -/
theorem ziel_ort_sperre_fortschritt (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ∀ t : Faden, AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr t hA
  have hZ := ziel_ort_sperre P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK
    hStart hSstart hex M hr
  exact schritt_an_pruefungI t (hZ.2.2.1 t)
    (fun L hL => rufG_haelt_statisch hO sp init hr t _ List.mem_cons_self L hL) hA

/-- **A start without signature locks is exclusive**: when every thread's
    root takes its locks in `locks` blocks (holds none by signature),
    `StartExklusiv` holds for ANY assignment -- the same routine may run on
    every thread. The premise of the goal theorem is exactly "no two
    threads START holding the same lock"; with the acquire steps of G and
    the lock invariants, a routine that takes its lock in a block needs no
    more. -/
theorem startExklusiv_ohne_haelt (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (h : ∀ t, D.haelt (init t).1 = []) : StartExklusiv init :=
  fun t _ _ L hL _ => by
    rw [h t] at hL
    exact absurd hL List.not_mem_nil

/-- **`ziel_ort_ganz` is the special case of the empty family** (no
    protected carriers, invariant `true`): its footprint check gives the new
    one (`fussSperreB_of_G`), its obligation gives the new one
    (`koerperGutS_leer`: every environment move is the identity and the
    semantics is `execStmt`). -/
theorem ziel_ort_ganz_aus_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutZ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M ∧ KeinLogikHaltG O passes M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG P O passes M t M' := by
  intro M hr
  obtain ⟨h1, _, h3, h4⟩ := ziel_ort_sperre P O passes Q (SperrInv.leer D) fs sp init hO hRL hQ
    hlok sperrInvOk_leer hvoll hFrag (fussSperreB_of_G P _ fs hFuss)
    (fun f => koerperGutS_leer (hK f)) hStart (fun _ => rfl) hex M hr
  exact ⟨h1, h3, h4⟩

/-! ## CUTS:

  What is proved: `ziel_ort_sperre` -- over the repaired G, with a
  well-formed family of lock invariants `S` (protected carriers per lock,
  guarded by it; an invariant over them), the footprint check
  `fussSperreB` (a footprint carrier may be protected by the invariant of
  one of its guards instead of a signature lock), and the user obligation
  `KoerperGutS` (the sequential triple, caller duty and no `logik`
  outcome over the semantics in which every acquire may move the protected
  carriers within the invariant and every release checks it), every
  reachable machine satisfies `VertragAmOrtG`, `SperrInvG` (the invariant
  of every free lock holds in live memory), `KeinLogikHaltG` and progress at
  the checks. `ziel_ort_ganz` is its instance at the empty family
  (`ziel_ort_ganz_aus_sperre`). Every premise is used: `SperrInvOk` (the
  record moves are in the class, the rely on protected carriers, the
  machine invariant), `hSstart` (the machine invariant at the start, the
  default of the record moves), `fussSperreB` (reads inside stable
  carriers), `KoerperGutS` (both clauses: returns, calls, releases), the
  rest as in `ziel_ort_ganz`.

  What is NOT covered:

  - The invariant is a semantic family (`SperrInv.inv : Lock → Speicher →
    Bool`, local to its listed carriers), not a surface clause: nothing
    parses `lock L protects … invariant …`, and no checker rule computes
    `fussSperreB` or the first half of `SperrInvOk` (both decidable).
  - Precision of the environment's move: at an acquire of `L` the move may
    change EVERY carrier `L` protects, also one guarded by a second lock the
    frame already holds (no other thread can have changed it; the class is
    conservative, the user proves slightly more than needed for nested
    locks).
  - Held-set relaxation (2026-09-13, verdict note T): `RufPasst.hh` is now
    an inclusion (the callee's signature locks are among the caller's held
    locks), with lock floors (`Signatur.boden`, `RufPasst.hx`/`hb`) for the
    rank discipline across calls; G's side condition is `HeldIn`. The
    theorem above needed no change; `ziel_ort_sperre_fortschritt` drops the
    `HeldGenau` hypothesis of the progress conjunct. Witness: `helfer_zeuge`
    (`HelferZeuge.lean`).
  - A carrier read from only ONE thread still needs a guard, a signature
    lock or no writer (`sicher`); a concurrency-aware exemption needs the
    call graph of each thread, which no invariant of G carries yet.
  - Device carriers (register reads) are read without a guard at the
    access: they stay signature-guarded or unwritten.
  - Waiting at `dannLocks` (another thread holds `L`) is the named scheduler
    situation; no fairness or hold-time bound. Everything cut in
    `ZielOrtGanz.lean` (table invariants, termination, full progress) and
    `ZielOrtRahmen.lean` carries over.
-/

#print axioms Gabbro.Grammatik.akteurS
#print axioms Gabbro.Grammatik.zielInvS_erreichbar
#print axioms Gabbro.Grammatik.ziel_ort_sperre
#print axioms Gabbro.Grammatik.ziel_ort_sperre_fortschritt
#print axioms Gabbro.Grammatik.ziel_ort_ganz_aus_sperre


end Gabbro.Grammatik
