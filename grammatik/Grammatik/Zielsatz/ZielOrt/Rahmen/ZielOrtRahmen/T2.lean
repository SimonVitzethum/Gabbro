/- Part 2 of 2 of `ZielOrtRahmen` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtRahmen.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmen.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **The rely for the replay** (as `andere_ok`): a step of thread `u`
    leaves the footprint of every head frame of another thread alone. -/
theorem andereR (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenR P O passes Q (M.faeden t) (M.weltVon t)) :
    FadenR P O passes Q (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenR_speicher hF (fun c hc => ?_)
  rcases fussOrtGB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** -/
theorem zielInvR_start
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInvR P O passes Q (RufStartG P sp init) := by
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
    exact ⟨⟨[], [], sp.welt [], hStart t, funkV_nil, vertraegeOkR_nil P, kurzV_nil _, funkA_nil,
      rahmenA_nil, vertragA_nil _ Q, kurzA_nil _, GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpfG P _⟩,
      fun R O' _ _ _ => ZErg.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant; the acting thread uses the
    machine's frame fact at the pre-step machine (`rufG_rahmen`). -/
theorem zielInvR_schritt (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (hK : ∀ f, KoerperGutRQ P passes Q f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvR P O passes Q M) :
    ZielInvR P O passes Q M' := by
  have hRS := rufG_rahmen hO hvoll hFuss sp init hex hr
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteurR hO hRL hQ hlok hK hFrag e0 hs (hI.1 t) (hI.2 t) (hRS t)).1
    · exact andereR hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteurR hO hRL hQ hlok hK hFrag e0 hs (hI.1 t) (hI.2 t) (hRS t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **The replay invariant on every reachable machine**, generic in the
    declared axiom ensures `Q` (the oracle meets it, `AxVertragO Q O`; it
    reads only the declared carriers, `AxEnsLokal Q`) and over the
    obligation `KoerperGutRQ`. `ziel_ort_rahmen` is its instance at the
    trivial ensures; the goal theorem `ziel_ort_ganz` (`ZielOrtGanz.lean`)
    reads the head replay it carries. -/
theorem zielInvR_erreichbar (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (fs : List D.Fn) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (e0 : Ereignis D) (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutRQ P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      ZielInvR P O passes Q M := by
  have hFragF : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true :=
    programmImFragmentG_ok P hvoll hFrag
  intro M hr
  induction hr with
  | start => exact zielInvR_start hFragF sp init hStart
  | schritt M M' u hr' hs ih =>
      exact zielInvR_schritt hO hRL hQ hlok hvoll hFuss hK hFragF e0 sp init hex hr' hs ih

/-- **ZIEL AM ORT AGAINST DECLARED FRAMES -- contracts hold at their place
    on every machine of the repaired concurrent call machine G, for the
    fragment of `ziel_ort_geraet`, with the user obligation weakened to the
    body triple against frame-respecting call handlers.**

    Premises, by class:
    * (a) user obligations: `KoerperGutR P passes f` for every function (the
      body's Hoare triple over the SEQUENTIAL semantics with any call handler
      that respects the callees' contracts AND their declared write sets and
      held locks, any oracle that respects the declared axiom frames and is
      register-local, and its caller duty), `StartGut` and `StartExklusiv`
      (the boot assignment);
    * (b) hardware: `GutO O`, `RegLokal O`;
    * (c) decidable program facts over a complete member list `fs`: the
      widened fragment (`programmImFragmentG`) and the widened footprint
      check (`fussOrtGB`);
    * the declaration declares a table, a global or a lock (`e0`).

    The frame the obligation assumes of a callee is not a premise: the
    machine delivers it (`rufG_rahmen`, from the signature permission on
    every write, `RufPasst` at every push, the footprint check, the held
    signature locks and the exclusive start).

    Conclusion: `VertragAmOrtG` on EVERY machine reachable from the start
    machine. -/
theorem ziel_ort_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutR P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  intro M hr
  have hI := zielInvR_erreichbar P O passes (axWahr D) fs sp init e0 hO hRL (axVertragO_wahr O)
    axEnsLokal_wahr hvoll hFrag hFuss (fun f => koerperGutRQ_of_R (axWahr D) (hK f)) hStart hex M hr
  exact fun t ev hev => hI.2 t ev hev

end Ziel
/-! ## 3. The earlier theorems are special cases -/

/-- **`ziel_ort_geraet` from `ziel_ort_rahmen`**: the same premises, the
    old obligation gives the new one (`koerperGutR_of_G`). -/
theorem ziel_ort_geraet_aus_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutG P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_rahmen P O passes fs sp init e0 hO hRL hvoll hFrag hFuss
    (fun f => koerperGutR_of_G (hK f)) hStart hex

/-- **`ziel_ort_voll` on register-local oracles from `ziel_ort_rahmen`**
    (the statement of `ziel_ort_voll_lokal`). -/
theorem ziel_ort_voll_lokal_aus_rahmen (P : Programm D) (O : Orakel D) (passes : Nat)
    (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutV P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_rahmen P O passes fs sp init e0 hO hRL hvoll (programmImFragmentG_of_V P fs hFrag)
    (fussOrtGB_of_V P fs hFrag hFuss) (fun f => koerperGutR_of_V (hK f)) hStart hex

/-- **`ziel_ort` on register-local oracles from `ziel_ort_rahmen`**: the
    premises of `ziel_ort` plus `RegLokal O`. -/
theorem ziel_ort_lokal_aus_rahmen (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragment P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGut P O passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_voll_lokal_aus_rahmen P O passes fs sp init e0 hO hRL hvoll
    (programmImFragmentV_of P fs hFrag) hFuss
    (fun f => koerperGutV_of_kOk P O passes f ((List.all_eq_true.mp hFrag) f (hvoll f)) (hK f))
    hStart hex

/-! ## CUTS:

  What is proved: `ziel_ort_rahmen` -- over the repaired G, for every
  program in the widened fragment of `ziel_ort_geraet` whose widened
  footprint check passes, whose bodies satisfy `KoerperGutR` (the triple
  against call handlers that respect contracts AND declared frames), whose
  start assignment is exclusive and meets `StartGut`, with an oracle
  satisfying `GutO` and `RegLokal`, every reachable machine satisfies
  `VertragAmOrtG`. Every premise is used: `GutO` (rely, held locks, axiom
  frames, the machine frame fact), `RegLokal` (register and visibility
  steps, the record oracle for the obligation), `hvoll`,
  `programmImFragmentG`, `fussOrtGB` (the rely of head frames AND of every
  suspended frame, `rufG_rahmen`), `KoerperGutR` (`popR_ens`, `pushR_req`),
  `StartGut`, `StartExklusiv` (`exklusivG` inside `rufG_rahmen` and
  `andereR`), `e0` (fresh trace positions). The earlier theorems follow:
  `ziel_ort_geraet` (`ziel_ort_geraet_aus_rahmen`, same premises),
  `ziel_ort_voll` on register-local oracles
  (`ziel_ort_voll_lokal_aus_rahmen`) and `ziel_ort` on register-local
  oracles (`ziel_ort_lokal_aus_rahmen`). The corpus program
  `beispiele/104-referenz.gab`, whose `einzahlen` refutes the old
  obligation, is certified in `Referenz104Rahmen.lean`.

  What is NOT covered:

  - `ziel_ort_voll` and `ziel_ort` for NON-local oracles are not derived
    from `ziel_ort_rahmen` (its obligation quantifies over register-local
    oracles only); they stay as proved. Since 2026-09-13 the replay here is
    generic in a declared axiom ensures `Q` (`zielInvR_erreichbar`), so
    `ziel_ort_voll_ax` on register-local oracles IS derived
    (`ziel_ort_voll_ax_lokal_aus_ganz`, `ZielOrtGanz.lean`); for non-local
    oracles it stays as proved.
  - `ziel_ort_rahmen` is vacuous past a failing `logik` check (a false loop
    invariant, a transition from the wrong pre-state): its obligation does
    not ask for them, and G stops there before any return is logged (probe A,
    `paP_rahmen_zertifiziert`, `ZielOrtGanzZeuge.lean`). The goal theorem
    that closes this is `ziel_ort_ganz` (`ZielOrtGanz.lean`).
  - The handler class bounds NORMAL answers only; a reason answer
    (`grund`) carries no frame in the obligation (the machine keeps the
    frame for it too, and the replay records it with the frame-shaped
    answer world, but the user may not assume it).
  - The frame a caller may assume is its callee's declared write SET
    (tables and globals, whole carriers): a callee that writes one slot of a
    table may, for the caller, have changed every slot of it. No finer
    (per-slot, per-field) frame.
  - The cuts of `ziel_ort_geraet` carry over unchanged (device-driven
    change, locks-block-only readers, the minimal visibility locality,
    no-event declarations, stuck states, the converse adequacy).
-/

#print axioms Gabbro.Grammatik.akteurR
#print axioms Gabbro.Grammatik.andereR
#print axioms Gabbro.Grammatik.zielInvR_erreichbar
#print axioms Gabbro.Grammatik.ziel_ort_rahmen
#print axioms Gabbro.Grammatik.ziel_ort_geraet_aus_rahmen
#print axioms Gabbro.Grammatik.ziel_ort_voll_lokal_aus_rahmen
#print axioms Gabbro.Grammatik.ziel_ort_lokal_aus_rahmen


end Gabbro.Grammatik
