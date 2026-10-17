/- Part 2 of 2 of `ZielOrtAx` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtAx.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}

/-- **The rely for the replay** (as `andere_ok`): a step of thread `u`
    leaves the footprint of every head frame of another thread alone. -/
theorem andereA (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenA P O passes Q (M.faeden t) (M.weltVon t)) :
    FadenA P O passes Q (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenA_speicher hF (fun c hc => ?_)
  rcases fussOrtB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** -/
theorem zielInvA_start (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInvA P O passes Q (RufStartG P sp init) := by
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
    exact ⟨⟨[], [], sp.welt [], hStart t, funkV_nil, vertraegeOkV_nil P, kurzV_nil _, funkA_nil,
      rahmenA_nil, vertragA_nil _ Q, kurzA_nil _, GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpf P _⟩,
      fun R O' _ _ _ => ZErg.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant. -/
theorem zielInvA_schritt (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (hK : ∀ f, KoerperGutA P passes Q f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvA P O passes Q M) :
    ZielInvA P O passes Q M' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteurA hO hQ hlok hK hFrag e0 hs (hI.1 t) (hI.2 t)).1
    · exact andereA hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteurA hO hQ hlok hK hFrag e0 hs (hI.1 t) (hI.2 t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **ZIEL AM ORT, FULL LANGUAGE, WITH DECLARED AXIOM ENSURES
    (`ziel_ort_voll_ax`)** -- contracts hold at their place on every
    machine of the repaired concurrent call machine G, for bodies with
    loops, exits, the error channel and axiom calls whose contracts may
    depend on the axioms' results and declared writes.

    Premises, by class:
    * (a) user obligations: `KoerperGutA P passes Q f` for every function
      (the body's Hoare triple over the SEQUENTIAL semantics with any
      contract-respecting call handler AND any oracle respecting the
      declared axiom frames AND meeting the declared axiom ensures `Q`, and
      its caller duty), `StartGut` and `StartExklusiv`;
    * (b) hardware: `GutO O` and `AxVertragO Q O` (the machine's axioms
      meet their declared ensures);
    * the declaration: `AxEnsLokal Q` (each declared ensures reads only the
      result and the axiom's declared write carriers);
    * (c) decidable program facts over a complete member list `fs`: the
      covered fragment (`programmImFragmentV`: no register read, no
      `awaits`; an indirect call only where every function of its
      signature has its contract carriers in the caller's footprint) and
      the footprint check (`fussOrtB`);
    * the declaration declares a table, a global or a lock (`e0`: an event
      exists; it gives each recorded call answer and each recorded axiom
      answer a fresh trace position).

    Conclusion: on EVERY machine reachable from the start machine, at every
    `eintritt` of every thread log the callee's `requires` holds with the
    actual parameters at the actual entry world, and at every `rueck` the
    `ensures` holds with the actual entry world, return world, parameters
    and result. -/
theorem ziel_ort_voll_ax (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutA P passes Q f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  have hFragF : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true :=
    programmImFragmentV_ok P hvoll hFrag
  intro M hr
  have hI : ZielInvA P O passes Q M := by
    induction hr with
    | start => exact zielInvA_start hFragF sp init hStart
    | schritt M M' u hr' hs ih =>
        exact zielInvA_schritt hO hQ hlok hvoll hFuss hK hFragF e0 sp init hex hr' hs ih
  exact fun t ev hev => hI.2 t ev hev

/-- `ziel_ort_voll` is the special case of the trivial declared ensures
    (`Q = true`): every oracle meets it, and `KoerperGutV` gives
    `KoerperGutA`. -/
theorem ziel_ort_voll_aus_ax (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutV P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_voll_ax P O passes (fun _ _ _ => true) fs sp init e0 hO (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl) hvoll hFrag hFuss (fun f => koerperGutA_of_V _ (hK f)) hStart hex

end Ziel
/-! ## CUTS:

  What is proved: `ziel_ort_voll_ax` -- the goal over G with the
  strengthened obligation `KoerperGutA` (body triple against every
  frame-respecting oracle that meets the declared axiom ensures `Q`), for
  every program in the fragment of `ziel_ort_voll`, under `GutO O`,
  `AxVertragO Q O` and `AxEnsLokal Q`; `ziel_ort_voll` as its special case
  `Q = true` (`ziel_ort_voll_aus_ax`, a second proof of the same statement).
  The witness with a result-dependent contract is `ziel_ort_voll_ax_zeuge`
  (`ZielOrtAxZeuge.lean`).

  What is NOT covered: declared ensures that read the axiom's OLD world or
  its parameters (`AxEnsLokal` restricts `Q` to the result and the post
  values of the declared write carriers: the replay's record world
  `axWelt` agrees with the machine's answer world only there); the device
  forms of `ziel_ort_geraet` (register reads, `awaits`) with declared axiom
  ensures -- the same extension of `ZielOrtGeraetBeweis.lean` was not built.
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.ziel_ort_voll_ax
#print axioms Gabbro.Grammatik.ziel_ort_voll_aus_ax

