/- Part 2 of 2 of `ZielOrtGeraet` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtGeraet.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 2. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for the replay** (as `andere_ok`): a step of thread `u`
    leaves the footprint of every head frame of another thread alone. -/
theorem andereG (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenG P O passes (M.faeden t) (M.weltVon t)) :
    FadenG P O passes (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenG_speicher hF (fun c hc => ?_)
  rcases fussOrtGB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** -/
theorem zielInvG_start
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInvG P O passes (RufStartG P sp init) := by
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
      rahmenA_nil, kurzA_nil _, GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpfG P _⟩,
      fun R O' _ _ _ => ZErg.folgt_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant. -/
theorem zielInvG_schritt (hO : GutO O) (hRL : RegLokal O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (hK : ∀ f, KoerperGutG P passes f)
    (hFrag : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true)
    (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInvG P O passes M) :
    ZielInvG P O passes M' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteurG hO hRL hK hFrag e0 hs (hI.1 t) (hI.2 t)).1
    · exact andereG hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteurG hO hRL hK hFrag e0 hs (hI.1 t) (hI.2 t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **ZIEL AM ORT WITH DEVICES -- contracts hold at their place on every
    machine of the repaired concurrent call machine G, for bodies with
    loops, exits, the error channel, axiom calls, indirect calls, register
    reads (with and without `else`), register writes, `transition`,
    `exchange` and `awaits`.**

    Premises, by class:
    * (a) user obligations: `KoerperGutG P passes f` for every function
      (the body's Hoare triple over the SEQUENTIAL semantics with any
      contract-respecting call handler AND any oracle that respects the
      declared axiom frames and is register-local, and its caller duty),
      `StartGut` and `StartExklusiv` (the boot assignment);
    * (b) hardware: `GutO O` (axiom answers inside their declared frames)
      and `RegLokal O` (a register answers from its device's carriers
      `D.rtraeger r`, the visibility answer of `awaits g` from `g`);
    * (c) decidable program facts over a complete member list `fs`: the
      widened fragment (`programmImFragmentG`: every form; an indirect call
      only where every function of its signature has its contract carriers
      in the caller's widened footprint) and the widened footprint check
      (`fussOrtGB`: every carrier of `fussOrteG` -- the footprint of
      `ziel_ort_voll` plus the device carriers of every register the body
      reads -- is guarded by a signature lock of the function or written by
      no function);
    * the declaration declares a table, a global or a lock (`e0`, as in
      `ziel_ort_voll`).

    Conclusion: `VertragAmOrtG` on EVERY machine reachable from the start
    machine. -/
theorem ziel_ort_geraet (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussOrtGB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutG P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  have hFragF : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) = true :=
    programmImFragmentG_ok P hvoll hFrag
  intro M hr
  have hI : ZielInvG P O passes M := by
    induction hr with
    | start => exact zielInvG_start hFragF sp init hStart
    | schritt M M' u hr' hs ih =>
        exact zielInvG_schritt hO hRL hvoll hFuss hK hFragF e0 sp init hex hr' hs ih
  exact fun t ev hev => hI.2 t ev hev

end Ziel
/-! ## 3. `ziel_ort_voll` on register-local oracles is a special case -/

/-- **`ziel_ort_voll` follows from `ziel_ort_geraet` for every
    register-local oracle**: with the premises of `ziel_ort_voll` and
    `RegLokal O`, the old fragment is inside the widened one, the old
    footprint check is the widened one there (no register is read), and the
    old obligation gives the new one. (`ziel_ort_voll` itself, without
    `RegLokal`, stays as it is.) -/
theorem ziel_ort_voll_lokal (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hRL : RegLokal O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentV P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGutV P passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M :=
  ziel_ort_geraet P O passes fs sp init e0 hO hRL hvoll (programmImFragmentG_of_V P fs hFrag)
    (fussOrtGB_of_V P fs hFrag hFuss) (fun f => koerperGutG_of_V (hK f)) hStart hex

/-! ## CUTS:

  What is proved: `ziel_ort_geraet` -- over the repaired G, for every
  program in the widened fragment (every form of `ziel_ort_voll`'s fragment
  plus `let x = R`, `let x = R else …` and `awaits`; register writes,
  `transition` and `exchange` were already in), whose widened footprint
  check passes, whose bodies satisfy `KoerperGutG`, whose start assignment
  is exclusive and meets `StartGut`, with an oracle satisfying `GutO` and
  `RegLokal`, every reachable machine satisfies `VertragAmOrtG`. Every
  premise is used: `GutO` (rely, held locks, axiom frames), `RegLokal` (the
  register and visibility steps of `akteurG`; the record oracle is local
  for the user obligation in `popG_ens`/`pushG_req`), `hvoll` and
  `programmImFragmentG` (every residue in the widened fragment, every
  register read with its device carriers in the footprint), `fussOrtGB`
  (`andereG`: the device carriers are protected like every footprint
  carrier), `KoerperGutG`, `StartGut`, `StartExklusiv`, `e0`. On
  register-local oracles `ziel_ort_voll` is a special case
  (`ziel_ort_voll_lokal`). The witness with all premises jointly is
  `ziel_ort_geraet_zeuge` (`ZielOrtGeraetZeuge.lean`).

  What is NOT covered:

  - Device-driven change as a machine step of its own. A device that
    changes its state by itself is modelled by a declared write to its
    carriers (an axiom whose frame names them, recorded like every axiom
    answer); G has no asynchronous device step (`GeraetSchreibt` in
    `Semantik.lean` is a shape beside the run), so a register whose answer
    changes between two reads with NO write to its carriers violates
    `RegLokal` and is outside the theorem.
  - The device carriers must be protected like every footprint carrier: a
    lock the reader holds BY SIGNATURE, or no writer at all
    (`fussOrtGB`). A reader that takes the device lock in a `locks` block
    only is not covered (the same restriction as `fussOrtB`).
  - `RegLokal`'s visibility half is minimal (the awaited global only); an
    answer that depends on the payload globals of `publishes` is outside it.
  - `ziel_ort_voll` for NON-local oracles is not derived from
    `ziel_ort_geraet` (it stays as proved); the other cuts of
    `ziel_ort_voll` (no-event declarations, stuck states, the converse
    adequacy) carry over unchanged.
-/

#print axioms Gabbro.Grammatik.akteurG
#print axioms Gabbro.Grammatik.andereG
#print axioms Gabbro.Grammatik.ziel_ort_geraet
#print axioms Gabbro.Grammatik.ziel_ort_voll_lokal


end Gabbro.Grammatik
