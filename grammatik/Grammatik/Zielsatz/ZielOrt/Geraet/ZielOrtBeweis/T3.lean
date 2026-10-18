/- Part 3 of 3 of `ZielOrtBeweis` (split by instrumente/teile/lean-teilen.py; the umbrella `ZielOrtBeweis.lean` imports all parts). -/
import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 6. The other threads, the start, the theorem -/

section Ziel

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The rely for the replay.** A step of thread `u` leaves the footprint
    of every live head frame of another thread `t` alone: a footprint
    carrier is guarded by a signature lock of the head function, which `t`
    holds (`rufG_haelt_signatur`) and `u` therefore does not (`exklusivG`),
    or no function writes it (`FussOrtOk`). -/
theorem andere_ok (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (hF : FadenOk P O passes (M.faeden t) (M.weltVon t)) :
    FadenOk P O passes (M'.faeden t) (M'.weltVon t) := by
  have e : M'.faeden t = M.faeden t := rufSchrittG_fremd hs t htu
  have hW : M'.weltVon t = M'.speicher.welt (M.faeden t).spur := by
    unfold RufMaschineG.weltVon; rw [e]
  rw [hW, e]
  refine fadenOk_speicher hF (fun c hc => ?_)
  rcases fussOrtB_ok P fs hvoll hFuss (M.faeden t).kopf.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t _ List.mem_cons_self L hL
    exact relyG hO sp init hex hr hs t (fun h => htu h.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

/-- **The start machine is replayed.** Every thread's start frame: empty
    record, sequential world = entry world, `requires` by `StartGut`. -/
theorem zielInv_start (hFrag : ∀ f, (P.rumpf f).kOk = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hStart : StartGut P sp init) :
    ZielInv P O passes (RufStartG P sp init) := by
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
    refine ⟨⟨[], sp.welt [], hStart t, funk_nil, vertraegeOk_nil P, kurzH_nil _,
      GleichAuf.vonSpeicher rfl, ⟨hFrag _, fuss_rumpf P _⟩, fun R _ => ZErg.gleich_refl _⟩, trivial⟩
  · rw [hz t]
    exact logOk_eintritt (fun _ h => absurd h List.not_mem_nil) (hStart t)

/-- One step keeps the global invariant. -/
theorem zielInv_schritt (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtB P fs = true) (hK : ∀ f, KoerperGut P O passes f)
    (hFrag : ∀ f, (P.rumpf f).kOk = true) (e0 : Ereignis D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (hI : ZielInv P O passes M) :
    ZielInv P O passes M' := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · by_cases htu : t = u
    · subst htu
      exact (akteur hK hFrag e0 hs (hI.1 t) (hI.2 t)).1
    · exact andere_ok hO hvoll hFuss sp init hex hr hs t htu (hI.1 t)
  · by_cases htu : t = u
    · subst htu
      exact (akteur hK hFrag e0 hs (hI.1 t) (hI.2 t)).2
    · rw [rufSchrittG_fremd hs t htu]
      exact hI.2 t

/-- **ZIEL AM ORT -- contracts hold at their place on every machine of the
    repaired concurrent call machine G.**

    Premises, by class:
    * (a) user obligations: `KoerperGut P O passes f` for every function
      (the body's Hoare triple over the SEQUENTIAL semantics with any
      contract-respecting handler, and its caller duty), `StartGut` (the
      start functions' `requires` at the start memory) and `StartExklusiv`
      (no two threads start in functions holding a common lock -- the boot
      assignment);
    * (b) hardware: `GutO O`;
    * (c) decidable program facts over a complete member list `fs`: the
      fragment (`programmImFragment`) and the footprint check (`fussOrtB`:
      every carrier a function reads, or its contract or a direct callee's
      contract mentions, is guarded by a lock the function holds by
      signature, or written by no function);
    * the declaration declares a table, a global or a lock (`e0`: an event
      exists; it gives each recorded call answer a fresh trace position).

    Conclusion: on EVERY machine reachable from the start machine, at every
    `eintritt` of every thread log the callee's `requires` holds with the
    actual parameters at the actual entry world, and at every `rueck` the
    `ensures` holds with the actual entry world, return world, parameters
    and result. -/
theorem ziel_ort (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (e0 : Ereignis D)
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragment P fs = true) (hFuss : fussOrtB P fs = true)
    (hK : ∀ f : D.Fn, KoerperGut P O passes f) (hStart : StartGut P sp init)
    (hex : StartExklusiv init) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      VertragAmOrtG P M := by
  have hFragF : ∀ f, (P.rumpf f).kOk = true :=
    fun f => (List.all_eq_true.mp hFrag) f (hvoll f)
  intro M hr
  have hI : ZielInv P O passes M := by
    induction hr with
    | start => exact zielInv_start hFragF sp init hStart
    | schritt M M' u hr' hs ih =>
        exact zielInv_schritt hO hvoll hFuss hK hFragF e0 sp init hex hr' hs ih
  exact fun t ev hev => hI.2 t ev hev

end Ziel
/-! ## CUTS:

  What is proved: `ziel_ort` -- over the repaired G, for every program in
  the fragment whose footprint check passes, whose bodies satisfy
  `KoerperGut`, whose start assignment is exclusive and meets `StartGut`,
  with an oracle satisfying `GutO`, every reachable machine satisfies
  `VertragAmOrtG`. Premises and their use: `GutO` (rely, held locks),
  `hvoll` (member list complete: fragment and footprint per function),
  `programmImFragment` (every residue in the fragment: `okZ`),
  `fussOrtB` (the rely covers the footprint: `andere_ok`), `KoerperGut`
  (the return leg `pop_ens` and the call leg `push_req`), `StartGut`
  (`zielInv_start`), `StartExklusiv` (`exklusivG` in the rely), `e0`
  (fresh trace positions for the record: `pop_kopf`).

  What is NOT covered:

  - Declarations without any table, global and lock (no `e0`). There the
    world has no memory and a single trace, the record's keys collapse to
    (callee, parameters), and a replay needs that two returns of a callee
    with equal parameters return equal values -- a determinism lemma for
    G that is not proved here. (Closed for the lock-invariant replay that
    the goal uses, 2026-09-14: `Begruendet`, `begruendet_eindeutig`,
    SperreBeweis.lean §0b -- the determinism obtained from the replay
    itself; this older replay keeps `e0`.)
  - Bodies outside the fragment `kOk` (loops, `leave`/`next`, the error
    channel, indirect calls, axioms, the oracle forms).
  - `schreiberHaeltB` (the static writer discipline of `ZielOrt.lean`) is
    NOT a premise: the repaired G enforces the writer discipline
    dynamically (every write carries its guards in the static holdings and
    demands `HeldGenau`), and requiring it statically would make every
    guarded carrier that is written at all the property of ONE thread
    forever (a writer's start function would hold the guard by signature).
-/

#print axioms Gabbro.Grammatik.pop_ens
#print axioms Gabbro.Grammatik.pop_kopf
#print axioms Gabbro.Grammatik.push_req
#print axioms Gabbro.Grammatik.push_ok
#print axioms Gabbro.Grammatik.akteur
#print axioms Gabbro.Grammatik.andere_ok
#print axioms Gabbro.Grammatik.ziel_ort


end Gabbro.Grammatik
