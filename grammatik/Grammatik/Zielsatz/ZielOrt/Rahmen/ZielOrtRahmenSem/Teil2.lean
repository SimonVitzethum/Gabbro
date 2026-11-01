module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Maschine
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **CALLEES RESPECT THEIR FRAMES ON G (`rufG_rahmen`).** On every machine
    reachable from the start, for every thread and every suspended frame
    `F` on its stack waiting for a callee `g` entered at world `s0`: `g`'s
    declared writes are inside `F`'s, and the live memory agrees with `s0`
    on every footprint carrier of `F` that `g` does not declare as written
    -- whatever `g`, its callees and all other threads did since. Premises:
    `GutO` (the oracle frame, the held locks), the footprint check
    `fussOrtGB` over a complete member list, and the exclusive start. -/
theorem rufG_rahmen (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    RahmenInv P M := by
  induction hr with
  | start =>
      intro t
      show RahmenStapel P sp _ ((RufStartG P sp init).faeden t).stapel
      have e : ((RufStartG P sp init).faeden t).stapel = [] := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).stapel = []
        cases init t
        rfl
      rw [e]
      trivial
  | schritt M M' u hr' hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact rahmenStapel_akteur hO hs (ih t)
      · exact rahmenStapel_andere hO hvoll hFuss sp init hex hr' hs t htu (ih t)

end Maschine

/-! ## CUTS:

  What is proved: the handler class `RespektiertRahmen` (contracts plus the
  callee's declared frame and held locks on every normal answer), the
  obligation `KoerperGutR` over it, its weakening from `KoerperGutG` and
  `KoerperGutV` (`koerperGutR_of_G`, `koerperGutR_of_V`), the record forms
  (`RahmenV`, `VertraegeOkR`, `rufAusV_rahmen`), the recorded answer world
  `rahmenWelt` (in the callee's frame by construction, held locks kept by
  the `neutral` trace piece, agreeing with the machine on the caller's
  footprint when the machine kept it outside the callee's writes), and the
  machine fact `rufG_rahmen`: every suspended frame's footprint carriers
  change during its pending call only where the callee declares a write.

  What is NOT here: the goal theorem over `KoerperGutR`
  (`ZielOrtRahmen.lean`). The frame is a condition on NORMAL answers only;
  a reason answer (`grund`) keeps no frame in the handler class (the
  machine fact `rufG_rahmen` holds for it too, the replay records it with
  the same answer world). The frame is stated for the caller's footprint
  on the machine: carriers outside every suspended frame's footprint may be
  written by other threads during a call, and the sequential answer world
  takes them from the key world -- the caller's reasoning never reads them.
-/

#print axioms Gabbro.Grammatik.koerperGutR_of_G
#print axioms Gabbro.Grammatik.koerperGutR_of_V
#print axioms Gabbro.Grammatik.rufAusV_rahmen
#print axioms Gabbro.Grammatik.rahmenWelt_gleichAuf
#print axioms Gabbro.Grammatik.rahmenStapel_akteur
#print axioms Gabbro.Grammatik.rufG_rahmen

end Gabbro.Grammatik
