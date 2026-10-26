/-
  File:      stage0/Stage0/Schnell/Normal.lean
  Subject:   **The normal form the fast machine keeps.** `normal w M`: the memory of `M`; every frame without its
             entry world (`w` instead, it only feeds the logs); every thread's trace compact; no call log, no run log.
             The fast machine IS `normal w M` for the machine `M` it stands for (the equation is a proof, erased at
             run time). The steps of the thread machine read nothing that the normal form drops
             (`Schnell/Sim*.lean`).
-/
import Stage0.Schnell.BlattPaar

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- A frame without its entry world. -/
def _root_.Gabbro.Grammatik.RufRahmenG.ohne (w : World D) (r : RufRahmenG D) : RufRahmenG D := ⟨r.f, r.rho, w, r.rest⟩

/-- A thread in normal form: frames without entry worlds, the compact trace, no call log. -/
def fadenNormal (w : World D) (z : RufFadenG D) : RufFadenG D :=
  ⟨z.stapel.map (RufRahmenG.ohne w), z.kopf.ohne w, kompakt z.spur, []⟩

/-- **The normal form of a machine.** -/
def normal (w : World D) (M : RufMaschineG D) : RufMaschineG D :=
  ⟨M.speicher, fun g => fadenNormal w (M.faeden g), [], w⟩

variable {w : World D}

theorem _root_.Gabbro.Grammatik.RufRahmenG.ohne_ohne (r : RufRahmenG D) : (r.ohne w).ohne w = r.ohne w := rfl

theorem kompakt_kompakt (s : List (Ereignis D)) : kompakt (kompakt s) = kompakt s := by
  simp only [kompakt, offen_nimmtListe]

theorem kompakt_kongr {s s' : List (Ereignis D)} (h : offen s = offen s') : kompakt s = kompakt s' := by
  simp only [kompakt, h]

theorem fadenNormal_fadenNormal (z : RufFadenG D) : fadenNormal w (fadenNormal w z) = fadenNormal w z := by
  simp only [fadenNormal, List.map_map, kompakt_kompakt]
  rfl

/-- Two threads with the same normal form: the same frames up to entry worlds, the same open locks. -/
theorem fadenNormal_eq {z z' : RufFadenG D} (hs : z.stapel.map (RufRahmenG.ohne w) = z'.stapel.map (RufRahmenG.ohne w))
    (hk : z.kopf.ohne w = z'.kopf.ohne w) (ho : offen z.spur = offen z'.spur) :
    fadenNormal w z = fadenNormal w z' := by
  simp only [fadenNormal, hs, hk, kompakt_kongr ho]

theorem offen_normal (M : RufMaschineG D) (g : Faden) :
    offen ((normal w M).faeden g).spur = offen (M.faeden g).spur := offen_kompakt _

theorem fremdZahl_normal (M : RufMaschineG D) (g : Faden) : fremdZahl ((normal w M).faeden g).spur = 0 :=
  fremdZahl_kompakt _

theorem rufFreiG_normal {M : RufMaschineG D} {f : Faden} {L : D.Lock} :
    RufFreiG (normal w M) f L ↔ RufFreiG M f L := by
  simp only [RufFreiG, offen_normal]

/-- The world thread `g` of the normal form sees, paired with the machine's: one memory, the compact trace. -/
theorem paar_normal (M : RufMaschineG D) (g : Faden) :
    Paar (kompakt (M.faeden g).spur) (M.faeden g).spur ((normal w M).weltVon g) (M.weltVon g) :=
  Paar.start M.speicher

theorem schwanz_normal (M : RufMaschineG D) (g : Faden) :
    Schwanz (fremdZahl (M.faeden g).spur) (kompakt (M.faeden g).spur) (M.faeden g).spur :=
  ⟨offen_kompakt _, by rw [fremdZahl_kompakt]; omega⟩

/-- **The normal form after a step of thread `f`**: the memories agree, and the new thread `f` has the same normal
    form on both sides; the other threads are untouched. -/
theorem normal_schritt {M : RufMaschineG D} {f : Faden} {S S' : Speicher D} {zF zM : RufFadenG D}
    {l l' : Lauf D} {st st' : World D} (hS : S = S') (hz : fadenNormal w zF = fadenNormal w zM) :
    normal w ⟨S, rufUpdateG (normal w M).faeden f zF, l, st⟩ = normal w ⟨S', rufUpdateG M.faeden f zM, l', st'⟩ := by
  subst hS
  simp only [normal, RufMaschineG.mk.injEq, true_and, and_true]
  funext g
  by_cases hg : g = f
  · subst hg
    simp only [rufUpdateG_self, hz]
  · simp only [rufUpdateG_noteq _ _ _ hg, fadenNormal_fadenNormal]

/-- New events in front of paired tails: the open locks agree. -/
theorem offen_neu_kompakt (neu s : List (Ereignis D)) : offen (neu ++ kompakt s) = offen (neu ++ s) :=
  offen_append_kongr (offen_kompakt s) neu

/-- The events a paired world added are the events the step names. -/
theorem Paar.neu_eq {sF sM : List (Ereignis D)} {σF σM : World D} (h : Paar sF sM σF σM) {neu : List (Ereignis D)}
    (hF : σF.spur = neu ++ sF) : σM.spur = neu ++ sM := by
  obtain ⟨n, h1, h2⟩ := h.neu
  rw [hF] at h1
  rw [h2, List.append_cancel_right h1]

theorem stapel_normal (M : RufMaschineG D) (f : Faden) :
    ((normal w M).faeden f).stapel.map (RufRahmenG.ohne w) = (M.faeden f).stapel.map (RufRahmenG.ohne w) := by
  simp only [normal, fadenNormal, List.map_map]
  rfl

/-- **The end of every simulation lemma**: after a step of thread `f` on both sides -- one memory, the same frames up
    to entry worlds, the same new events in front of the compact and of the machine's trace -- the normal forms agree
    and the machine's thread has asked exactly the questions the fast one counts. -/
theorem sim_schluss {M : RufMaschineG D} {f : Faden} {S S' : Speicher D} {zF zM : RufFadenG D}
    {l l' : Lauf D} {st st' : World D} (hS : S = S')
    (hst : zF.stapel.map (RufRahmenG.ohne w) = zM.stapel.map (RufRahmenG.ohne w))
    (hk : zF.kopf.ohne w = zM.kopf.ohne w) {neu : List (Ereignis D)}
    (hF : zF.spur = neu ++ kompakt (M.faeden f).spur) (hM : zM.spur = neu ++ (M.faeden f).spur) :
    normal w ⟨S, rufUpdateG (normal w M).faeden f zF, l, st⟩ = normal w ⟨S', rufUpdateG M.faeden f zM, l', st'⟩ ∧
      fremdZahl ((⟨S', rufUpdateG M.faeden f zM, l', st'⟩ : RufMaschineG D).faeden f).spur =
        fremdZahl ((⟨S, rufUpdateG (normal w M).faeden f zF, l, st⟩ : RufMaschineG D).faeden f).spur +
          fremdZahl (M.faeden f).spur := by
  refine ⟨normal_schritt hS (fadenNormal_eq hst hk ?_), ?_⟩
  · rw [hF, hM]
    exact offen_neu_kompakt neu _
  · simp only [rufUpdateG_self, hF, hM, fremdZahl_append, fremdZahl_kompakt]
    omega

theorem Paar.neu_eq' {sF sM : List (Ereignis D)} {σF σM : World D} {neu : List (Ereignis D)}
    (hF : σF.spur = neu ++ sF) (h : Paar sF sM σF σM) : σM.spur = neu ++ sM := h.neu_eq hF

end Gabbro.Stage0
