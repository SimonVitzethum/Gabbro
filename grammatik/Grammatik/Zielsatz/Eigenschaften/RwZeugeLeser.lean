/-
  File:      Grammatik/Zielsatz/Eigenschaften/RwZeugeLeser.lean
  Subject:   PLANTED DEFECT of the reader/writer lock layer: A READER THAT WRITES a carrier its lock
             guards. The premise `LeserLos` of `rennfrei_rw` (`RwOrdnung.lean`) is load-bearing.

  The fixture is `Proben/InvZeuge.lean`: one lock `()` guarding the table `konto`; `haupt` holds the
  lock by signature and calls `setze`, which writes `konto[0] := 5`. Two threads (0 and 1) both run
  `haupt`, so both start HOLDING the lock -- legal in the layer only if both are readers
  (`lAll`: every thread is a reader). Thread 0 writes `konto[0]`, then thread 1 writes it: two
  conflicting accesses to one guarded carrier by two readers that hold the lock at the same time, and
  no release in between.

  * `leser_schreibt_rennt`: the run is a layer run, the start meets `RwExkl` and `SpurInv`, both steps
    access the carrier, the first writes it, the carrier is guarded -- and the two accesses are NOT
    ordered through the lock (`¬ GeordnetRw`). By `rennfrei_rw` that is only possible if the discipline
    fails: `¬ LeserLos`. The theorem states it, derived from `rennfrei_rw`, not assumed.
-/
import Grammatik.Proben.InvZeuge
import Grammatik.Zielsatz.Eigenschaften.RwInv

namespace Gabbro.Grammatik.Zielsatz.RwFix2

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- Threads 0 and 1 run `haupt` (each holds the lock by signature), every other thread `nichts`. -/
def init2 : Faden → Σ f : ivD.Fn, Env ivD (ivD.params f) :=
  fun t => if t ≤ 1 then ⟨ivHaupt, .nil⟩ else ⟨ivNichts, .nil⟩

/-- Every thread is a reader of every lock. -/
def lAll : Lese ivD := fun _ _ => True

abbrev M0i : RufMaschineG ivD := RufStartG ivPgut ivSp init2

theorem m0_faden0 : M0i.faeden 0 =
    ⟨[], ⟨ivHaupt, .nil, ivSp.welt [], ⟨false, [], ivL, .nil, .ende ivRumpfHaupt⟩⟩,
      startSpur ivHaupt, [RufEreignisF.eintritt ivHaupt .nil (ivSp.welt [])]⟩ := rfl

theorem m0_faden1 : M0i.faeden 1 =
    ⟨[], ⟨ivHaupt, .nil, ivSp.welt [], ⟨false, [], ivL, .nil, .ende ivRumpfHaupt⟩⟩,
      startSpur ivHaupt, [RufEreignisF.eintritt ivHaupt .nil (ivSp.welt [])]⟩ := rfl

theorem exkl_i : RwExkl lAll M0i := fun _ _ _ _ _ _ => ⟨trivial, trivial⟩

/-- A recorded write event on `t` in the new trace makes the step access (and write) `t`. -/
theorem zugriff_aus_spur {M M' : RufMaschineG ivD} {f : Faden} {Λ : List (Res ivD)}
    {hh : List ivD.Lock}
    (h : (M'.faeden f).spur = [Ereignis.zugriff () true Λ hh] ++ (M.faeden f).spur) :
    ((Sum.inl () : ivD.Tab ⊕ ivD.Glob), true) ∈ zugriffe M M' f := by
  show _ ∈ (ereignisse M M' f).filterMap zugriffVon
  rw [ereignisse_eq h]
  simp [zugriffVon]

/-- One thread's two steps: `haupt` calls `setze`, `setze` writes `konto[0] := 5`, with the write
    event recorded. -/
theorem zwei_schritte {M : RufMaschineG ivD} {f : Faden}
    (hz : M.faeden f = ⟨[], ⟨ivHaupt, .nil, ivSp.welt [], ⟨false, [], ivL, .nil, .ende ivRumpfHaupt⟩⟩,
      startSpur ivHaupt, [RufEreignisF.eintritt ivHaupt .nil (ivSp.welt [])]⟩) :
    ∃ M1 M2 : RufMaschineG ivD, RufSchrittG ivPgut ivO 0 M f M1 ∧ RufSchrittG ivPgut ivO 0 M1 f M2 ∧
      ((Sum.inl () : ivD.Tab ⊕ ivD.Glob), true) ∈ zugriffe M1 M2 f ∧
      (∀ g, g ≠ f → M1.faeden g = M.faeden g) ∧ (∀ g, g ≠ f → M2.faeden g = M.faeden g) := by
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := ivPgut) (O := ivO) (passes := 0) hz ivSetze .nil ivHp rfl
    ivHauptRest .nil rfl (ivHeld ivOffen0)
  have hoff1 : offen (M1.faeden f).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]
    show offen (M.faeden f).spur = [()]
    rw [hz]
    exact ivOffen0
  have e1 := hZ1.1
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := ivPgut) (O := ivO) (passes := 0) e1 ivS0
    (.cons ivS1 ivRetS) .nil rfl rfl (by rw [← e1]; exact ivHeld hoff1) _ _ rfl
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  refine ⟨M1, M2, s1, s2, ?_, fun g hg => rufSchrittG_fremd s1 g hg,
    fun g hg => (rufSchrittG_fremd s2 g hg).trans (rufSchrittG_fremd s1 g hg)⟩
  refine zugriff_aus_spur (Λ := ivL) (hh := (M1.faeden f).spur |> offen) ?_
  rw [hZ2.spur]
  rfl

/-- **A READER THAT WRITES: the two accesses are unordered, and so the discipline fails.** Two readers
    that both hold the lock write `konto[0]` one after the other; nothing releases the lock between
    them. `rennfrei_rw` would order them if `LeserLos` held, so it does not hold. -/
theorem leser_schreibt_rennt : ∃ (ms : Nat → RufMaschineG ivD) (fs : Nat → Faden),
    RwLauf ivPgut ivO 0 lAll M0i ms fs 4 ∧ fs 1 ≠ fs 3 ∧
    ZugriffG (ms 1) (ms 2) (fs 1) (Sum.inl ()) ∧ ZugriffG (ms 3) (ms 4) (fs 3) (Sum.inl ()) ∧
    SchreibG (ms 1) (ms 2) (fs 1) (Sum.inl ()) ∧ ¬ GeordnetRw ms fs () 1 3 ∧
    ¬ LeserLos lAll ms fs 4 := by
  obtain ⟨A1, A2, a1, a2, ha, fa1, fa2⟩ := zwei_schritte (M := M0i) (f := 0) m0_faden0
  have hb : A2.faeden 1 = M0i.faeden 1 := fa2 1 (by decide)
  obtain ⟨B1, B2, b1, b2, hb', fb1, fb2⟩ := zwei_schritte (M := A2) (f := 1) (hb.trans m0_faden1)
  obtain ⟨ms1, fs1, l1, m1, _⟩ := rwLauf_schritt
    (rwLauf_nil (lese := lAll) (P := ivPgut) (O := ivO) (passes := 0) M0i) rfl (rwSchritt_of_G a1)
  obtain ⟨ms2, fs2, l2, m2, k2, n2, p2⟩ := rwLauf_schritt l1 m1 (rwSchritt_of_G a2)
  obtain ⟨ms3, fs3, l3, m3, k3, n3, p3⟩ := rwLauf_schritt l2 m2 (rwSchritt_of_G b1)
  obtain ⟨ms4, fs4, l4, m4, k4, n4, p4⟩ := rwLauf_schritt l3 m3 (rwSchritt_of_G b2)
  have hm1 : ms4 1 = A1 := by rw [k4 1 (by omega), k3 1 (by omega), k2 1 (by omega), m1]
  have hm2 : ms4 2 = A2 := by rw [k4 2 (by omega), k3 2 (by omega), m2]
  have hm3 : ms4 3 = B1 := by rw [k4 3 (by omega), m3]
  have hf1 : fs4 1 = 0 := by rw [p4 1 (by omega), p3 1 (by omega), n2]
  have hf3 : fs4 3 = 1 := n4
  have hzi : ZugriffG (ms4 1) (ms4 2) (fs4 1) (Sum.inl ()) := by
    rw [hm1, hm2, hf1]
    exact Or.inl ⟨true, ha⟩
  have hzj : ZugriffG (ms4 3) (ms4 4) (fs4 3) (Sum.inl ()) := by
    rw [hm3, m4, hf3]
    exact Or.inl ⟨true, hb'⟩
  have hwi : SchreibG (ms4 1) (ms4 2) (fs4 1) (Sum.inl ()) := by
    rw [hm1, hm2, hf1]
    exact Or.inl ha
  have hfg : fs4 1 ≠ fs4 3 := by rw [hf1, hf3]; decide
  have hno : ¬ GeordnetRw ms4 fs4 () 1 3 := by
    rintro ⟨r, a, h1, h2, h3, _⟩
    omega
  refine ⟨ms4, fs4, l4, hfg, hzi, hzj, hwi, hno, fun hd => hno ?_⟩
  exact rennfrei_rw ivO_gut l4 exkl_i (spurInv_start ivPgut ivSp init2) hd 1 3 (by omega)
    (by omega) hfg (Sum.inl ()) () (List.mem_singleton.mpr rfl) hzi hzj (Or.inl hwi)

end Gabbro.Grammatik.Zielsatz.RwFix2

#print axioms Gabbro.Grammatik.Zielsatz.RwFix2.leser_schreibt_rennt
