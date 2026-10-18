/- Part 4 of 4 of `Schlusssatz124` (split by instrumente/teile/lean-teilen.py; the umbrella `Schlusssatz124.lean` imports all parts). -/
import Grammatik.Korrespondenz.Kette.Schlusssatz124.T3

namespace Gabbro.Grammatik
namespace K124

open Zielsatz

section Satz

/-- The G start for a root assignment `w` of the runtime: `hauptA` where it
    started root 2, `hauptB` where root 3, the idle root elsewhere. -/
def kInit (w : Faden → Option Nat) : Faden → Σ f : DR.Fn, Env DR (DR.params f) := fun t =>
  match w t with
  | some 2 => ⟨some kHauptA, .nil⟩
  | some 3 => ⟨some kHauptB, .nil⟩
  | _ => ⟨none, .nil⟩

/-- The start machine of G for `w`, from the declared initial memory. -/
def M0 (w : Faden → Option Nat) : RufMaschineG DR := RufStartG PR (speicherR kSp) (kInit w)

/-- The root assignments `FadenStartC` admits: declared roots only, each once. -/
def Wurzeln (w : Faden → Option Nat) : Prop :=
  (∀ t f, w t = some f → f ∈ [2, 3]) ∧ ∀ t u f, w t = some f → w u = some f → t = u

theorem kInit_2 {w : Faden → Option Nat} {t : Faden} (h : w t = some 2) :
    kInit w t = ⟨some kHauptA, .nil⟩ := by
  unfold kInit; rw [h]; rfl

theorem kInit_3 {w : Faden → Option Nat} {t : Faden} (h : w t = some 3) :
    kInit w t = ⟨some kHauptB, .nil⟩ := by
  unfold kInit; rw [h]; rfl

theorem kInit_sonst {w : Faden → Option Nat} {t : Faden} (h2 : w t ≠ some 2)
    (h3 : w t ≠ some 3) : kInit w t = ⟨none, .nil⟩ := by
  unfold kInit
  split
  · rename_i h; exact absurd h h2
  · rename_i h; exact absurd h h3
  · rfl

theorem fadenRel_sonst {o : Option Nat} {c : CFaden} {z : RufFadenG DR} (h2 : o ≠ some 2)
    (h3 : o ≠ some 3) (h : FadenRel o c z) : c = .aus := by
  unfold FadenRel at h
  split at h
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact h

/-- **The runtime premise of the C (`FadenStartC`) gives the runtime premise
    (d) of the goal theorem** for the corresponding G start. -/
theorem laufzeit_w (w : Faden → Option Nat) (hw : Wurzeln w) :
    Laufzeit kE (speicherR kSp) (kInit w) where
  lader := rfl
  start t := by
    by_cases h2 : w t = some 2
    · exact Or.inr ⟨⟨kHauptA, .nil⟩, List.mem_cons_self, by rw [kInit_2 h2]; rfl⟩
    · by_cases h3 : w t = some 3
      · exact Or.inr ⟨⟨kHauptB, .nil⟩, List.mem_cons_of_mem _ List.mem_cons_self,
          by rw [kInit_3 h3]; rfl⟩
      · exact Or.inl (kInit_sonst h2 h3)
  einmal t u htu he := by
    have fall : ∀ v, (w v = some 2 ∧ (kInit w v).1 = some kHauptA) ∨
        (w v = some 3 ∧ (kInit w v).1 = some kHauptB) ∨ (kInit w v).1 = none := by
      intro v
      by_cases h2 : w v = some 2
      · exact Or.inl ⟨h2, by rw [kInit_2 h2]⟩
      · by_cases h3 : w v = some 3
        · exact Or.inr (Or.inl ⟨h3, by rw [kInit_3 h3]⟩)
        · exact Or.inr (Or.inr (by rw [kInit_sonst h2 h3]))
    rcases fall t with ⟨ht, et⟩ | ⟨ht, et⟩ | et
    · rcases fall u with ⟨hu, eu⟩ | ⟨hu, eu⟩ | eu
      · exact absurd (hw.2 t u 2 ht hu) htu
      · rw [et, eu] at he; cases he
      · rw [et, eu] at he; cases he
    · rcases fall u with ⟨hu, eu⟩ | ⟨hu, eu⟩ | eu
      · rw [et, eu] at he; cases he
      · exact absurd (hw.2 t u 3 ht hu) htu
      · rw [et, eu] at he; cases he
    · exact Or.inl et

/-- The start trace of every start function the runtime uses holds no lock. -/
theorem start_offen (w : Faden → Option Nat) (u : Faden) :
    offen ((M0 w).faeden u).spur = [] := by
  rw [M0, start_faden]
  by_cases h2 : w u = some 2
  · rw [kInit_2 h2]; rfl
  · by_cases h3 : w u = some 3
    · rw [kInit_3 h3]; rfl
    · rw [kInit_sonst h2 h3]; rfl

/-- **The relation holds at the two starts.** -/
theorem r124_start (w : Faden → Option Nat) (hw : Wurzeln w) :
    R124 w (startC c124 w st0) (M0 w) := by
  refine ⟨⟨fun tb _ => ⟨rfl, fun k f _ _ => rfl⟩, And.intro (fun g => nomatch g) (fun _ _ => rfl)⟩, ?_, fun t => ?_⟩
  · intro L u
    show (none : Option Faden) = some u ↔ _
    constructor
    · intro h; cases h
    · rintro ⟨_, hm⟩
      rw [start_offen w u] at hm
      exact absurd hm List.not_mem_nil
  · by_cases h2 : w t = some 2
    · have e : FadenRel (w t) ((startC c124 w st0).faeden t) ((M0 w).faeden t) =
          ThreadA ((startC c124 w st0).faeden t) ((M0 w).faeden t) := by rw [h2]; rfl
      rw [e]
      refine ⟨0, startSpur (D := DR) (some kHauptA),
        [RufEreignisF.eintritt (D := DR) (some kHauptA) Env.nil ((speicherR kSp).welt [])],
        by omega, ?_, ?_, ?_⟩
      · show (match w t with
          | some f => anStart c124 f
          | none => .aus) = posA 0
        rw [h2]; rfl
      · rw [M0, start_faden, kInit_2 h2]; rfl
      · rfl
    · by_cases h3 : w t = some 3
      · have e : FadenRel (w t) ((startC c124 w st0).faeden t) ((M0 w).faeden t) =
            ThreadB ((startC c124 w st0).faeden t) ((M0 w).faeden t) := by rw [h3]; rfl
        rw [e]
        refine ⟨0, startSpur (D := DR) (some kHauptB),
          [RufEreignisF.eintritt (D := DR) (some kHauptB) Env.nil ((speicherR kSp).welt [])],
          by omega, ?_, ?_, ?_⟩
        · show (match w t with
            | some f => anStart c124 f
            | none => .aus) = posB 0
          rw [h3]; rfl
        · rw [M0, start_faden, kInit_3 h3]; rfl
        · rfl
      · have hs : (startC c124 w st0).faeden t = .aus := by
          show (match w t with
            | some f => anStart c124 f
            | none => .aus) = .aus
          rcases hwt : w t with _ | f
          · rfl
          · have := hw.1 t f hwt
            simp only [List.mem_cons, List.not_mem_nil, or_false] at this
            rcases this with rfl | rfl
            · exact absurd hwt h2
            · exact absurd hwt h3
        rcases hwt : w t with _ | f
        · show (startC c124 w st0).faeden t = .aus
          exact hs
        · have : f ≠ 2 := fun e => h2 (by rw [hwt, e])
          have : f ≠ 3 := fun e => h3 (by rw [hwt, e])
          unfold FadenRel
          split
          · rename_i h; cases h; contradiction
          · rename_i h; cases h; contradiction
          · exact hs

/-- **THE SIMULATION CERTIFICATE of `beispiele/124`**: every SC step of the
    emitted C, from every reachable related pair, is a segment of steps of the
    same thread of machine G that ends related and fits the step. -/
def sim124 (passes : Nat) (w : Faden → Option Nat) (hw : Wurzeln w) :
    SimC c124 (startC c124 w st0) kEL lnr PR OR passes (M0 w) where
  R := R124 w
  start := r124_start w hw
  schritt := fun K M t ℓ K' _ _ hR hs => by
    by_cases h2 : w t = some 2
    · exact schrittA w h2 hR hs
    · by_cases h3 : w t = some 3
      · exact schrittB w h3 hR hs
      · exact (schrittC_aus hs (fadenRel_sonst h2 h3 (hR.2.2 t))).elim

/-- The closing theorem for a GIVEN root assignment `w` of the runtime. -/
theorem schlusssatz_124_bei (passes : Nat) (w : Faden → Option Nat) (hw : Wurzeln w)
    (LP : SperrSem) (hLP : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h')
    (Echt : BeobC → Prop) (hDRF : DRFSC c124 LP (startC c124 w st0) Echt) :
    Laufzeit kE (speicherR kSp) (kInit w) ∧ RennfreiC c124 LP (startC c124 w st0) ∧
      (∀ K, ErreichbarC c124 LP (startC c124 w st0) K → ∃ M, RufErreichbarG PR OR passes (M0 w) M ∧
        R124 w K M ∧ Ziel PR kE.S.mitRuhe OR passes (M0 w) M) ∧
      ∀ b, Echt b → ∃ K M, ErreichbarC c124 LP (startC c124 w st0) K ∧ beobC K = b ∧
        RufErreichbarG PR OR passes (M0 w) M ∧ R124 w K M ∧
        Ziel PR kE.S.mitRuhe OR passes (M0 w) M := by
  have hZ : ∀ M, RufErreichbarG PR OR passes (M0 w) M → Ziel PR kE.S.mitRuhe OR passes (M0 w) M :=
    fun M hM => k124_ziel kO kO_hw passes _ _ (laufzeit_w w hw) M hM
  obtain ⟨h1, h2, h3⟩ := schluss_b (sim124 passes w hw) kE.S.mitRuhe hZ LP hLP Echt hDRF
  exact ⟨laufzeit_w w hw, h1, h2, h3⟩

/-- **THE CLOSING THEOREM, STAGE (b), for `beispiele/124`.** For every
    `forever` budget, every meaning `LP` of the runtime's lock primitive,
    every start configuration `K0` of the C and every set `Echt` of real
    observations: if the runtime creates threads only at the declared roots
    and its lock primitive meets its specification (`LaufzeitC`, the runtime
    list) and the real memory model is SC for race-free programs (`DRFSC`),
    then there is the runtime's root assignment `w` with
    1. `K0` its start, and the goal theorem's runtime premise (d) for the
       corresponding G start;
    2. the emitted C DATA-RACE FREE (under the real lock primitive) -- PROVED
       from machine G, so DRF-SC applies;
    3. every SC configuration of the C related to a reachable machine of G
       (memory by `corrW`, locks, every thread) at which the goal theorem's
       conclusion `Ziel` holds;
    4. every real observation the observation of such a configuration. -/
theorem schlusssatz_124 (passes : Nat) (LP : SperrSem) (K0 : KonfC)
    (hLZ : LaufzeitC c124 [2, 3] st0 K0 LP) (Echt : BeobC → Prop)
    (hDRF : DRFSC c124 LP K0 Echt) :
    ∃ w : Faden → Option Nat, K0 = startC c124 w st0 ∧ Laufzeit kE (speicherR kSp) (kInit w) ∧
      RennfreiC c124 LP K0 ∧
      (∀ K, ErreichbarC c124 LP K0 K → ∃ M, RufErreichbarG PR OR passes (M0 w) M ∧
        R124 w K M ∧ Ziel PR kE.S.mitRuhe OR passes (M0 w) M) ∧
      ∀ b, Echt b → ∃ K M, ErreichbarC c124 LP K0 K ∧ beobC K = b ∧
        RufErreichbarG PR OR passes (M0 w) M ∧ R124 w K M ∧
        Ziel PR kE.S.mitRuhe OR passes (M0 w) M := by
  obtain ⟨w, hK0, hwf, hwi⟩ := hLZ.faeden
  subst hK0
  exact ⟨w, rfl, schlusssatz_124_bei passes w ⟨hwf, hwi⟩ LP hLZ.sperre Echt hDRF⟩

/-! ### The conclusion, read in the C -/

/-- **The lock invariant, in the C memory**: at a related pair where the C lock
    is free, `konto_speicher.slots[0].stand == konto_speicher.slots[1].stand`
    -- the leg `sperrInv` of `Ziel` carried through the relation. -/
theorem c124_sperrinv {passes : Nat} {w : Faden → Option Nat} {K : KonfC} {M : RufMaschineG DR}
    (hR : R124 w K M) (hZ : Ziel PR kE.S.mitRuhe OR passes (M0 w) M)
    (hfrei : K.halter 0 = none) : K.st.mem (.tab 0) 0 = K.st.mem (.tab 0) 4 := by
  have hinv := hZ.sperrInv lL (fun u hu => by
    have := (hR.2.1 0 u).mpr ⟨rfl, hu⟩
    rw [hfrei] at this
    cases this)
  have hd : decide ((M.speicher.slots KTab.konto 0 ()).n = (M.speicher.slots KTab.konto 1 ()).n) =
      true := hinv
  have he := of_decide_eq_true hd
  have h0 := (hR.1.1 KTab.konto rfl).2 0 () (by decide) (by decide)
  have h1 := (hR.1.1 KTab.konto rfl).2 1 () (by decide) (by decide)
  have e0 : K.st.mem (.tab 0) 0 = .int (M.speicher.slots KTab.konto 0 ()).n := h0
  have e1 : K.st.mem (.tab 0) 4 = .int (M.speicher.slots KTab.konto 1 ()).n := h1
  rw [e0, e1, he]

/-- **`hauptA`'s `ensures`, in the C memory**: once the C thread that runs
    `hauptA` has returned, `privA_speicher.slots[0].stand == 7` -- the leg
    `startEnde` of `Ziel` carried through the relation (the thread's G root
    stands at its `return`, and `privA` is written by no other thread). -/
theorem c124_ende {passes : Nat} {w : Faden → Option Nat} {K : KonfC} {M : RufMaschineG DR}
    (hR : R124 w K M) (hZ : Ziel PR kE.S.mitRuhe OR passes (M0 w) M) {t : Faden}
    (hwt : w t = some 2) (haus : K.faeden t = .aus) : K.st.mem (.tab 1) 0 = .int 7 := by
  have hA : ThreadA (K.faeden t) (M.faeden t) := by
    have := hR.2.2 t; rw [hwt] at this; exact this
  obtain ⟨i, sp, log, hi, hc, hz, _⟩ := hA
  have hi12 : i = 12 := by
    rw [haus] at hc
    match i, hi, hc with
    | 12, _, _ => rfl
  subst hi12
  have hSE := hZ.startEnde t
  rw [hz] at hSE
  have hE := (hSE rfl false [] [] .nil (.ende (ruEnd (V := vertragVon kD kHauptA) (l := false)
    (Γ := []) (Λ := []) (.ret .empty List.Perm.nil))) .empty rfl ⟨List.Perm.nil, Or.inl rfl⟩).1
  have hd : decide ((M.speicher.slots KTab.privA 0 ()).n = 7) = true := hE
  have h7 : (M.speicher.slots KTab.privA 0 ()).n = 7 := of_decide_eq_true hd
  have h0 := (hR.1.1 KTab.privA rfl).2 0 () (by decide) (by decide)
  have e0 : K.st.mem (.tab 1) 0 = .int (M.speicher.slots KTab.privA 0 ()).n := h0
  rw [e0, h7]

end Satz
/-! ## 7. The conclusion on the C runs, and the witness -/

section Zeuge

/-- **The goal theorem's conclusion on every SC run of the emitted C**, two
    legs read in C memory: on every reachable configuration, a free lock
    means `konto[0] == konto[1]` in the C memory (`sperrInv`), and a returned
    `hauptA` thread means `privA[0] == 7` there (`startEnde`). -/
theorem schlusssatz_124_c (passes : Nat) (w : Faden → Option Nat) (hw : Wurzeln w)
    (LP : SperrSem) (hLP : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h') (K : KonfC)
    (hK : ErreichbarC c124 LP (startC c124 w st0) K) :
    (K.halter 0 = none → K.st.mem (.tab 0) 0 = K.st.mem (.tab 0) 4) ∧
    (∀ t, w t = some 2 → K.faeden t = .aus → K.st.mem (.tab 1) 0 = .int 7) := by
  obtain ⟨M, hM, hR⟩ := sim_erreichbar (sim124 passes w hw) (erreichbarC_mono hLP hK)
  have hZ := k124_ziel kO kO_hw passes _ _ (laufzeit_w w hw) M hM
  exact ⟨c124_sperrinv hR hZ, fun t hwt ha => c124_ende hR hZ hwt ha⟩

/-- The runtime's start of the witness: `hauptA` on thread 0, `hauptB` on
    thread 1, no other thread. -/
def wAB : Faden → Option Nat := fun t => if t = 0 then some 2 else if t = 1 then some 3 else none

theorem wAB_eq {t f : Nat} (h : wAB t = some f) : (t = 0 ∧ f = 2) ∨ (t = 1 ∧ f = 3) := by
  unfold wAB at h
  by_cases h0 : t = 0
  · rw [if_pos h0] at h; exact Or.inl ⟨h0, (Option.some.inj h).symm⟩
  · rw [if_neg h0] at h
    by_cases h1 : t = 1
    · rw [if_pos h1] at h; exact Or.inr ⟨h1, (Option.some.inj h).symm⟩
    · rw [if_neg h1] at h; cases h

theorem wAB_wurzeln : Wurzeln wAB := by
  refine ⟨fun t f h => ?_, fun t u f ht hu => ?_⟩
  · rcases wAB_eq h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  · rcases wAB_eq ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases wAB_eq hu with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact h1.trans h3.symm
    · exact absurd (h2.symm.trans h4) (by decide)
    · exact absurd (h2.symm.trans h4) (by decide)
    · exact h1.trans h3.symm

/-- The start configuration of the witness. -/
def KAB : KonfC := startC c124 wAB st0

theorem corrW_st0 : corrW kEL ((speicherR kSp).welt []) st0 :=
  ⟨fun _ _ => ⟨rfl, fun _ _ _ _ => rfl⟩, And.intro (fun g => nomatch g) (fun _ _ => rfl)⟩

/-- **WITNESS of `schlusssatz_124`, with a CONTENDED lock** (rule 13). Every
    premise holds jointly (the specified lock primitive; thread creation at
    the two declared roots; DRF-SC with the SC observations as the real
    ones), and on a concrete SC run of the emitted C:
    * `Kb`: thread 0 (`hauptA`) holds the lock inside its critical section,
      thread 1 (`hauptB`) stands at `L_nimm();` and CANNOT step -- it is
      blocked on the lock the other thread holds;
    * `Kd`: thread 0 has released, and thread 1 has taken the lock;
    * `Kf`: both threads have returned; the lock is free; the C memory has
      `konto[0] == konto[1]` and `privA[0] == 7` -- both BY THE THEOREM, read
      in the C through the relation (`schlusssatz_124_c`) -- and the memory
      moved (`privA[0]` was 0 at the start);
    and the C program is data-race free, by the theorem. -/
theorem schlusssatz_124_zeuge :
    LaufzeitC c124 [2, 3] st0 KAB sperrAbstrakt ∧
    DRFSC c124 sperrAbstrakt KAB (fun b => ∃ K, ErreichbarC c124 sperrAbstrakt KAB K ∧ beobC K = b) ∧
    RennfreiC c124 sperrAbstrakt KAB ∧
    ∃ Kb Kd Kf : KonfC,
      ErreichbarC c124 sperrAbstrakt KAB Kb ∧ Kb.halter 0 = some 0 ∧
        Kb.faeden 1 = .an [cNimm, cRestB2] ρ0 ∧
        (∀ ℓ K', ¬ SchrittC c124 sperrAbstrakt Kb 1 ℓ K') ∧
      ErreichbarC c124 sperrAbstrakt KAB Kd ∧ Kd.halter 0 = some 1 ∧
      ErreichbarC c124 sperrAbstrakt KAB Kf ∧ Kf.faeden 0 = .aus ∧ Kf.faeden 1 = .aus ∧
        Kf.halter 0 = none ∧
        Kf.st.mem (.tab 0) 0 = Kf.st.mem (.tab 0) 4 ∧ Kf.st.mem (.tab 1) 0 = .int 7 ∧
        st0.mem (.tab 1) 0 = .int 0 := by
  have hLZ : LaufzeitC c124 [2, 3] st0 KAB sperrAbstrakt :=
    ⟨⟨wAB, rfl, wAB_wurzeln.1, wAB_wurzeln.2⟩, fun _ _ _ _ h => h⟩
  have hDRF : DRFSC c124 sperrAbstrakt KAB
      (fun b => ∃ K, ErreichbarC c124 sperrAbstrakt KAB K ∧ beobC K = b) := fun _ _ hb => hb
  obtain ⟨-, hRC, -, -⟩ := schlusssatz_124_bei 0 wAB wAB_wurzeln sperrAbstrakt
    (fun _ _ _ _ h => h) _ hDRF
  refine ⟨hLZ, hDRF, hRC, ?_⟩
  -- the C blocks of the run, from related states
  obtain ⟨st1, hx1, hc1, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privA 0 (by decide) (.lit 7) 7 ρ0 (fun _ => rfl) (by decide) _ st0 corrW_st0 []
    ⟨7, by decide, by decide⟩ rfl
  obtain ⟨st2, hx2, hc2, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privA 1 (by decide) (.lit 7) 7 ρ0 (fun _ => rfl) (by decide) _ st1 hc1 []
    ⟨7, by decide, by decide⟩ rfl
  obtain ⟨st3, hx3, hc3, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privB 0 (by decide) (.lit 5) 5 ρ0 (fun _ => rfl) (by decide) _ st2 hc2 []
    ⟨5, by decide, by decide⟩ rfl
  obtain ⟨st4, hx4, hc4⟩ := cSetze_lauf 30 (by decide) _ st3 hc3 ρ0 [] [] ⟨30, by decide, by decide⟩ rfl
  obtain ⟨st5, hx5, hc5⟩ := cSetze_lauf 70 (by decide) _ st4 hc4 ρ0 [] [] ⟨70, by decide, by decide⟩ rfl
  have hx6 := cPruefe_lauf _ st5 hc5 ρ0
  -- the run: thread 0 into its critical section, thread 1 up to `L_nimm();`
  have r1 := ErreichbarC.schritt (E := c124) (LP := sperrAbstrakt) (K0 := KAB) .start
    (SchrittC.teile KAB 0 cA0 cRestA1 [] ρ0 rfl)
  have r2 := ErreichbarC.schritt r1 (SchrittC.block _ 0 cA0 [cRestA1] ρ0 st1 ρ0 rfl rfl hx1)
  have r3 := ErreichbarC.schritt r2 (SchrittC.teile _ 0 cA1 cRestA2 [] ρ0 rfl)
  have r4 := ErreichbarC.schritt r3 (SchrittC.block _ 0 cA1 [cRestA2] ρ0 st2 ρ0 rfl rfl hx2)
  have r5 := ErreichbarC.schritt r4 (SchrittC.teile _ 0 cNimm cRestA3 [] ρ0 rfl)
  have r6 := ErreichbarC.schritt r5 (SchrittC.sperre _ 0 0 [cRestA3] ρ0 (.nimm 0)
    (halterSetze (fun _ => none) 0 (some 0)) rfl rfl ⟨rfl, rfl⟩)
  have r7 := ErreichbarC.schritt r6 (SchrittC.teile _ 0 cSetzeA cRestA4 [] ρ0 rfl)
  have r8 := ErreichbarC.schritt r7 (SchrittC.teile _ 1 cB0 cRestB1 [] ρ0 rfl)
  have r9 := ErreichbarC.schritt r8 (SchrittC.block _ 1 cB0 [cRestB1] ρ0 st3 ρ0 rfl rfl hx3)
  have r10 := ErreichbarC.schritt r9 (SchrittC.teile _ 1 cNimm cRestB2 [] ρ0 rfl)
  -- thread 0 finishes its critical section and releases; thread 1 takes the lock
  have r11 := ErreichbarC.schritt r10 (SchrittC.block _ 0 cSetzeA [cRestA4] ρ0 st4 ρ0 rfl rfl hx4)
  have r12 := ErreichbarC.schritt r11 (SchrittC.teile _ 0 cGib cPruefe [] ρ0 rfl)
  have r13 := ErreichbarC.schritt r12 (SchrittC.sperre _ 0 1 [cPruefe] ρ0 (.gib 0)
    (halterSetze (halterSetze (fun _ => none) 0 (some 0)) 0 none) rfl rfl ⟨rfl, rfl⟩)
  have r14 := ErreichbarC.schritt r13 (SchrittC.sperre _ 1 0 [cRestB2] ρ0 (.nimm 0)
    (halterSetze (halterSetze (halterSetze (fun _ => none) 0 (some 0)) 0 none) 0 (some 1))
    rfl rfl ⟨rfl, rfl⟩)
  -- thread 1 runs its critical section and returns; then thread 0 returns
  have r15 := ErreichbarC.schritt r14 (SchrittC.teile _ 1 cSetzeB cGib [] ρ0 rfl)
  have r16 := ErreichbarC.schritt r15 (SchrittC.block _ 1 cSetzeB [cGib] ρ0 st5 ρ0 rfl rfl hx5)
  have r17 := ErreichbarC.schritt r16 (SchrittC.sperre _ 1 1 [] ρ0 (.gib 0)
    (halterSetze (halterSetze (halterSetze (halterSetze (fun _ => none) 0 (some 0)) 0 none) 0
      (some 1)) 0 none) rfl rfl ⟨rfl, rfl⟩)
  have r18 := ErreichbarC.schritt r17 (SchrittC.ende _ 1 ρ0 rfl)
  have r19 := ErreichbarC.schritt r18 (SchrittC.block _ 0 cPruefe [] ρ0 _ ρ0 rfl rfl hx6)
  have r20 := ErreichbarC.schritt r19 (SchrittC.ende _ 0 ρ0 rfl)
  obtain ⟨hinv, hende⟩ := schlusssatz_124_c 0 wAB wAB_wurzeln sperrAbstrakt (fun _ _ _ _ h => h)
    _ r20
  refine ⟨_, _, _, r10, rfl, rfl, fun ℓ K' hs => ?_, r14, rfl, r20, rfl, rfl, rfl,
    hinv rfl, hende 0 rfl rfl, rfl⟩
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, hx, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, hx, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, ho, hl, -, -⟩
  · cases hK
  · cases hK
  · cases hK; exact ext_kein_block hx
  · cases hK; exact ext_kein_block hx
  · cases hK
    cases ho
    have h' : (none : Option Faden) = some 0 := hl.1.symm.trans rfl
    cases h'

end Zeuge
section ZeugeRennen

/-- **WITNESS of the race transfer** (`rennfreiC_aus_sim`, rule 13): on the
    contended run of `schlusssatz_124_zeuge`, taken as an indexed SC run of
    20 steps, the two critical sections -- step 10, thread 0's `setze(30);`,
    and step 15, thread 1's `setze(70);` -- CONFLICT (both write
    `konto_speicher`), and the race freedom PROVED from machine G orders them
    through a lock; here the order is thread 0's `L_gib();` at step 12 and
    thread 1's `L_nimm();` at step 13. -/
theorem rennfreiC_zeuge_124 :
    ∃ (ks : Nat → KonfC) (ts : Nat → Faden) (ls : Nat → Etikett),
      LaufC c124 sperrAbstrakt KAB ks ts ls 20 ∧ KonfliktC c124 ls 10 15 (.tab 0) ∧
      ts 10 ≠ ts 15 ∧ (∃ L, GeordnetC ts ls L 10 15) ∧
      ls 12 = .sperre (.gib 0) ∧ ls 13 = .sperre (.nimm 0) ∧ ts 12 = 0 ∧ ts 13 = 1 := by
  have hDRF : DRFSC c124 sperrAbstrakt KAB
      (fun b => ∃ K, ErreichbarC c124 sperrAbstrakt KAB K ∧ beobC K = b) := fun _ _ hb => hb
  obtain ⟨-, hRC, -, -⟩ := schlusssatz_124_bei 0 wAB wAB_wurzeln sperrAbstrakt
    (fun _ _ _ _ h => h) _ hDRF
  obtain ⟨st1, hx1, hc1, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privA 0 (by decide) (.lit 7) 7 ρ0 (fun _ => rfl) (by decide) _ st0 corrW_st0 []
    ⟨7, by decide, by decide⟩ rfl
  obtain ⟨st2, hx2, hc2, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privA 1 (by decide) (.lit 7) 7 ρ0 (fun _ => rfl) (by decide) _ st1 hc1 []
    ⟨7, by decide, by decide⟩ rfl
  obtain ⟨st3, hx3, hc3, -⟩ := cStore_lauf 2 (CallAt c124.L c124.orc keinXR c124.Pr 1) keinXR
    KTab.privB 0 (by decide) (.lit 5) 5 ρ0 (fun _ => rfl) (by decide) _ st2 hc2 []
    ⟨5, by decide, by decide⟩ rfl
  obtain ⟨st4, hx4, hc4⟩ := cSetze_lauf 30 (by decide) _ st3 hc3 ρ0 [] [] ⟨30, by decide, by decide⟩ rfl
  obtain ⟨st5, hx5, hc5⟩ := cSetze_lauf 70 (by decide) _ st4 hc4 ρ0 [] [] ⟨70, by decide, by decide⟩ rfl
  have hx6 := cPruefe_lauf _ st5 hc5 ρ0
  have l0 : LaufC c124 sperrAbstrakt KAB (fun _ => KAB) (fun _ => 0) (fun _ => .still) 0 :=
    ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  have l1 := laufC_snoc l0 (SchrittC.teile _ 0 cA0 cRestA1 [] ρ0 rfl)
  have l2 := laufC_snoc l1 (SchrittC.block _ 0 cA0 [cRestA1] ρ0 st1 ρ0 rfl rfl hx1)
  have l3 := laufC_snoc l2 (SchrittC.teile _ 0 cA1 cRestA2 [] ρ0 rfl)
  have l4 := laufC_snoc l3 (SchrittC.block _ 0 cA1 [cRestA2] ρ0 st2 ρ0 rfl rfl hx2)
  have l5 := laufC_snoc l4 (SchrittC.teile _ 0 cNimm cRestA3 [] ρ0 rfl)
  have l6 := laufC_snoc l5 (SchrittC.sperre _ 0 0 [cRestA3] ρ0 (.nimm 0)
    (halterSetze (fun _ => none) 0 (some 0)) rfl rfl ⟨rfl, rfl⟩)
  have l7 := laufC_snoc l6 (SchrittC.teile _ 0 cSetzeA cRestA4 [] ρ0 rfl)
  have l8 := laufC_snoc l7 (SchrittC.teile _ 1 cB0 cRestB1 [] ρ0 rfl)
  have l9 := laufC_snoc l8 (SchrittC.block _ 1 cB0 [cRestB1] ρ0 st3 ρ0 rfl rfl hx3)
  have l10 := laufC_snoc l9 (SchrittC.teile _ 1 cNimm cRestB2 [] ρ0 rfl)
  have l11 := laufC_snoc l10 (SchrittC.block _ 0 cSetzeA [cRestA4] ρ0 st4 ρ0 rfl rfl hx4)
  have l12 := laufC_snoc l11 (SchrittC.teile _ 0 cGib cPruefe [] ρ0 rfl)
  have l13 := laufC_snoc l12 (SchrittC.sperre _ 0 1 [cPruefe] ρ0 (.gib 0)
    (halterSetze (halterSetze (fun _ => none) 0 (some 0)) 0 none) rfl rfl ⟨rfl, rfl⟩)
  have l14 := laufC_snoc l13 (SchrittC.sperre _ 1 0 [cRestB2] ρ0 (.nimm 0)
    (halterSetze (halterSetze (halterSetze (fun _ => none) 0 (some 0)) 0 none) 0 (some 1))
    rfl rfl ⟨rfl, rfl⟩)
  have l15 := laufC_snoc l14 (SchrittC.teile _ 1 cSetzeB cGib [] ρ0 rfl)
  have l16 := laufC_snoc l15 (SchrittC.block _ 1 cSetzeB [cGib] ρ0 st5 ρ0 rfl rfl hx5)
  have l17 := laufC_snoc l16 (SchrittC.sperre _ 1 1 [] ρ0 (.gib 0)
    (halterSetze (halterSetze (halterSetze (halterSetze (fun _ => none) 0 (some 0)) 0 none) 0
      (some 1)) 0 none) rfl rfl ⟨rfl, rfl⟩)
  have l18 := laufC_snoc l17 (SchrittC.ende _ 1 ρ0 rfl)
  have l19 := laufC_snoc l18 (SchrittC.block _ 0 cPruefe [] ρ0 _ ρ0 rfl rfl hx6)
  have l20 := laufC_snoc l19 (SchrittC.ende _ 0 ρ0 rfl)
  refine ⟨_, _, _, l20, ⟨by decide, by decide, Or.inl (by decide)⟩, by decide,
    hRC _ _ _ 20 l20 10 15 (.tab 0) (by decide) (by decide) (by decide)
      ⟨by decide, by decide, Or.inl (by decide)⟩, rfl, rfl, rfl, rfl⟩

end ZeugeRennen

/-
CUTS: what this file does not do, by name (PLAN §7 lists the open steps).
- The C unit `c124` is the emitted text transcribed as data by hand; there is
  no Lean C parser (the same joint as A2 of stage (a)).
- The G program `kP` is written from the source by hand: the exporter refuses
  124 (`LG003`), so the parse and elaboration step of stage (a) (part 1 of
  `schlusssatz_104`) has no counterpart here. `setze`'s `ensures` is stronger
  than the source's (Korpus124.lean, header): with the source's contract the
  goal theorem's premise (b) fails.
- The simulation certificate `sim124` is constructed for this program; a
  checker for concurrent correspondence certificates over all emitted forms
  (T2 for stage (b)) does not exist.
- The semantics runs a lock call only at the top of a root's continuation,
  not inside a loop, a branch or a callee (the emitted 124 has none there);
  foreign calls other than the lock primitive, volatile and atomic accesses
  are outside the direct fragment.
-/

end K124

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.K124.c124_direkt
#print axioms Gabbro.Grammatik.K124.gBlatt
#print axioms Gabbro.Grammatik.K124.gNimm
#print axioms Gabbro.Grammatik.K124.gSetze
#print axioms Gabbro.Grammatik.K124.gGib
#print axioms Gabbro.Grammatik.K124.gPruefe
#print axioms Gabbro.Grammatik.K124.cStore_lauf
#print axioms Gabbro.Grammatik.K124.cSetze_lauf
#print axioms Gabbro.Grammatik.K124.cPruefe_lauf
#print axioms Gabbro.Grammatik.K124.schrittA
#print axioms Gabbro.Grammatik.K124.schrittB
#print axioms Gabbro.Grammatik.K124.r124_start
#print axioms Gabbro.Grammatik.K124.sim124
#print axioms Gabbro.Grammatik.K124.schlusssatz_124_bei
#print axioms Gabbro.Grammatik.K124.schlusssatz_124
#print axioms Gabbro.Grammatik.K124.c124_sperrinv
#print axioms Gabbro.Grammatik.K124.c124_ende
#print axioms Gabbro.Grammatik.K124.schlusssatz_124_c
#print axioms Gabbro.Grammatik.K124.schlusssatz_124_zeuge
#print axioms Gabbro.Grammatik.K124.rennfreiC_zeuge_124

