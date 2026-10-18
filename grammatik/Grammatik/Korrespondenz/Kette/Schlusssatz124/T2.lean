/- Part 2 of 4 of `Schlusssatz124` (split by instrumente/teile/lean-teilen.py; the umbrella `Schlusssatz124.lean` imports all parts). -/
import Grammatik.Korrespondenz.Kette.Schlusssatz124.T1

namespace Gabbro.Grammatik
namespace K124

open Zielsatz

/-- The C positions of a `hauptA` thread. -/
def posA : Nat → CFaden
  | 0 => .an [cHauptA] ρ0
  | 1 => .an [cA0, cRestA1] ρ0
  | 2 => .an [cRestA1] ρ0
  | 3 => .an [cA1, cRestA2] ρ0
  | 4 => .an [cRestA2] ρ0
  | 5 => .an [cNimm, cRestA3] ρ0
  | 6 => .an [cRestA3] ρ0
  | 7 => .an [cSetzeA, cRestA4] ρ0
  | 8 => .an [cRestA4] ρ0
  | 9 => .an [cGib, cPruefe] ρ0
  | 10 => .an [cPruefe] ρ0
  | 11 => .an [] ρ0
  | _ => .aus

/-- Which G residue a C position of `hauptA` corresponds to. -/
def gOfA : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | 7 => 3 | 8 => 4 | 9 => 4
  | 10 => 5 | _ => 6

/-- The locks a `hauptA` thread holds at each G residue. -/
def heldGA : Nat → List DR.Lock
  | 3 => [lL] | 4 => [lL] | _ => []

def posB : Nat → CFaden
  | 0 => .an [cHauptB] ρ0
  | 1 => .an [cB0, cRestB1] ρ0
  | 2 => .an [cRestB1] ρ0
  | 3 => .an [cNimm, cRestB2] ρ0
  | 4 => .an [cRestB2] ρ0
  | 5 => .an [cSetzeB, cGib] ρ0
  | 6 => .an [cGib] ρ0
  | 7 => .an [] ρ0
  | _ => .aus

def gOfB : Nat → Nat
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 3 | _ => 4

def heldGB : Nat → List DR.Lock
  | 2 => [lL] | 3 => [lL] | _ => []

/-- A `hauptA` thread: C position `i` and the G thread at the corresponding
    residue, with the locks that residue holds. -/
def ThreadA (c : CFaden) (z : RufFadenG DR) : Prop :=
  ∃ (i : Nat) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR)), i ≤ 12 ∧ c = posA i ∧
    z = ⟨[], frA (gOfA i), sp, log⟩ ∧ offen sp = heldGA (gOfA i)

def ThreadB (c : CFaden) (z : RufFadenG DR) : Prop :=
  ∃ (i : Nat) (sp : List (Ereignis DR)) (log : List (RufEreignisF DR)), i ≤ 8 ∧ c = posB i ∧
    z = ⟨[], frB (gOfB i), sp, log⟩ ∧ offen sp = heldGB (gOfB i)

/-- Thread `t` of the C and of G, by the root the runtime started on it. -/
def FadenRel : Option Nat → CFaden → RufFadenG DR → Prop
  | some 2, c, z => ThreadA c z
  | some 3, c, z => ThreadB c z
  | _, c, _ => c = .aus

/-- The C lock `0` is held by `u` exactly when the G thread `u` holds `L`. -/
def SperrRel (K : KonfC) (M : RufMaschineG DR) : Prop :=
  ∀ (L : Nat) (u : Faden), K.halter L = some u ↔ (L = 0 ∧ lL ∈ offen (M.faeden u).spur)

/-- **THE SIMULATION RELATION** of `beispiele/124` under a root assignment `w`:
    memory corresponds (`corrW`), locks correspond, and every thread is at
    corresponding positions. -/
def R124 (w : Faden → Option Nat) (K : KonfC) (M : RufMaschineG DR) : Prop :=
  corrW kEL (M.speicher.welt []) K.st ∧ SperrRel K M ∧
    ∀ t, FadenRel (w t) (K.faeden t) (M.faeden t)

section Sim

variable {passes : Nat}

/-! ### Segments of G steps -/

def seg1 (M M1 : RufMaschineG DR) : Nat → RufMaschineG DR
  | 0 => M
  | _ => M1

def seg2 (M M1 M2 : RufMaschineG DR) : Nat → RufMaschineG DR
  | 0 => M
  | 1 => M1
  | _ => M2

def seg5 (M M1 M2 M3 M4 M5 : RufMaschineG DR) : Nat → RufMaschineG DR
  | 0 => M
  | 1 => M1
  | 2 => M2
  | 3 => M3
  | 4 => M4
  | _ => M5

theorem lauf0 (M : RufMaschineG DR) (t : Faden) :
    LaufG PR OR passes M (fun _ => M) (fun _ => t) 0 :=
  ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

theorem lauf1 {M M1 : RufMaschineG DR} {t : Faden} (s1 : RufSchrittG PR OR passes M t M1) :
    LaufG PR OR passes M (seg1 M M1) (fun _ => t) 1 :=
  ⟨rfl, fun k hk => by
    match k, hk with
    | 0, _ => exact s1
    | k + 1, hk => exact absurd hk (by omega)⟩

theorem lauf2 {M M1 M2 : RufMaschineG DR} {t : Faden} (s1 : RufSchrittG PR OR passes M t M1)
    (s2 : RufSchrittG PR OR passes M1 t M2) : LaufG PR OR passes M (seg2 M M1 M2) (fun _ => t) 2 :=
  ⟨rfl, fun k hk => by
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
    | k + 2, hk => exact absurd hk (by omega)⟩

theorem lauf5 {M M1 M2 M3 M4 M5 : RufMaschineG DR} {t : Faden}
    (s1 : RufSchrittG PR OR passes M t M1) (s2 : RufSchrittG PR OR passes M1 t M2)
    (s3 : RufSchrittG PR OR passes M2 t M3) (s4 : RufSchrittG PR OR passes M3 t M4)
    (s5 : RufSchrittG PR OR passes M4 t M5) :
    LaufG PR OR passes M (seg5 M M1 M2 M3 M4 M5) (fun _ => t) 5 :=
  ⟨rfl, fun k hk => by
    match k, hk with
    | 0, _ => exact s1
    | 1, _ => exact s2
    | 2, _ => exact s3
    | 3, _ => exact s4
    | 4, _ => exact s5
    | k + 5, hk => exact absurd hk (by omega)⟩

theorem fremd_ende {ms : Nat → RufMaschineG DR} {M : RufMaschineG DR} {t : Faden} {N : Nat}
    (hl : LaufG PR OR passes M ms (fun _ => t) N) (u : Faden) (hu : u ≠ t) :
    (ms N).faeden u = M.faeden u :=
  laufG_fremd hl u (fun _ _ h => hu h.symm) N (Nat.le_refl N)

/-! ### The lock relation along a step -/

theorem sperrRel_gleich {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden) (hS : SperrRel K M)
    (hh : K'.halter = K.halter) (ht : offen (M'.faeden t).spur = offen (M.faeden t).spur)
    (ho : ∀ u, u ≠ t → M'.faeden u = M.faeden u) : SperrRel K' M' := by
  intro L u
  rw [hh]
  by_cases hu : u = t
  · subst hu; rw [ht]; exact hS L u
  · rw [ho u hu]; exact hS L u

theorem sperrRel_nimm {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden) (hS : SperrRel K M)
    (h0 : K.halter 0 = none) (hh : K'.halter = halterSetze K.halter 0 (some t))
    (ht : offen (M'.faeden t).spur = [lL]) (ho : ∀ u, u ≠ t → M'.faeden u = M.faeden u) :
    SperrRel K' M' := by
  intro L u
  rw [hh]
  unfold halterSetze
  by_cases hL : L = 0
  · subst hL
    rw [if_pos rfl]
    by_cases hu : u = t
    · subst hu; rw [ht]; exact ⟨fun _ => ⟨rfl, List.mem_singleton_self _⟩, fun _ => rfl⟩
    · rw [ho u hu]
      constructor
      · intro h
        have e : t = u := Option.some.inj h
        exact absurd e.symm hu
      · rintro ⟨_, hmem⟩
        have := (hS 0 u).mpr ⟨rfl, hmem⟩
        rw [h0] at this
        cases this
  · rw [if_neg hL]
    by_cases hu : u = t
    · subst hu
      rw [ht]
      constructor
      · intro h; exact absurd ((hS L u).mp h).1 hL
      · rintro ⟨h, _⟩; exact absurd h hL
    · rw [ho u hu]; exact hS L u

theorem sperrRel_gib {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden) (hS : SperrRel K M)
    (h0 : K.halter 0 = some t) (hh : K'.halter = halterSetze K.halter 0 none)
    (ht : offen (M'.faeden t).spur = []) (ho : ∀ u, u ≠ t → M'.faeden u = M.faeden u) :
    SperrRel K' M' := by
  intro L u
  rw [hh]
  unfold halterSetze
  by_cases hL : L = 0
  · subst hL
    rw [if_pos rfl]
    by_cases hu : u = t
    · subst hu; rw [ht]; simp
    · rw [ho u hu]
      constructor
      · intro h; cases h
      · rintro ⟨_, hmem⟩
        have := (hS 0 u).mpr ⟨rfl, hmem⟩
        rw [h0] at this
        exact absurd (Option.some.inj this) (Ne.symm hu)
  · rw [if_neg hL]
    by_cases hu : u = t
    · subst hu
      rw [ht]
      constructor
      · intro h; exact absurd ((hS L u).mp h).1 hL
      · rintro ⟨h, _⟩; exact absurd h hL
    · rw [ho u hu]; exact hS L u

/-- The relation after a step of `t`, from its three parts. -/
theorem r124_neu (w : Faden → Option Nat) {K K' : KonfC} {M M' : RufMaschineG DR} (t : Faden)
    (hR : R124 w K M) (hC : corrW kEL (M'.speicher.welt []) K'.st) (hS : SperrRel K' M')
    (hkf : ∀ u, u ≠ t → K'.faeden u = K.faeden u) (hmf : ∀ u, u ≠ t → M'.faeden u = M.faeden u)
    (ht : FadenRel (w t) (K'.faeden t) (M'.faeden t)) : R124 w K' M' := by
  refine ⟨hC, hS, fun u => ?_⟩
  by_cases hu : u = t
  · subst hu; exact ht
  · rw [hkf u hu, hmf u hu]; exact hR.2.2 u

/-! ### The C step, inverted at a known head -/

/-- The goal of one simulation step. -/
def SchrittZiel (w : Faden → Option Nat) (M : RufMaschineG DR) (t : Faden) (ℓ : Etikett)
    (K' : KonfC) : Prop :=
  ∃ (ms : Nat → RufMaschineG DR) (N : Nat), LaufG PR OR passes M ms (fun _ => t) N ∧
    R124 w K' (ms N) ∧ SegPasst c124 kEL lnr t ℓ ms N

/-- A split: no G step. -/
theorem k_teile (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {a b : CS} {k : List CS} {ρ : CLok}
    (hc : K.faeden t = .an (.seq a b :: k) ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    (hrel : FadenRel (w t) (.an (a :: b :: k) ρ) (M.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, hl, hK'⟩ | ⟨ρ', hK, -, -⟩ |
    ⟨s, k', ρ', st', ρ'', hK, hq, -, -, -⟩ | ⟨s, k', ρ', st', v', hK, hq, -, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK
    cases hK
    subst hl; subst hK'
    refine ⟨fun _ => M, 0, lauf0 M t, r124_neu w t hR hR.1 (sperrRel_gleich t hR.2.1 rfl rfl
      (fun _ _ => rfl)) (fun u hu => fadenSetze_ne _ _ _ _ hu) (fun _ _ => rfl)
      (by show FadenRel (w t) (fadenSetze K.faeden t _ t) (M.faeden t)
          rw [fadenSetze_eq]; exact hrel), ⟨?_, ?_, ?_, ?_⟩⟩
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK; cases hq
  · rw [hc] at hK; cases hK; cases hq
  · rw [hc] at hK; cases hK

/-- The end of a root body: no G step (G's root stands at its `return`). -/
theorem k_ende (w : Faden → Option Nat) {K K' : KonfC} {M : RufMaschineG DR} {t : Faden}
    {ℓ : Etikett} (hR : R124 w K M) {ρ : CLok}
    (hc : K.faeden t = .an [] ρ) (hs : SchrittC c124 sperrAbstrakt K t ℓ K')
    (hrel : FadenRel (w t) .aus (M.faeden t)) :
    SchrittZiel (passes := passes) w M t ℓ K' := by
  rcases schrittC_inv hs with ⟨a', b', k', ρ', hK, -, -⟩ | ⟨ρ', hK, hl, hK'⟩ |
    ⟨s, k', ρ', st', ρ'', hK, -, -, -, -⟩ | ⟨s, k', ρ', st', v', hK, -, -, -, -⟩ |
    ⟨n, k', ρ', op, h', hK, -, -, -, -⟩
  · rw [hc] at hK; cases hK
  · subst hl; subst hK'
    refine ⟨fun _ => M, 0, lauf0 M t, r124_neu w t hR hR.1 (sperrRel_gleich t hR.2.1 rfl rfl
      (fun _ _ => rfl)) (fun u hu => fadenSetze_ne _ _ _ _ hu) (fun _ _ => rfl)
      (by show FadenRel (w t) (fadenSetze K.faeden t _ t) (M.faeden t)
          rw [fadenSetze_eq]; exact hrel), ⟨?_, ?_, ?_, ?_⟩⟩
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro b hb; exact absurd hb List.not_mem_nil
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
    · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK
  · rw [hc] at hK; cases hK

end Sim

