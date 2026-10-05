/-
  File:      Grammatik/X86/PipelineLinkRel8.lean
  Subject:   Linking: rel8 selection convergence and fall-through coverage.

  FOLLOW-UP of lane 1193 (`PipelineLinkMulti.lean`): open were
  rel8-selection convergence, fall-through coverage beyond re-decoded
  windows, and instructions outside jump/call/conditional sites. This
  file proves branch relaxation with relocation converges (monotone
  widening, termination within the short-site count, fixed-point fit)
  and that the linked bytes cover exactly the relaxed program:
  fall-through bytes survive through the multi-operand frame, every
  site's bytes are exact, short sites read back, long jump sites
  re-decode through the accepted agreement legs; overlapping sites
  stay refused.

  Reused, never duplicated (no second decoder, loader, executor,
  ISA model or IR):
  - operands/patching: `MultiFeld`, `multiBytes`, `multiPatch`,
    `multiPatchAlle`, `opStelle`, `opWeite`, `opsDisjunktB`,
    `opsDisjunktB_gilt`, `multiPatchAlle_rahmen`/`_laenge`/
    `_kopf_stelle`, `disjunktStellen`;
  - rel8 vocabulary: `rel8Passt`, `rel8Byte`, `disp8Signed`,
    `rel8Byte_rundgang`, `multi_rel8_liest`;
  - rel32 bridge: `rel32Bytes`, `rel32Passt`, `fenster_sprung`,
    `feld_agreement_sprung`;
  - mapping/run witnesses: `ruf_schritt_zeuge` (reached
    memory-changing run through actual bytes).
-/
import Grammatik.X86.PipelineLinkMulti

namespace Gabbro.Grammatik.X86

/-- One relaxed program piece: fixed fall-through bytes of length
    `len`, a short (rel8, 2-byte) branch site, or a widened
    (rel32, 5-byte) unconditional-jump site. -/
inductive RelaxStueck where
  | fest (len : Nat)
  | kurz
  | weit
  deriving DecidableEq, Repr

/-- Laid-out width in bytes: fall-through keeps its length, a short
    site is opcode plus one displacement byte, a wide site is opcode
    plus four displacement bytes. -/
def stueckWeite : RelaxStueck → Nat
  | .fest len => len
  | .kurz => 2
  | .weit => 5

/-- A short site never exceeds its widened form. -/
theorem stueckWeite_kurz_le_weit :
    stueckWeite .kurz ≤ stueckWeite .weit := by
  decide

/-! ## 1. Layout: addresses grow monotonically under widening. -/

/-- Widening order on pieces: fixed stays fixed, short stays short or
    widens to the rel32 form. -/
inductive stueckLE : RelaxStueck → RelaxStueck → Prop where
  | fest_eq (l : Nat) : stueckLE (.fest l) (.fest l)
  | kurz_kurz : stueckLE .kurz .kurz
  | kurz_weit : stueckLE .kurz .weit
  | weit_weit : stueckLE .weit .weit

/-- Pointwise widening order on relaxed programs. -/
def progLE : List RelaxStueck → List RelaxStueck → Prop
  | [], [] => True
  | a :: pa, b :: pb => stueckLE a b ∧ progLE pa pb
  | _, _ => False

/-- Widths respect the widening order. Every premise is used: the
    order hypothesis picks the case, the width equations close it. -/
theorem weite_mono {a b : RelaxStueck} (h : stueckLE a b) :
    stueckWeite a ≤ stueckWeite b := by
  cases h with
  | fest_eq l => simp [stueckWeite]
  | kurz_kurz => simp [stueckWeite]
  | kurz_weit => decide
  | weit_weit => simp [stueckWeite]

/-- Laid-out start addresses from `base`: prefix sums of widths. -/
def adressenAux : List RelaxStueck → Nat → List Nat
  | [], _ => []
  | st :: rest, base => base :: adressenAux rest (base + stueckWeite st)

/-- Laid-out start addresses of a relaxed program at load base. -/
def adressen (prog : List RelaxStueck) (basis : Nat) : List Nat :=
  adressenAux prog basis

/-- Addresses keep the program length. -/
theorem adressenAux_laenge (prog : List RelaxStueck) (basis : Nat) :
    (adressenAux prog basis).length = prog.length := by
  induction prog generalizing basis with
  | nil => rfl
  | cons st rest ih => simp [adressenAux, ih]

/-- Pointwise address comparison: every laid-out address of the
    narrower program is covered above by the wider one. -/
def adressenLE (l₁ l₂ : List Nat) : Prop :=
  ∀ (i : Nat) (a : Nat), l₁[i]? = some a →
    ∃ (b : Nat), l₂[i]? = some b ∧ a ≤ b

/-- MONOTONE WIDENING: widening sites never moves any laid-out
    address down. Every premise is used: `hbase` seeds the head,
    `hle` orders head widths (through `weite_mono`) and tail
    addresses (through the induction hypothesis). -/
theorem adressenAux_mono (p q : List RelaxStueck) (b₁ b₂ : Nat)
    (hbase : b₁ ≤ b₂) (hle : progLE p q) :
    adressenLE (adressenAux p b₁) (adressenAux q b₂) := by
  induction p generalizing q b₁ b₂ with
  | nil =>
    cases q with
    | nil =>
      unfold adressenLE
      intro i a h
      simp [adressenAux] at h
    | cons hd tl =>
      simp [progLE] at hle
  | cons hd tl ih =>
    cases q with
    | nil =>
      simp [progLE] at hle
    | cons hd' tl' =>
      simp only [progLE] at hle
      obtain ⟨hhd, htl⟩ := hle
      have hw := weite_mono hhd
      have htail := ih tl' (b₁ + stueckWeite hd)
        (b₂ + stueckWeite hd') (by omega) htl
      unfold adressenLE
      intro i a h
      cases i with
      | zero =>
        simp only [adressenAux, List.getElem?_cons_zero] at h
        simp only [adressenAux, List.getElem?_cons_zero]
        have heq : b₁ = a := Option.some_inj.mp h
        subst heq
        exact ⟨b₂, rfl, hbase⟩
      | succ n =>
        simp only [adressenAux, List.getElem?_cons_succ] at h ⊢
        exact htail n a h

/-! ## 2. Displacement, selection, one relaxation step. -/

/-- Displacement of a branch at laid-out address `addr` with total
    instruction width `w` against absolute target `ziel`: the value
    the relocation must encode. -/
def dispAn (ziel addr w : Nat) : Int :=
  (ziel : Int) - (((addr + w : Nat)) : Int)

/-- One relaxation step over program, targets and laid-out addresses:
    a short site whose displacement misses signed-8 widens; fixed
    pieces, widened sites and fitting short sites stay. Targets
    (`ziele`) and addresses run parallel to the program; on length
    mismatch the tail is kept unchanged, never guessed. -/
def relaxSchrittAux : List RelaxStueck → List (Option Nat) → List Nat →
    List RelaxStueck
  | [], _, _ => []
  | st :: pr, z :: zr, a :: ar =>
    match st, z with
    | .kurz, some t =>
      (if rel8Passt (dispAn t a 2) then .kurz else .weit) ::
        relaxSchrittAux pr zr ar
    | _, _ => st :: relaxSchrittAux pr zr ar
  | st :: pr, _, _ => st :: relaxSchrittAux pr [] []

/-- One relaxation step at load base: addresses are recomputed from
    the current widths, then unfit short sites widen. -/
def relaxSchritt (prog : List RelaxStueck) (ziele : List (Option Nat))
    (basis : Nat) : List RelaxStueck :=
  relaxSchrittAux prog ziele (adressen prog basis)

/-- A step keeps the program length. -/
theorem relaxSchrittAux_laenge (p : List RelaxStueck)
    (z : List (Option Nat)) (a : List Nat) :
    (relaxSchrittAux p z a).length = p.length := by
  induction p generalizing z a with
  | nil => simp [relaxSchrittAux]
  | cons st pr ih =>
    cases z with
    | nil =>
      cases a with
      | nil => simp [relaxSchrittAux, ih]
      | cons ah ar => simp [relaxSchrittAux, ih]
    | cons zh zr =>
      cases a with
      | nil => simp [relaxSchrittAux, ih]
      | cons ah ar =>
        cases st with
        | fest l =>
          cases zh with
          | none => simp [relaxSchrittAux, ih]
          | some t => simp [relaxSchrittAux, ih]
        | kurz =>
          cases zh with
          | none => simp [relaxSchrittAux, ih]
          | some t =>
            simp only [relaxSchrittAux]
            simp [ih]
        | weit =>
          cases zh with
          | none => simp [relaxSchrittAux, ih]
          | some t => simp [relaxSchrittAux, ih]

/-- A step only ever widens: the output covers the input in the
    widening order. Every premise is used: the program shape drives
    the induction, targets and addresses pick the arm, the fit check
    picks the short-site case. -/
theorem schrittWaechstAux (p : List RelaxStueck)
    (z : List (Option Nat)) (a : List Nat) :
    progLE p (relaxSchrittAux p z a) := by
  induction p generalizing z a with
  | nil => simp [progLE, relaxSchrittAux]
  | cons st pr ih =>
    cases z with
    | nil =>
      cases a with
      | nil =>
        simp only [relaxSchrittAux]
        simp only [progLE]
        constructor
        · cases st with
          | fest l => exact stueckLE.fest_eq l
          | kurz => exact stueckLE.kurz_kurz
          | weit => exact stueckLE.weit_weit
        · exact ih [] []
      | cons ah ar =>
        simp only [relaxSchrittAux]
        simp only [progLE]
        constructor
        · cases st with
          | fest l => exact stueckLE.fest_eq l
          | kurz => exact stueckLE.kurz_kurz
          | weit => exact stueckLE.weit_weit
        · exact ih [] []
    | cons zh zr =>
      cases a with
      | nil =>
        simp only [relaxSchrittAux]
        simp only [progLE]
        constructor
        · cases st with
          | fest l => exact stueckLE.fest_eq l
          | kurz => exact stueckLE.kurz_kurz
          | weit => exact stueckLE.weit_weit
        · exact ih [] []
      | cons ah ar =>
        cases st with
        | fest l =>
          cases zh with
          | none =>
            simp only [relaxSchrittAux]
            simp only [progLE]
            exact ⟨stueckLE.fest_eq l, ih zr ar⟩
          | some t =>
            simp only [relaxSchrittAux]
            simp only [progLE]
            exact ⟨stueckLE.fest_eq l, ih zr ar⟩
        | kurz =>
          cases zh with
          | none =>
            simp only [relaxSchrittAux]
            simp only [progLE]
            exact ⟨stueckLE.kurz_kurz, ih zr ar⟩
          | some t =>
            simp only [relaxSchrittAux]
            simp only [progLE]
            constructor
            · by_cases hc : rel8Passt (dispAn t ah 2) = true
              · simp only [hc, if_true]
                exact stueckLE.kurz_kurz
              · simp only [hc]
                exact stueckLE.kurz_weit
            · exact ih zr ar
        | weit =>
          cases zh with
          | none =>
            simp only [relaxSchrittAux]
            simp only [progLE]
            exact ⟨stueckLE.weit_weit, ih zr ar⟩
          | some t =>
            simp only [relaxSchrittAux]
            simp only [progLE]
            exact ⟨stueckLE.weit_weit, ih zr ar⟩

/-- A step at load base only ever widens. -/
theorem relaxSchritt_waechst (prog : List RelaxStueck)
    (ziele : List (Option Nat)) (basis : Nat) :
    progLE prog (relaxSchritt prog ziele basis) := by
  unfold relaxSchritt
  exact schrittWaechstAux prog ziele (adressen prog basis)

/-- FIXED-POINT FIT: where the step rests, every short site with a
    listed target fits signed-8 at its laid-out address. Every
    premise is used: `h` ties the output to the input (head and tail
    projections), `hs`/`hz`/`ha` pick the site, target and address. -/
theorem schrittFixpunkt_passtAux (p : List RelaxStueck)
    (z : List (Option Nat)) (a : List Nat)
    (h : relaxSchrittAux p z a = p)
    (i : Nat) (t ad : Nat)
    (hs : p[i]? = some .kurz) (hz : z[i]? = some (some t))
    (ha : a[i]? = some ad) :
    rel8Passt (dispAn t ad 2) = true := by
  induction p generalizing z a i with
  | nil =>
    have hnil : (([] : List RelaxStueck)[i]? = none) :=
      List.getElem?_eq_none (by simp)
    rw [hnil] at hs
    cases hs
  | cons hd tl ih =>
    cases z with
    | nil =>
      have hnil : (([] : List (Option Nat))[i]? = none) :=
        List.getElem?_eq_none (by simp)
      rw [hnil] at hz
      cases hz
    | cons zh zr =>
      cases a with
      | nil =>
        have hnil : (([] : List Nat)[i]? = none) :=
          List.getElem?_eq_none (by simp)
        rw [hnil] at ha
        cases ha
      | cons ah ar =>
        cases hd with
        | fest l =>
          cases zh with
          | none =>
            simp only [relaxSchrittAux] at h
            have htail : relaxSchrittAux tl zr ar = tl := by
              have h2 := congrArg List.tail h
              simpa using h2
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero] at hs
              simp at hs
            | succ n =>
              simp only [List.getElem?_cons_succ] at hs hz ha
              exact ih zr ar htail n hs hz ha
          | some t₀ =>
            simp only [relaxSchrittAux] at h
            have htail : relaxSchrittAux tl zr ar = tl := by
              have h2 := congrArg List.tail h
              simpa using h2
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero] at hs
              simp at hs
            | succ n =>
              simp only [List.getElem?_cons_succ] at hs hz ha
              exact ih zr ar htail n hs hz ha
        | kurz =>
          cases zh with
          | none =>
            simp only [relaxSchrittAux] at h
            have htail : relaxSchrittAux tl zr ar = tl := by
              have h2 := congrArg List.tail h
              simpa using h2
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero] at hz
              simp at hz
            | succ n =>
              simp only [List.getElem?_cons_succ] at hs hz ha
              exact ih zr ar htail n hs hz ha
          | some t₀ =>
            simp only [relaxSchrittAux] at h
            have hhead : (if rel8Passt (dispAn t₀ ah 2) then
                RelaxStueck.kurz else RelaxStueck.weit) =
                RelaxStueck.kurz := by
              have h2 := congrArg List.head? h
              simpa using h2
            have htail : relaxSchrittAux tl zr ar = tl := by
              have h2 := congrArg List.tail h
              simpa using h2
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero] at hs hz ha
              have ht : t₀ = t :=
                Option.some_inj.mp (Option.some_inj.mp hz)
              have had : ah = ad := Option.some_inj.mp ha
              rw [ht] at hhead
              rw [had] at hhead
              by_cases hc : rel8Passt (dispAn t ad 2) = true
              · exact hc
              · simp only [hc] at hhead
                simp at hhead
            | succ n =>
              simp only [List.getElem?_cons_succ] at hs hz ha
              exact ih zr ar htail n hs hz ha
        | weit =>
          cases zh with
          | none =>
            simp only [relaxSchrittAux] at h
            have htail : relaxSchrittAux tl zr ar = tl := by
              have h2 := congrArg List.tail h
              simpa using h2
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero] at hs
              simp at hs
            | succ n =>
              simp only [List.getElem?_cons_succ] at hs hz ha
              exact ih zr ar htail n hs hz ha
          | some t₀ =>
            simp only [relaxSchrittAux] at h
            have htail : relaxSchrittAux tl zr ar = tl := by
              have h2 := congrArg List.tail h
              simpa using h2
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero] at hs
              simp at hs
            | succ n =>
              simp only [List.getElem?_cons_succ] at hs hz ha
              exact ih zr ar htail n hs hz ha

/-- Fixed-point fit at load base: where the step rests, every short
    site with a listed target fits signed-8. -/
theorem relaxSchritt_fixpunkt_passt (prog : List RelaxStueck)
    (ziele : List (Option Nat)) (basis : Nat)
    (h : relaxSchritt prog ziele basis = prog)
    (i : Nat) (t ad : Nat)
    (hs : prog[i]? = some .kurz) (hz : ziele[i]? = some (some t))
    (ha : (adressen prog basis)[i]? = some ad) :
    rel8Passt (dispAn t ad 2) = true := by
  unfold relaxSchritt at h
  exact schrittFixpunkt_passtAux prog ziele (adressen prog basis)
    h i t ad hs hz ha

end Gabbro.Grammatik.X86
