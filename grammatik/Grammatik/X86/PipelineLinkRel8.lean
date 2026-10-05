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

/-! ## 3. Termination: at most one widening per short site. -/

/-- Number of remaining short sites: the termination measure. -/
def anzahlKurz : List RelaxStueck → Nat
  | [] => 0
  | .kurz :: r => 1 + anzahlKurz r
  | _ :: r => anzahlKurz r

/-- The widening order is reflexive. -/
theorem progLE_refl (p : List RelaxStueck) : progLE p p := by
  induction p with
  | nil => simp [progLE]
  | cons hd tl ih =>
    simp only [progLE]
    constructor
    · cases hd with
      | fest l => exact stueckLE.fest_eq l
      | kurz => exact stueckLE.kurz_kurz
      | weit => exact stueckLE.weit_weit
    · exact ih

/-- Widening composes on pieces. -/
theorem stueckLE_trans {a b c : RelaxStueck}
    (h₁ : stueckLE a b) (h₂ : stueckLE b c) : stueckLE a c := by
  cases h₁ with
  | fest_eq l =>
    cases h₂ with
    | fest_eq _ => exact stueckLE.fest_eq l
  | kurz_kurz =>
    cases h₂ with
    | kurz_kurz => exact stueckLE.kurz_kurz
    | kurz_weit => exact stueckLE.kurz_weit
  | kurz_weit =>
    cases h₂ with
    | weit_weit => exact stueckLE.kurz_weit
  | weit_weit =>
    cases h₂ with
    | weit_weit => exact stueckLE.weit_weit

/-- The widening order is transitive. Every premise is used: `h₁`
    and `h₂` split into head and tail, heads compose through
    `stueckLE_trans`, tails through the induction hypothesis. -/
theorem progLE_trans {p q r : List RelaxStueck}
    (h₁ : progLE p q) (h₂ : progLE q r) : progLE p r := by
  induction p generalizing q r with
  | nil =>
    cases q with
    | nil =>
      cases r with
      | nil => simp [progLE]
      | cons _ _ => simp [progLE] at h₂
    | cons _ _ => simp [progLE] at h₁
  | cons hd tl ih =>
    cases q with
    | nil => simp [progLE] at h₁
    | cons hd' tl' =>
      cases r with
      | nil => simp [progLE] at h₂
      | cons hd'' tl'' =>
        simp only [progLE] at h₁ h₂ ⊢
        obtain ⟨hhd₁, htl₁⟩ := h₁
        obtain ⟨hhd₂, htl₂⟩ := h₂
        exact ⟨stueckLE_trans hhd₁ hhd₂, ih htl₁ htl₂⟩

/-- Widening never creates short sites. -/
theorem progLE_anzahl {p q : List RelaxStueck}
    (h : progLE p q) : anzahlKurz q ≤ anzahlKurz p := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp [anzahlKurz]
    | cons _ _ => simp [progLE] at h
  | cons hd tl ih =>
    cases q with
    | nil => simp [progLE] at h
    | cons hd' tl' =>
      simp only [progLE] at h
      obtain ⟨hhd, htl⟩ := h
      have hle := ih htl
      cases hhd with
      | fest_eq l => simp only [anzahlKurz]; exact hle
      | kurz_kurz => simp only [anzahlKurz]; omega
      | kurz_weit => simp only [anzahlKurz]; omega
      | weit_weit => simp only [anzahlKurz]; exact hle

/-- Same short count under widening means no step happened. -/
theorem progLE_gleich {p q : List RelaxStueck}
    (h : progLE p q) (hc : anzahlKurz p = anzahlKurz q) : p = q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons _ _ => simp [progLE] at h
  | cons hd tl ih =>
    cases q with
    | nil => simp [progLE] at h
    | cons hd' tl' =>
      simp only [progLE] at h
      obtain ⟨hhd, htl⟩ := h
      cases hhd with
      | fest_eq l =>
        simp only [anzahlKurz] at hc
        have hte := ih htl hc
        simp [hte]
      | kurz_kurz =>
        simp only [anzahlKurz] at hc
        have hte : tl = tl' := ih htl (by omega)
        simp [hte]
      | kurz_weit =>
        simp only [anzahlKurz] at hc
        have hle := progLE_anzahl htl
        omega
      | weit_weit =>
        simp only [anzahlKurz] at hc
        have hte := ih htl hc
        simp [hte]

/-- Without short sites the step rests. -/
theorem schrittOhneKurzAux (p : List RelaxStueck)
    (z : List (Option Nat)) (a : List Nat)
    (h : anzahlKurz p = 0) : relaxSchrittAux p z a = p := by
  induction p generalizing z a with
  | nil => simp [relaxSchrittAux]
  | cons hd tl ih =>
    have htl : anzahlKurz tl = 0 := by
      cases hd with
      | fest l => simpa [anzahlKurz] using h
      | kurz => simp [anzahlKurz] at h
      | weit => simpa [anzahlKurz] using h
    cases hd with
    | fest l =>
      cases z <;> cases a <;> simp [relaxSchrittAux, ih _ _ htl]
    | kurz =>
      simp only [anzahlKurz] at h
      omega
    | weit =>
      cases z <;> cases a <;> simp [relaxSchrittAux, ih _ _ htl]

/-- Without short sites the step rests at load base. -/
theorem relaxSchrittOhneKurz (p : List RelaxStueck)
    (z : List (Option Nat)) (b : Nat)
    (h : anzahlKurz p = 0) : relaxSchritt p z b = p :=
  schrittOhneKurzAux p z (adressen p b) h

/-- A changing step strictly reduces the short count. Every premise
    is used: the order gives the inequality, the disequality (through
    `progLE_gleich`) makes it strict. -/
theorem schrittAendertZahl (p : List RelaxStueck)
    (z : List (Option Nat)) (a : List Nat)
    (hne : relaxSchrittAux p z a ≠ p) :
    anzahlKurz (relaxSchrittAux p z a) < anzahlKurz p := by
  have hle1 := schrittWaechstAux p z a
  have hle2 := progLE_anzahl hle1
  have hne2 : anzahlKurz p ≠ anzahlKurz (relaxSchrittAux p z a) := by
    intro hcon
    exact hne (progLE_gleich hle1 hcon).symm
  omega

/-- A changing step at load base strictly reduces the short count. -/
theorem relaxSchrittAendertZahl (p : List RelaxStueck)
    (z : List (Option Nat)) (b : Nat)
    (hne : relaxSchritt p z b ≠ p) :
    anzahlKurz (relaxSchritt p z b) < anzahlKurz p :=
  schrittAendertZahl p z (adressen p b) hne

/-- Fuelled relaxation: iterate until the step rests. -/
def relaxMitFuel : Nat → List RelaxStueck → List (Option Nat) → Nat →
    List RelaxStueck
  | 0, p, _, _ => p
  | f + 1, p, z, b =>
    if relaxSchritt p z b = p then p
    else relaxMitFuel f (relaxSchritt p z b) z b

/-- Fuelled iteration rests within the short-site count, only ever
    widening. The fuel hypothesis bounds the measure, the step
    hypothesis splits rest from progress. -/
theorem relaxKonvAux (f : Nat) (p : List RelaxStueck)
    (z : List (Option Nat)) (b : Nat)
    (hle : anzahlKurz p ≤ f) :
    relaxSchritt (relaxMitFuel f p z b) z b = relaxMitFuel f p z b ∧
    progLE p (relaxMitFuel f p z b) := by
  induction f generalizing p with
  | zero =>
    have h0 : anzahlKurz p = 0 := by omega
    have hfix : relaxSchritt p z b = p :=
      relaxSchrittOhneKurz p z b h0
    simp only [relaxMitFuel]
    exact ⟨hfix, progLE_refl p⟩
  | succ f ih =>
    by_cases hfix : relaxSchritt p z b = p
    · simp only [relaxMitFuel, if_pos hfix]
      exact ⟨hfix, progLE_refl p⟩
    · have hlt := relaxSchrittAendertZahl p z b hfix
      have hle2 : anzahlKurz (relaxSchritt p z b) ≤ f := by omega
      have ihc := ih (relaxSchritt p z b) hle2
      simp only [relaxMitFuel, if_neg hfix]
      exact ⟨ihc.1, progLE_trans (relaxSchritt_waechst p z b) ihc.2⟩

/-- CONVERGENCE (termination and fixed point): fuelled iteration
    with the short-site count as fuel rests at a widened program
    where every short site with a listed target fits signed-8 at its
    laid-out address. -/
theorem relaxKonvergiert (p : List RelaxStueck)
    (z : List (Option Nat)) (b : Nat) :
    ∃ q, relaxSchritt q z b = q ∧ progLE p q ∧
      ∀ (i : Nat) (t ad : Nat), q[i]? = some .kurz →
        z[i]? = some (some t) → (adressen q b)[i]? = some ad →
        rel8Passt (dispAn t ad 2) = true := by
  obtain ⟨hfix, hle⟩ :=
    relaxKonvAux (anzahlKurz p) p z b (by omega)
  refine ⟨relaxMitFuel (anzahlKurz p) p z b, hfix, hle, ?_⟩
  intro i t ad hs hz ha
  exact relaxSchritt_fixpunkt_passt _ _ _ hfix i t ad hs hz ha

/-! ## 4. The relaxed link closing: fall-through frame, exact
    site bytes, short read-back, long re-decode. -/

/-- EVERY SITE'S BYTES ARE EXACT: after a disjoint multi-operand
    closing, each operand's range carries exactly its operand bytes.
    The head case survives through `multiPatchAlle_kopf_stelle` with
    head-against-tail separation from the decided check (no diagonal
    needed); the tail case is the induction hypothesis on the
    remaining operands. -/
theorem relaxAlle_stelle (img : List Byte) (ops : List SchliessOp)
    (out : List Byte) (h : multiPatchAlle img ops = some out)
    (hdisj : opsDisjunktB ops = true)
    (op : SchliessOp) (hm : op ∈ ops)
    (k : Nat) (hk : k < opWeite op) :
    out[opStelle op + k]? = (multiBytes op.2)[k]? := by
  revert h hdisj hm hk
  induction ops generalizing img out op k with
  | nil =>
    intro h hdisj hm hk
    simp at hm
  | cons hd rest ih =>
    intro h hdisj hm hk
    simp only [opsDisjunktB, Bool.and_eq_true] at hdisj
    obtain ⟨hall, hrest⟩ := hdisj
    cases h1 : multiPatch img hd.1 hd.2 with
    | none =>
      have h2 := h
      simp only [multiPatchAlle, h1] at h2
      cases h2
    | some mid =>
      have htail : multiPatchAlle mid rest = some out := by
        have h2 := h
        simp only [multiPatchAlle, h1] at h2
        exact h2
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hmem
      · have hdis : ∀ op' ∈ rest, ∀ kk, kk < opWeite op →
            ∀ j, j < opWeite op' →
            opStelle op + kk ≠ opStelle op' + j := by
          intro op' hm' kk hkk j hj
          have hdec : decide (disjunktStellen (opStelle op)
              (opWeite op) (opStelle op') (opWeite op')) = true :=
            List.all_eq_true.mp hall op' hm'
          have hpair := of_decide_eq_true hdec
          simp only [disjunktStellen] at hpair
          omega
        exact multiPatchAlle_kopf_stelle img op rest out h hdis k hk
      · exact ih mid out op k htail hrest hmem hk

/-- **RELAXED LINK CORRECTNESS.** For a disjoint multi-operand
    closing over relaxed-program bytes: fall-through bytes (outside
    every operand) survive, the length is kept, every site's bytes
    are exact, and every short site reads back to its displacement.
    Every premise is used: `h` runs the frame, length and sites,
    `hdisj` orders the sites, `hfit8` rounds the short bytes back. -/
theorem relaxVerknuepft_korrekt (img out : List Byte)
    (ops : List SchliessOp)
    (h : multiPatchAlle img ops = some out)
    (hdisj : opsDisjunktB ops = true)
    (hfit8 : ∀ (off : Nat) (d : Int),
      (off, .rel8 d) ∈ ops → rel8Passt d = true) :
    (∀ i, (∀ op ∈ ops, ∀ kk, kk < opWeite op →
        i ≠ opStelle op + kk) → out[i]? = img[i]?) ∧
    out.length = img.length ∧
    (∀ op ∈ ops, ∀ kk, kk < opWeite op →
      out[opStelle op + kk]? = (multiBytes op.2)[kk]?) ∧
    (∀ (off : Nat) (d : Int), (off, .rel8 d) ∈ ops →
      out[off]? = some (rel8Byte d) ∧
      disp8Signed (rel8Byte d) = d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i haussen
    exact multiPatchAlle_rahmen img ops out h i haussen
  · exact multiPatchAlle_laenge img ops out h
  · intro op hm kk hk
    exact relaxAlle_stelle img ops out h hdisj op hm kk hk
  · intro off d hm
    have hfit := hfit8 off d hm
    have hfitI := rel8Passt_grenzen d hfit
    have hk : 0 < opWeite (off, .rel8 d) := by
      simp [opWeite, multiBytes]
    have hstelle :=
      relaxAlle_stelle img ops out h hdisj (off, .rel8 d) hm 0 hk
    have hbyte : out[off]? = some (rel8Byte d) := by
      simpa [opStelle, multiBytes] using hstelle
    exact ⟨hbyte, rel8Byte_rundgang d hfitI.1 hfitI.2⟩

/-- LONG-SITE RE-DECODE: a widened unconditional-jump site whose
    window carries the opcode and the displacement bytes, and which
    re-decodes to a five-byte jump, carries the relaxed displacement;
    the taken window re-decodes. Through the accepted window and
    agreement legs, never through decoder internals. -/
theorem relaxLang_dekodiert (out : List Byte) (ij : Nat) (disp : Int)
    (d : BitVec 32) (rest : List Byte)
    (hop : out[ij]? = some (natByte 233))
    (hfeld : ∀ kk, kk < 4 → out[ij + 1 + kk]? = (rel32Bytes disp)[kk]?)
    (hfit : rel32Passt disp = true)
    (hdec : decode (out.drop ij) = some ((⟨.jump32 d, 5⟩, rest))) :
    dispSigned d = disp ∧
    5 + rest.length = (out.drop ij).length ∧
    decktAb ⟨.jump32 d, 5⟩ ∧
    decode ((out.drop ij).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
  have htake := fenster_sprung out ij disp hop hfeld
  exact feld_agreement_sprung out ij disp d rest hfit htake hdec

end Gabbro.Grammatik.X86
