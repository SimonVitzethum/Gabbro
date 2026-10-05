/-
  File:      Grammatik/X86/HwBildFamilien.lean
  Subject:   Loaded-image fetch obstructions for all extension families.

  Lane 1179: follow-up of lane 1137 (`HwLoadedImage.lean`, merged), which
  pins only the narrow row as `fetchDekodiert`-refused while the Hw machine
  steps it (`hwBild_erweitert_ohne_pilot`). Here the same is stated and
  proved for muldiv, shift, setcc, cmov, fp and vec, then as ONE generic
  theorem over `ExtInstr` (every non-pilot family), plus the per-family
  fetch agreement on a checked mapping. Every accepted definition is
  reused unchanged; nothing is redefined here.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.Kern.Byteschritt
import Grammatik.X86.Kern.Bild
import Grammatik.X86.Laden.LoadedExecution
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.ExtendedExecution
import Grammatik.X86.Hw.Bild.HwLoadedImage
namespace Gabbro.Grammatik.X86

/-- A unified instruction is an extension row when it is no pilot row. -/
def istErweitert : ExtInstr → Prop
  | .pilot _ => False
  | _ => True

/-- Every extension row is non-pilot, by construction. -/
theorem istErweitert_nicht_pilot (i : ExtInstr) (d : Decodiert)
    (h : istErweitert i) (heq : i = .pilot d) : False := by
  cases i with
  | pilot _ => exact h
  | narrow _ => cases heq
  | muldiv _ => cases heq
  | shift _ => cases heq
  | setcc _ _ _ => cases heq
  | cmov _ _ _ _ => cases heq
  | fp _ => cases heq
  | vec _ => cases heq

/-- GENERIC DISPATCH INVERSION: any unified non-pilot outcome means the
    pilot decoder refuses. The first dispatch arm decides on `decode`
    alone, so every extension arm runs only under `decode = none`. -/
theorem decodeExt_nicht_pilot_zeigt_decode_none (bs : List Byte)
    (i : ExtInstr) (rest : List Byte)
    (h : decodeExt bs = some (i, rest))
    (hnp : ∀ d : Decodiert, i ≠ .pilot d) :
    decode bs = none := by
  cases hdec : decode bs with
  | some pr =>
    obtain ⟨d', rest'⟩ := pr
    have hde : decodeExt bs = some (.pilot d', rest') :=
      decodeExt_kanonisch bs d' rest' hdec
    rw [hde] at h
    have hi : i = .pilot d' := by cases h; rfl
    exact absurd hi (hnp d')
  | none => rfl

/-- GENERIC OBSTRUCTION: a fetched extension row has no `Byteschritt`
    counterpart -- the pilot fetch refuses while the Hw machine steps
    it. This subsumes the narrow-only `hwBild_erweitert_ohne_pilot`
    and needs no per-family copy. -/
theorem hwBildFamilien_erweitert_ohne_pilot (t : FpZustand)
    (i : ExtInstr) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (i, rest))
    (hnp : ∀ d : Decodiert, i ≠ .pilot d) :
    fetchDekodiert t.kern = none := by
  have herf := fetchExt_erfolg t _ _ _ hf
  have hd := decodeExt_nicht_pilot_zeigt_decode_none _ _ _ herf.1 hnp
  unfold fetchDekodiert
  simp [hd]

/-! ## Per-family obstructions: thin corollaries of the generic one.

  Each states what lane 1137 states for narrow: the fetched row steps
  the Hw machine (`stepExt` selection, reused by name) while the pilot
  fetch `fetchDekodiert` refuses. No proof is copied; every corollary
  applies the generic theorem with its constructor inequality. -/

/-- OBSTRUCTION (muldiv): a fetched multiply/divide row refuses the pilot. -/
theorem hwBildFamilien_muldiv_ohne_pilot (t : FpZustand)
    (mm : MulDivDecodiert) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.muldiv mm, rest)) :
    fetchDekodiert t.kern = none :=
  hwBildFamilien_erweitert_ohne_pilot t (.muldiv mm) rest hf
    (fun d h => by cases h)

/-- OBSTRUCTION (shift): a fetched shift row refuses the pilot. -/
theorem hwBildFamilien_shift_ohne_pilot (t : FpZustand)
    (d : ShiftDecodiert) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.shift d, rest)) :
    fetchDekodiert t.kern = none :=
  hwBildFamilien_erweitert_ohne_pilot t (.shift d) rest hf
    (fun c h => by cases h)

/-- OBSTRUCTION (setcc): a fetched SETcc row refuses the pilot. -/
theorem hwBildFamilien_setcc_ohne_pilot (t : FpZustand)
    (c : Bedingung) (dst : Register) (l : Nat) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.setcc c dst l, rest)) :
    fetchDekodiert t.kern = none :=
  hwBildFamilien_erweitert_ohne_pilot t (.setcc c dst l) rest hf
    (fun d h => by cases h)

/-- OBSTRUCTION (cmov): a fetched CMOVcc row refuses the pilot. -/
theorem hwBildFamilien_cmov_ohne_pilot (t : FpZustand)
    (c : Bedingung) (dst src : Register) (l : Nat) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.cmov c dst src l, rest)) :
    fetchDekodiert t.kern = none :=
  hwBildFamilien_erweitert_ohne_pilot t (.cmov c dst src l) rest hf
    (fun d h => by cases h)

/-- OBSTRUCTION (fp): a fetched scalar-FP row refuses the pilot. -/
theorem hwBildFamilien_fp_ohne_pilot (t : FpZustand)
    (f : FpDecodiert) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.fp f, rest)) :
    fetchDekodiert t.kern = none :=
  hwBildFamilien_erweitert_ohne_pilot t (.fp f) rest hf
    (fun d h => by cases h)

/-- OBSTRUCTION (vec): a fetched packed-integer row refuses the pilot. -/
theorem hwBildFamilien_vec_ohne_pilot (t : FpZustand)
    (v : VectorDec) (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.vec v, rest)) :
    fetchDekodiert t.kern = none :=
  hwBildFamilien_erweitert_ohne_pilot t (.vec v) rest hf
    (fun d h => by cases h)

/-! ## Per-family fetch lifting on the core projection.

  Each mirrors `hwBild_fetchExt_pilot`: a checked family
  fetch-decoding (decoder success through the exact fallback chain,
  length equation, length guard, execute permission of the consumed
  prefix) is a unified `fetchExt` fetch on the Hw core projection.
  The old decoders are lifted, never redefined. -/

/-- FETCH LIFTING (muldiv): a checked multiply/divide decoding is fetched. -/
theorem hwBildFamilien_fetch_muldiv (m : HwMaschine) (c : Nat)
    (mm : MulDivDecodiert) (rest : List Byte)
    (h1 : decode (geholt (projZustand m c)) = none)
    (h2 : decodeNarrow (geholt (projZustand m c)) = none)
    (h3 : decodeMulDiv (geholt (projZustand m c)) = some (mm, rest))
    (hsum : mm.laenge + rest.length = (geholt (projZustand m c)).length)
    (hok : laengeOk mm.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip mm.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.muldiv mm, rest) := by
  have hde := decodeExt_muldiv (geholt (projZustand m c)) mm rest h1 h2 h3
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.muldiv mm) rest = true := by
    have e1 : decide (extLen (.muldiv mm) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.muldiv mm)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip (extLen (.muldiv mm)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-- FETCH LIFTING (shift): a checked shift decoding is fetched. -/
theorem hwBildFamilien_fetch_shift (m : HwMaschine) (c : Nat)
    (f : ShiftForm) (rest : List Byte)
    (h1 : decode (geholt (projZustand m c)) = none)
    (h2 : decodeNarrow (geholt (projZustand m c)) = none)
    (h3 : decodeMulDiv (geholt (projZustand m c)) = none)
    (h4 : decodeShift (geholt (projZustand m c)) = some (f, rest))
    (hsum : shiftLaenge f + rest.length =
      (geholt (projZustand m c)).length)
    (hok : laengeOk (shiftLaenge f) = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip (shiftLaenge f) = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.shift ⟨f, shiftLaenge f⟩, rest) := by
  have hde := decodeExt_shift (geholt (projZustand m c)) f rest h1 h2 h3 h4
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.shift ⟨f, shiftLaenge f⟩) rest = true := by
    have e1 : decide (extLen (.shift ⟨f, shiftLaenge f⟩) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.shift ⟨f, shiftLaenge f⟩)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip
        (extLen (.shift ⟨f, shiftLaenge f⟩)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-- FETCH LIFTING (setcc): a checked SETcc decoding is fetched. -/
theorem hwBildFamilien_fetch_setcc (m : HwMaschine) (c : Nat)
    (cc : Bedingung) (dst : Register) (rest : List Byte)
    (h1 : decode (geholt (projZustand m c)) = none)
    (h2 : decodeNarrow (geholt (projZustand m c)) = none)
    (h3 : decodeMulDiv (geholt (projZustand m c)) = none)
    (h4 : decodeShift (geholt (projZustand m c)) = none)
    (h5 : decodeSetCC (geholt (projZustand m c)) =
      some ((cc, dst), rest))
    (hsum : 4 + rest.length = (geholt (projZustand m c)).length)
    (hok : laengeOk 4 = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip 4 = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.setcc cc dst 4, rest) := by
  have hde := decodeExt_setcc (geholt (projZustand m c)) cc dst rest
    h1 h2 h3 h4 h5
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.setcc cc dst 4) rest = true := by
    have e1 : decide (extLen (.setcc cc dst 4) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.setcc cc dst 4)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip (extLen (.setcc cc dst 4)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-- FETCH LIFTING (cmov): a checked CMOVcc decoding is fetched. -/
theorem hwBildFamilien_fetch_cmov (m : HwMaschine) (c : Nat)
    (cc : Bedingung) (dst src : Register) (rest : List Byte)
    (h1 : decode (geholt (projZustand m c)) = none)
    (h2 : decodeNarrow (geholt (projZustand m c)) = none)
    (h3 : decodeMulDiv (geholt (projZustand m c)) = none)
    (h4 : decodeShift (geholt (projZustand m c)) = none)
    (h5 : decodeSetCC (geholt (projZustand m c)) = none)
    (h6 : decodeCmov (geholt (projZustand m c)) =
      some ((cc, dst, src), rest))
    (hsum : 4 + rest.length = (geholt (projZustand m c)).length)
    (hok : laengeOk 4 = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip 4 = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.cmov cc dst src 4, rest) := by
  have hde := decodeExt_cmov (geholt (projZustand m c)) cc dst src rest
    h1 h2 h3 h4 h5 h6
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.cmov cc dst src 4) rest = true := by
    have e1 : decide (extLen (.cmov cc dst src 4) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.cmov cc dst src 4)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip (extLen (.cmov cc dst src 4)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-- FETCH LIFTING (fp): a checked scalar-FP decoding is fetched. -/
theorem hwBildFamilien_fetch_fp (m : HwMaschine) (c : Nat)
    (f : FpDecodiert) (rest : List Byte)
    (h1 : decode (geholt (projZustand m c)) = none)
    (h2 : decodeNarrow (geholt (projZustand m c)) = none)
    (h3 : decodeMulDiv (geholt (projZustand m c)) = none)
    (h4 : decodeShift (geholt (projZustand m c)) = none)
    (h5 : decodeSetCC (geholt (projZustand m c)) = none)
    (h6 : decodeCmov (geholt (projZustand m c)) = none)
    (h7 : fpDecode (geholt (projZustand m c)) = some (f, rest))
    (hsum : f.laenge + rest.length = (geholt (projZustand m c)).length)
    (hok : laengeOk f.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip f.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.fp f, rest) := by
  have hde := decodeExt_fp (geholt (projZustand m c)) f rest
    h1 h2 h3 h4 h5 h6 h7
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.fp f) rest = true := by
    have e1 : decide (extLen (.fp f) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.fp f)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip (extLen (.fp f)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-- FETCH LIFTING (vec): a checked packed-integer decoding is fetched. -/
theorem hwBildFamilien_fetch_vec (m : HwMaschine) (c : Nat)
    (v : VectorDec) (rest : List Byte)
    (h1 : decode (geholt (projZustand m c)) = none)
    (h2 : decodeNarrow (geholt (projZustand m c)) = none)
    (h3 : decodeMulDiv (geholt (projZustand m c)) = none)
    (h4 : decodeShift (geholt (projZustand m c)) = none)
    (h5 : decodeSetCC (geholt (projZustand m c)) = none)
    (h6 : decodeCmov (geholt (projZustand m c)) = none)
    (h7 : fpDecode (geholt (projZustand m c)) = none)
    (h8 : decodeVector (geholt (projZustand m c)) = some (v, rest))
    (hsum : v.laenge + rest.length = (geholt (projZustand m c)).length)
    (hok : laengeOk v.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip v.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.vec v, rest) := by
  have hde := decodeExt_vec (geholt (projZustand m c)) v rest
    h1 h2 h3 h4 h5 h6 h7 h8
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.vec v) rest = true := by
    have e1 : decide (extLen (.vec v) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.vec v)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip (extLen (.vec v)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-! ## Loaded-image fetch agreement per family.

  Under memory coincidence and core agreement the core projection IS
  the loaded image state (`hwBild_zustand_gleich`, `hwBild_geholt_gleich`,
  both reused). Each theorem below moves the decoder premises from the
  image window to the core window and applies the §2 lifting: what the
  loaded image decodes as an extension row, the Hw core fetches as that
  row. Byte provenance from the checked map is inherited from
  `hwBild_geholt_aus_datei` (cited, not repeated). -/

/-- LOADED-FETCH AGREEMENT (muldiv): the image row is the core fetch. -/
theorem hwBildFamilien_muldiv_bild (m : HwMaschine) (c : Nat)
    (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags)
    (mm : MulDivDecodiert) (rest : List Byte)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl)
    (h1 : decode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h2 : decodeNarrow (geholt (bildZustand bild bias rip reg fl)) = none)
    (h3 : decodeMulDiv (geholt (bildZustand bild bias rip reg fl)) =
      some (mm, rest))
    (hsum : mm.laenge + rest.length =
      (geholt (bildZustand bild bias rip reg fl)).length)
    (hok : laengeOk mm.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip mm.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.muldiv mm, rest) := by
  have hg := hwBild_geholt_gleich m c bild bias rip reg fl
    hmem hrip hreg hfl
  rw [←hg] at h1 h2 h3 hsum
  exact hwBildFamilien_fetch_muldiv m c mm rest h1 h2 h3 hsum hok hexe

/-- LOADED-FETCH AGREEMENT (shift): the image row is the core fetch. -/
theorem hwBildFamilien_shift_bild (m : HwMaschine) (c : Nat)
    (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags)
    (f : ShiftForm) (rest : List Byte)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl)
    (h1 : decode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h2 : decodeNarrow (geholt (bildZustand bild bias rip reg fl)) = none)
    (h3 : decodeMulDiv (geholt (bildZustand bild bias rip reg fl)) = none)
    (h4 : decodeShift (geholt (bildZustand bild bias rip reg fl)) =
      some (f, rest))
    (hsum : shiftLaenge f + rest.length =
      (geholt (bildZustand bild bias rip reg fl)).length)
    (hok : laengeOk (shiftLaenge f) = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip (shiftLaenge f) = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.shift ⟨f, shiftLaenge f⟩, rest) := by
  have hg := hwBild_geholt_gleich m c bild bias rip reg fl
    hmem hrip hreg hfl
  rw [←hg] at h1 h2 h3 h4 hsum
  exact hwBildFamilien_fetch_shift m c f rest h1 h2 h3 h4 hsum hok hexe

/-- LOADED-FETCH AGREEMENT (setcc): the image row is the core fetch. -/
theorem hwBildFamilien_setcc_bild (m : HwMaschine) (c : Nat)
    (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags)
    (cc : Bedingung) (dst : Register) (rest : List Byte)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl)
    (h1 : decode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h2 : decodeNarrow (geholt (bildZustand bild bias rip reg fl)) = none)
    (h3 : decodeMulDiv (geholt (bildZustand bild bias rip reg fl)) = none)
    (h4 : decodeShift (geholt (bildZustand bild bias rip reg fl)) = none)
    (h5 : decodeSetCC (geholt (bildZustand bild bias rip reg fl)) =
      some ((cc, dst), rest))
    (hsum : 4 + rest.length =
      (geholt (bildZustand bild bias rip reg fl)).length)
    (hok : laengeOk 4 = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip 4 = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.setcc cc dst 4, rest) := by
  have hg := hwBild_geholt_gleich m c bild bias rip reg fl
    hmem hrip hreg hfl
  rw [←hg] at h1 h2 h3 h4 h5 hsum
  exact hwBildFamilien_fetch_setcc m c cc dst rest
    h1 h2 h3 h4 h5 hsum hok hexe

/-- LOADED-FETCH AGREEMENT (cmov): the image row is the core fetch. -/
theorem hwBildFamilien_cmov_bild (m : HwMaschine) (c : Nat)
    (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags)
    (cc : Bedingung) (dst src : Register) (rest : List Byte)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl)
    (h1 : decode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h2 : decodeNarrow (geholt (bildZustand bild bias rip reg fl)) = none)
    (h3 : decodeMulDiv (geholt (bildZustand bild bias rip reg fl)) = none)
    (h4 : decodeShift (geholt (bildZustand bild bias rip reg fl)) = none)
    (h5 : decodeSetCC (geholt (bildZustand bild bias rip reg fl)) = none)
    (h6 : decodeCmov (geholt (bildZustand bild bias rip reg fl)) =
      some ((cc, dst, src), rest))
    (hsum : 4 + rest.length =
      (geholt (bildZustand bild bias rip reg fl)).length)
    (hok : laengeOk 4 = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip 4 = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.cmov cc dst src 4, rest) := by
  have hg := hwBild_geholt_gleich m c bild bias rip reg fl
    hmem hrip hreg hfl
  rw [←hg] at h1 h2 h3 h4 h5 h6 hsum
  exact hwBildFamilien_fetch_cmov m c cc dst src rest
    h1 h2 h3 h4 h5 h6 hsum hok hexe

/-- LOADED-FETCH AGREEMENT (fp): the image row is the core fetch. -/
theorem hwBildFamilien_fp_bild (m : HwMaschine) (c : Nat)
    (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags)
    (f : FpDecodiert) (rest : List Byte)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl)
    (h1 : decode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h2 : decodeNarrow (geholt (bildZustand bild bias rip reg fl)) = none)
    (h3 : decodeMulDiv (geholt (bildZustand bild bias rip reg fl)) = none)
    (h4 : decodeShift (geholt (bildZustand bild bias rip reg fl)) = none)
    (h5 : decodeSetCC (geholt (bildZustand bild bias rip reg fl)) = none)
    (h6 : decodeCmov (geholt (bildZustand bild bias rip reg fl)) = none)
    (h7 : fpDecode (geholt (bildZustand bild bias rip reg fl)) =
      some (f, rest))
    (hsum : f.laenge + rest.length =
      (geholt (bildZustand bild bias rip reg fl)).length)
    (hok : laengeOk f.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip f.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.fp f, rest) := by
  have hg := hwBild_geholt_gleich m c bild bias rip reg fl
    hmem hrip hreg hfl
  rw [←hg] at h1 h2 h3 h4 h5 h6 h7 hsum
  exact hwBildFamilien_fetch_fp m c f rest
    h1 h2 h3 h4 h5 h6 h7 hsum hok hexe

/-- LOADED-FETCH AGREEMENT (vec): the image row is the core fetch. -/
theorem hwBildFamilien_vec_bild (m : HwMaschine) (c : Nat)
    (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags)
    (v : VectorDec) (rest : List Byte)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl)
    (h1 : decode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h2 : decodeNarrow (geholt (bildZustand bild bias rip reg fl)) = none)
    (h3 : decodeMulDiv (geholt (bildZustand bild bias rip reg fl)) = none)
    (h4 : decodeShift (geholt (bildZustand bild bias rip reg fl)) = none)
    (h5 : decodeSetCC (geholt (bildZustand bild bias rip reg fl)) = none)
    (h6 : decodeCmov (geholt (bildZustand bild bias rip reg fl)) = none)
    (h7 : fpDecode (geholt (bildZustand bild bias rip reg fl)) = none)
    (h8 : decodeVector (geholt (bildZustand bild bias rip reg fl)) =
      some (v, rest))
    (hsum : v.laenge + rest.length =
      (geholt (bildZustand bild bias rip reg fl)).length)
    (hok : laengeOk v.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip v.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.vec v, rest) := by
  have hg := hwBild_geholt_gleich m c bild bias rip reg fl
    hmem hrip hreg hfl
  rw [←hg] at h1 h2 h3 h4 h5 h6 h7 h8 hsum
  exact hwBildFamilien_fetch_vec m c v rest
    h1 h2 h3 h4 h5 h6 h7 h8 hsum hok hexe

/-! ## Well-formedness and the joint witness. -/

/-- WELL-FORMEDNESS SURVIVES: every Hw step of the family machine keeps
    the checked core/control profile (lifts `hwSchritt_wf`, as in
    lane 1137; the family adapters admit through `adapterBild`, whose
    per-instruction agreement is reused by name). -/
theorem hwBildFamilien_schritt_wf (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) (hwf : HwWf m) : HwWf m' :=
  hwSchritt_wf m m' e h hwf

/-- JOINT WITNESS: all six extension rows decode through the unified
    decoder exactly once, and the pilot refuses every one of them.
    Non-degenerate: six distinct real byte rows (the accepted pins),
    each with its pilot refusal beside it. The reached two-core
    memory-changing run (forwarding, drain 0 to 42) is inherited from
    `hwBild_zeuge` (lane 1137), cited here and not duplicated. -/
theorem hwBildFamilien_zeuge :
    decodeExt (encodeNarrow (.mov32rr .rax .rcx)) =
      some (.narrow ⟨.mov32rr .rax .rcx, 3⟩, []) ∧
    decodeExt (mulDivEncode (.mulRax .rcx)) =
      some (.muldiv ⟨.mulRax .rcx, 3⟩, []) ∧
    decodeExt (encodeShift (.imm .shl .rax 1)) =
      some (.shift ⟨.imm .shl .rax 1, 4⟩, []) ∧
    decodeExt (encodeSetCC .e .rax) =
      some (.setcc .e .rax 4, []) ∧
    decodeExt (encodeCmov .e .rax .rcx) =
      some (.cmov .e .rax .rcx 4, []) ∧
    decodeExt (fpEncodeMovsdRR .xmm0 .xmm1) =
      some (.fp ⟨.movsdRR .xmm0 .xmm1, 4⟩, []) ∧
    decodeExt (encodeVector (.pxorRR .xmm0 .xmm1)) =
      some (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩, []) ∧
    decode (encodeNarrow (.mov32rr .rax .rcx)) = none ∧
    decode (mulDivEncode (.mulRax .rcx)) = none ∧
    decode (encodeShift (.imm .shl .rax 1)) = none ∧
    decode (encodeSetCC .e .rax) = none ∧
    decode (encodeCmov .e .rax .rcx) = none ∧
    decode (fpEncodeMovsdRR .xmm0 .xmm1) = none ∧
    decode (encodeVector (.pxorRR .xmm0 .xmm1)) = none := by
  exact ⟨pin_ext_narrow_mov32, pin_ext_muldiv_mul, pin_ext_shift_shl,
    pin_ext_setcc, pin_ext_cmov, pin_ext_fp_movsd, pin_ext_vec_pxor,
    pin_pilot_weist_narrow_zurueck, pin_pilot_weist_muldiv_zurueck,
    pin_pilot_weist_shift_zurueck, pin_pilot_weist_setcc_zurueck,
    pin_pilot_weist_cmov_zurueck, pin_pilot_weist_fp_zurueck,
    pin_pilot_weist_vec_zurueck⟩

/- CUTS:
   Proved here, reusing every accepted definition unchanged (no second
   decoder, evaluator, loader or ISA model):
   - generic dispatch inversion (`decodeExt_nicht_pilot_zeigt_decode_none`):
     any unified non-pilot outcome means the pilot refuses;
   - generic obstruction (`hwBildFamilien_erweitert_ohne_pilot`): a fetched
     extension row refuses `fetchDekodiert` while the Hw machine steps it;
   - six per-family obstruction corollaries (muldiv, shift, setcc, cmov,
     fp, vec), each a one-line application of the generic theorem;
   - six per-family fetch liftings on the core projection (the checked
     decoder chain plus length equation, length guard and execute
     permission give a unified `fetchExt` fetch);
   - six loaded-image fetch agreements (image-window premises moved to
     the core window via `hwBild_geholt_gleich`);
   - well-formedness survival (`hwBildFamilien_schritt_wf`);
   - a joint witness over six distinct real byte rows with their pilot
     refusals (`hwBildFamilien_zeuge`).
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted canonical
     subsets with self-consistency only, not x86 truth. Silicon/timing
     assumptions: none beyond the accepted lemmas reused by name.
   - No per-access target-to-W/GX simulation and no whole-word atomicity
     beyond the reused guards; the TSO/memory run is inherited from
     `hwBild_zeuge`, not re-established per family here.
   - No source/IR/ABI/loader/entry/budget link; no LOCK RMW path;
     `verweigert` is the absence of a transition, never normal program
     termination.
   - The full bridge to W/GX is not claimed.
-/

#print axioms decodeExt_nicht_pilot_zeigt_decode_none
#print axioms hwBildFamilien_erweitert_ohne_pilot
#print axioms hwBildFamilien_muldiv_ohne_pilot
#print axioms hwBildFamilien_shift_ohne_pilot
#print axioms hwBildFamilien_setcc_ohne_pilot
#print axioms hwBildFamilien_cmov_ohne_pilot
#print axioms hwBildFamilien_fp_ohne_pilot
#print axioms hwBildFamilien_vec_ohne_pilot
#print axioms hwBildFamilien_fetch_muldiv
#print axioms hwBildFamilien_fetch_shift
#print axioms hwBildFamilien_fetch_setcc
#print axioms hwBildFamilien_fetch_cmov
#print axioms hwBildFamilien_fetch_fp
#print axioms hwBildFamilien_fetch_vec
#print axioms hwBildFamilien_muldiv_bild
#print axioms hwBildFamilien_shift_bild
#print axioms hwBildFamilien_setcc_bild
#print axioms hwBildFamilien_cmov_bild
#print axioms hwBildFamilien_fp_bild
#print axioms hwBildFamilien_vec_bild
#print axioms hwBildFamilien_schritt_wf
#print axioms hwBildFamilien_zeuge

end Gabbro.Grammatik.X86
