/-
  File:      Grammatik/X86/FloatValidatorAdmission.lean
  Subject:   Optional strengthened FP validator admission over loaded bytes.

  Lane 658: an independent optional admission for actual loaded scalar
  MOVSD/ADDSD bytes, binding the accepted opcode subset/profile/MXCSR
  (`ScalarFloatCodec`: `fpDecode`/`fpFetchDekodiert`/`fpByteschritt`;
  `ScalarFloat`: `fpSchritt`/`fpEintritt`), the entry control-state
  discipline (`FloatEntryState`: `mxcsrOk`/`eintrittFp`), the checked
  image mapping (`Bild`: `wohlgeformt`/`eintragEnthalten`/
  `ladenAusfuehrbar`/`geladen`) and loaded execution
  (`LoadedExecution`: `bildZustand`). The decoded form is derived from
  loaded bytes, never assumed from the caller; soundness implies a real
  `fpByteschritt` consequence and preserves entry/control/byte mapping
  observations. No new executor: the shared `FpZustand`/`fpByteschritt`
  interface is reused untouched. Finite source observations are reused
  from `FloatSourceObservations` only where their predicates establish
  them; no full-IEEE claim is made.
-/
import Grammatik.X86.ScalarFloatCodec
import Grammatik.X86.FloatEntryState
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.LoadedExecution
import Grammatik.X86.FloatSourceObservations

namespace Gabbro.Grammatik.X86

/-- Loaded FP state at a biased entry: registers/flags are caller-chosen,
    memory is the canonically loaded image, XMM/MXCSR ride along. -/
def fpBildT (bild : Bild) (bias e : Nat) (reg : Register → Wort)
    (fl : Flags) (xmm : XmmDatei) (k : FPKontext) : FpZustand :=
  ⟨bildZustand bild bias (BitVec.ofNat 64 e) reg fl, xmm, k⟩

/-- Strengthened FP entry admission (OPTIONAL, new): checked image
    mapping AND entry containment AND an executable byte at the entry
    AND a successful fetch-and-decode of actual loaded scalar FP bytes
    AND the MXCSR profile admission AND the entry control-state
    discipline with the control word bound to the entry word. -/
def valFpEintrittStark (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand) : Bool :=
  wohlgeformt p bild &&
  eintragEnthalten bias bild.abschnitte e &&
  ladenAusfuehrbar bild bias e &&
  (fpFetchDekodiert (fpBildT bild bias e reg fl xmm k)).isSome &&
  (fpEintritt k && (mxcsrOk z && decide (k.mxcsr = z.mxcsr)))

/-- The strengthened FP check implies the checked image mapping. -/
theorem valFp_wohlgeformt (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    wohlgeformt p bild = true := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1.1.1

/-- The strengthened FP check implies entry containment. -/
theorem valFp_eintrag (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    eintragEnthalten bias bild.abschnitte e = true := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1.1.2

/-- The strengthened FP check implies an executable byte at the entry. -/
theorem valFp_ausfuehrbar (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    ladenAusfuehrbar bild bias e = true := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1.2

/-- The strengthened FP check implies a successful fetch-and-decode
    of actual loaded scalar FP bytes at the entry state. -/
theorem valFp_fetch_exist (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    ∃ (d : FpDecodiert) (rest : List Byte),
      fpFetchDekodiert (fpBildT bild bias e reg fl xmm k) =
        some (d, rest) := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, hfetch⟩, _⟩ := h
  have hne : fpFetchDekodiert (fpBildT bild bias e reg fl xmm k) ≠ none := by
    intro hcontra
    simp [hcontra] at hfetch
  rw [Option.ne_none_iff_exists'] at hne
  obtain ⟨pr, hpr⟩ := hne
  cases pr with
  | mk d rest =>
    exact ⟨d, rest, hpr⟩

/-- The strengthened FP check implies the MXCSR profile admission. -/
theorem valFp_fpEintritt (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    fpEintritt k = true := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.2.1

/-- The strengthened FP check implies the entry control-state
    discipline. -/
theorem valFp_mxcsrOk (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    mxcsrOk z = true := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.2.2.1

/-- The strengthened FP check binds the control word to the entry
    word: a forged entry (a control word the entry never established)
    admits nothing. -/
theorem valFp_kontext (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    k.mxcsr = z.mxcsr := by
  unfold valFpEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.2.2.2

/-- The strengthened FP check readies the scalar-double feature:
    with OS vector state on, `bereit` holds at `.sseDoppel`. -/
theorem valFp_gibt_bereit (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    bereit ⟨k.mxcsr, true⟩ .sseDoppel = true := by
  have hg : fpEintritt k = true := valFp_fpEintritt p bild bias e reg fl xmm k z h
  unfold fpEintritt at hg
  unfold bereit
  simp [hg]

/-- ENTRY-AT-DECODED-START (generic soundness): from the strengthened
    FP check, the entry is contained in an executable section, an
    executable byte sits at the entry, and the actual fetched bytes at
    the loaded FP entry state decode to a canonical scalar FP form at
    its exact length, with the consumed prefix executable. The decode
    is derived from the real validator premise through the actual
    fetch, never assumed. -/
theorem valFp_gibt_bytes (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true) :
    eintragEnthalten bias bild.abschnitte e = true ∧
    ladenAusfuehrbar bild bias e = true ∧
    ∃ (d : FpDecodiert) (rest : List Byte),
      fpFetchDekodiert (fpBildT bild bias e reg fl xmm k) =
        some (d, rest) ∧
      fpDecode (fpGeholt (fpBildT bild bias e reg fl xmm k)) =
        some (d, rest) ∧
      d.laenge + rest.length =
        (fpGeholt (fpBildT bild bias e reg fl xmm k)).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN (fpBildT bild bias e reg fl xmm k).kern.speicher
        (fpBildT bild bias e reg fl xmm k).kern.rip d.laenge = true ∧
      bereit ⟨k.mxcsr, true⟩ .sseDoppel = true := by
  obtain ⟨d, rest, hf⟩ := valFp_fetch_exist p bild bias e reg fl xmm k z h
  have hdec := fpFetchDekodiert_erfolg _ d rest hf
  exact ⟨valFp_eintrag p bild bias e reg fl xmm k z h,
    valFp_ausfuehrbar p bild bias e reg fl xmm k z h,
    d, rest, hf, hdec.1, hdec.2.1, hdec.2.2.1, hdec.2.2.2,
    valFp_gibt_bereit p bild bias e reg fl xmm k z h⟩

/-- LOADED-STEP CONSEQUENCE (generic soundness): from the
    strengthened FP check, the fetched scalar FP instruction at the
    loaded entry state takes the same byte step as the accepted
    executor, and the successor keeps the admitted control word while
    the checked mapping, entry containment and execute permission
    stay put. Where the validator premise holds, loaded bytes and the
    decoded step agree; refusal shapes stay refusals. -/
theorem valFp_schritt (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) (xmm : XmmDatei) (k : FPKontext)
    (z : EintrittZustand)
    (h : valFpEintrittStark p bild bias e reg fl xmm k z = true)
    (d : FpDecodiert) (rest : List Byte)
    (hf : fpFetchDekodiert (fpBildT bild bias e reg fl xmm k) =
      some (d, rest))
    (t' : FpZustand)
    (hs : fpSchritt d (fpBildT bild bias e reg fl xmm k) = some t') :
    fpByteschritt (fpBildT bild bias e reg fl xmm k) = .weiter t' ∧
    t'.fp = k ∧
    wohlgeformt p bild = true ∧
    eintragEnthalten bias bild.abschnitte e = true ∧
    ladenAusfuehrbar bild bias e = true := by
  have hstep : fpByteschritt (fpBildT bild bias e reg fl xmm k) =
      .weiter t' := by
    unfold fpByteschritt
    rw [hf]
    simp only
    rw [hs]
  have hfp : t'.fp = k := by
    have hkeep := fpSchritt_erhaelt_fp d _ t' hs
    exact hkeep
  exact ⟨hstep, hfp,
    valFp_wohlgeformt p bild bias e reg fl xmm k z h,
    valFp_eintrag p bild bias e reg fl xmm k z h,
    valFp_ausfuehrbar p bild bias e reg fl xmm k z h⟩

/-! ## Witness image: a loaded MOVSD store of `+∞`.

  Code section holds the canonical eight store bytes
  (`MOVSD [rbx+0], xmm0`); the data section at `0x2000` is
  readable/writable, never executable. `rbx` points at the data
  section, `xmm0` holds `+∞` low, the control word is reset, and the
  entry binds that same word under the validated-save discipline. -/

/-- Witness code section: eight file bytes, executable, never
    writable (W^X), alignment 4096 divides the base. -/
def fpStoreCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 8, vaddr := 0x1000, memLen := 8,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Witness data section: eight file bytes, readable and writable,
    never executable. -/
def fpStoreDaten : Abschnitt :=
  { dateiOff := 8, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- Witness image: store bytes plus eight data zeros, entry at the
    code base, fixed mode. -/
def fpStoreBild : Bild :=
  { datei := fpEncodeMovsdSpeichere .rbx .xmm0 0 ++ List.replicate 8 (natByte 0)
    abschnitte := [fpStoreCode, fpStoreDaten]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- Witness registers: `rbx` points at the data section. -/
def fpStoreReg : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 0x2000 else BitVec.ofNat 64 0

/-- Witness XMM file: `xmm0` holds `+∞` low, every other register zero. -/
def fpStoreXmm : XmmDatei :=
  fun q => if q = XmmReg.xmm0 then vecJoin 0x7FF0000000000000 0 else vecJoin 0 0

/-- Witness control word: reset (admitted profile). -/
def fpStoreK : FPKontext := kontextReset

/-- Witness entry: XMM touched, save validated, reset word. -/
def fpStoreZ : EintrittZustand :=
  { zustand := fpZeugeKern
    mxcsr := 0x1F80
    xmmBeruehrt := true
    mxcsrGesichert := true
    ifBit := true
    guardOk := true }

/-- Witness loaded FP state at the biased entry. -/
def fpStoreT : FpZustand :=
  fpBildT fpStoreBild 0 0x1000 fpStoreReg storeFlags fpStoreXmm fpStoreK

/-- The witness store encoding is eight bytes long. -/
theorem fpStoreInstr_laenge :
    (fpEncodeMovsdSpeichere .rbx .xmm0 0).length = 8 := by
  decide

/-- ACCEPTANCE: the witness image validates under profile 48. -/
theorem fpStore_wohlgeformt :
    wohlgeformt .p48 fpStoreBild = true := by
  decide

/-- Fetch from the actual loaded store bytes yields the store form
    with no remainder: the eight executable bytes are exactly the
    instruction, the data section is not executable. -/
theorem fpStore_fetch :
    fpFetchDekodiert fpStoreT =
      some (⟨.movsdSpeichere .rbx .xmm0 0, 8⟩, []) := by
  decide

/-- ACCEPTANCE: the witness entry passes the strengthened FP check. -/
theorem fpStore_ok :
    valFpEintrittStark .p48 fpStoreBild 0 0x1000 fpStoreReg storeFlags
      fpStoreXmm fpStoreK fpStoreZ = true := by
  decide

/-- Witness memory after the store: `+∞` at `0x2000`. -/
def fpStoreSpeicherNach : Speicher :=
  { geladen fpStoreBild 0 with
    bytes := writeBytes (geladen fpStoreBild 0) (BitVec.ofNat 64 0x2000)
      0x7FF0000000000000 }

/-- Witness state after the store. -/
def fpStoreT2 : FpZustand :=
  { fpStoreT with kern := { fpStoreT.kern with speicher := fpStoreSpeicherNach, rip := ripNach fpStoreT.kern.rip 8 } }

/-- The witness `xmm0` holds `+∞` low. -/
theorem fpStoreTief0 :
    xmmTief fpStoreT.xmm XmmReg.xmm0 = 0x7FF0000000000000 := by
  decide

/-- The witness store address: `rbx + 0` is `0x2000`. -/
theorem fpStoreEffAddr :
    effAddr fpStoreT.kern Register.rbx 0 = BitVec.ofNat 64 0x2000 := by
  decide

/-- The store goes through: `+∞` lands at `0x2000`. -/
theorem fpStore_schreib :
    write64 fpStoreT.kern.speicher (effAddr fpStoreT.kern Register.rbx 0)
      (xmmTief fpStoreT.xmm XmmReg.xmm0) = some fpStoreSpeicherNach := by
  rw [fpStoreEffAddr, fpStoreTief0]
  have hc : schreibbar8 fpStoreT.kern.speicher (BitVec.ofNat 64 0x2000) =
      true := by
    decide
  unfold write64
  rw [if_pos hc]
  rfl

/-- The reached byte-step: actual loaded bytes store `xmm0` to `[rbx]`. -/
theorem fpStore_schritt :
    fpByteschritt fpStoreT = .weiter fpStoreT2 := by
  unfold fpByteschritt
  rw [fpStore_fetch]
  simp only
  have hs := fpSchritt_movsdSpeichere_erfolg
    ⟨.movsdSpeichere .rbx .xmm0 0, 8⟩ fpStoreT .rbx .xmm0 0
    fpStoreSpeicherNach
    (by decide : laengeOk 8 = true)
    (by decide : fpEintritt fpStoreT.fp = true)
    rfl fpStore_schreib
  simp only [hs, fpStoreT2]

/-- The stored word reads back: `+∞` at `0x2000`. -/
theorem fpStore_liest :
    read64 fpStoreT2.kern.speicher (BitVec.ofNat 64 0x2000) =
      some 0x7FF0000000000000 := by
  have hwr : write64 fpStoreT.kern.speicher (BitVec.ofNat 64 0x2000)
      0x7FF0000000000000 = some fpStoreSpeicherNach := by
    have h := fpStore_schreib
    rw [fpStoreEffAddr, fpStoreTief0] at h
    exact h
  have hrd : lesbar8 fpStoreT.kern.speicher (BitVec.ofNat 64 0x2000) =
      true := by
    decide
  exact read64_nach_write64 _ _ _ _ hwr hrd

/-- The store observably changed memory (top footprint byte). -/
theorem fpStore_aendert :
    fpStoreT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 0x2000) 7) ≠
      fpStoreT2.kern.speicher.bytes
        (addrOff (BitVec.ofNat 64 0x2000) 7) := by
  decide

/-- The store leaves executable bytes untouched: the entry byte still
    fetches, and the code address keeps execute permission. -/
theorem fpStore_code_bleibt :
    fpStoreT2.kern.speicher.ausfuehrbar (BitVec.ofNat 64 0x1000) = true ∧
    fpStoreT.kern.speicher.ausfuehrbar (BitVec.ofNat 64 0x1000) = true := by
  decide

/-- The store keeps the admitted control word. -/
theorem fpStore_fp_bleibt : fpStoreT2.fp = fpStoreT.fp := rfl

/-! ## Refusals: truncated bytes, refused MXCSR, wrong map, forged entry.

  Each refusal varies exactly one leg of the witness admission and is
  decided on actual bytes/words, never trusted. -/

/-- TRUNCATED-BYTE REFUSAL: the first three store bytes alone (prefix,
    escape, opcode without ModRM) fetch to nothing, and the
    strengthened FP check refuses the truncated image although its
    mapping checks. -/
def fpStumpfBild : Bild :=
  { fpStoreBild with
    datei := (fpEncodeMovsdSpeichere .rbx .xmm0 0).take 3 ++
      List.replicate 8 (natByte 0) }

theorem fpStumpf_verweigert :
    fpFetchDekodiert
      (fpBildT fpStumpfBild 0 0x1000 fpStoreReg storeFlags fpStoreXmm
        fpStoreK) = none ∧
    valFpEintrittStark .p48 fpStumpfBild 0 0x1000 fpStoreReg storeFlags
      fpStoreXmm fpStoreK fpStoreZ = false := by
  decide

/-- REFUSED-MXCSR REFUSAL: the FTZ word is refused at the fetch-level
    profile admission (`fpByteschritt`), at the strengthened FP check
    and at the entry predicate -- one bad word, three closed doors. -/
def fpFtzK : FPKontext := ⟨0x9F80⟩

theorem fpFtz_verweigert :
    fpByteschritt
      (fpBildT fpStoreBild 0 0x1000 fpStoreReg storeFlags fpStoreXmm
        fpFtzK) = .verweigert ∧
    valFpEintrittStark .p48 fpStoreBild 0 0x1000 fpStoreReg storeFlags
      fpStoreXmm fpFtzK fpStoreZ = false ∧
    mxcsrOk { fpStoreZ with mxcsr := 0x9F80 } = false := by
  refine ⟨?_, by decide, by decide⟩
  exact fpByteschritt_profil_verweigert _ (by decide)

/-- WRONG-MAP REFUSAL: a writable code section is refused by the checked
    mapping and hence by the strengthened FP check; starting the
    instruction pointer in the writable data section admits no FP
    fetch either. -/
def fpStoreBildWx : Bild :=
  { fpStoreBild with abschnitte := [{ fpStoreCode with schreibbar := true }, fpStoreDaten] }

theorem fpMap_verweigert :
    wohlgeformt .p48 fpStoreBildWx = false ∧
    valFpEintrittStark .p48 fpStoreBildWx 0 0x1000 fpStoreReg storeFlags
      fpStoreXmm fpStoreK fpStoreZ = false ∧
    fpFetchDekodiert
      (fpBildT fpStoreBild 0 0x2000 fpStoreReg storeFlags fpStoreXmm
        fpStoreK) = none := by
  decide

/-- FORGED-ENTRY REFUSAL: a control word the entry never established
    (reset profile word against an FTZ entry word) admits nothing,
    although the loaded bytes fetch and the word alone is valid. -/
theorem fpEintritt_geschmiedet_verweigert :
    fpFetchDekodiert fpStoreT ≠ none ∧
    fpEintritt fpStoreK = true ∧
    valFpEintrittStark .p48 fpStoreBild 0 0x1000 fpStoreReg storeFlags
      fpStoreXmm fpStoreK { fpStoreZ with mxcsr := 0x9F80 } = false := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Joint witness: admitted loaded FP store beside a reached source run.

  The admitted loaded entry stores `+∞` from actual image bytes with
  a real memory change, untouched executable bytes and an untouched
  control word; beside it, the certified source fixture contributes a
  reached one-step run whose table some function writes (`-0 -> +0`
  at the slot, bit patterns differing). Neither side is derived from
  the other; no lowering between them is claimed. -/

/-- JOINT WITNESS (admitted loaded FP execution + reached source run):
    the strengthened FP entry is admitted, its actual loaded bytes
    store `xmm0` to `[rbx]` with a real memory change under untouched
    execute permission and an untouched control word, and on the
    non-degenerate source fixture a reached run writes the one table
    the contract and the function both write. -/
theorem fpVal_gelenk_zeuge :
    ∃ (t' : FpZustand) (σ' : Gabbro.Grammatik.World fltWitD)
      (ρ' : Gabbro.Grammatik.Env fltWitD
        [Gabbro.Grammatik.Ty.fl (0, 1) (1, 1)]),
      valFpEintrittStark .p48 fpStoreBild 0 0x1000 fpStoreReg storeFlags
        fpStoreXmm fpStoreK fpStoreZ = true ∧
      fpByteschritt fpStoreT = .weiter t' ∧
      read64 t'.kern.speicher (BitVec.ofNat 64 0x2000) =
        some 0x7FF0000000000000 ∧
      fpStoreT.kern.speicher.bytes (addrOff (BitVec.ofNat 64 0x2000) 7) ≠
        t'.kern.speicher.bytes (addrOff (BitVec.ofNat 64 0x2000) 7) ∧
      t'.fp = fpStoreT.fp ∧
      t'.kern.speicher.ausfuehrbar (BitVec.ofNat 64 0x1000) = true ∧
      fltWitD.schreibt () () = true ∧
      fltWitV.schreibt () = true ∧
      Gabbro.Grammatik.execStmt fltWitO 0 fltWitR
        (Gabbro.Grammatik.Stmt.assignSlot (l := false) () () fltWitI fltWitE
          fltWitHw fltWitHL)
        fltWitSigma fltWitRho = .ok σ' ρ' ∧
      (fltWitSigma.slots () 0 ()).x ≠ (σ'.slots () 0 ()).x ∧
      Gleitkomma.zuBits Gleitkomma.f64 (fltWitSigma.slots () 0 ()).x ≠
        Gleitkomma.zuBits Gleitkomma.f64 (σ'.slots () 0 ()).x := by
  obtain ⟨σ', ρ', hschr, hV, hexec, _, _, hne, _, _, _, hbits⟩ :=
    null_beobachtung_zeuge
  exact ⟨fpStoreT2, σ', ρ', fpStore_ok, fpStore_schritt, fpStore_liest,
    fpStore_aendert, fpStore_fp_bleibt, fpStore_code_bleibt.1,
    hschr, hV, hexec, hne, hbits⟩

/- CUTS: what is not proved here.

   Proved here, over the ACTUAL accepted vocabulary
   (`ScalarFloatCodec`: `fpDecode`/`fpFetchDekodiert`/`fpByteschritt`
   with its round trips and refusals; `ScalarFloat`: `fpSchritt` with
   its step equations and frames; `FloatEntryState`: `mxcsrOk`/
   `eintrittFp`/`fpSchritt_erhaelt_fp`; `Bild`: `wohlgeformt`/
   `eintragEnthalten`/`ladenAusfuehrbar`/`geladen`/`schreibLese_zeuge`
   shape reused, not redone; `LoadedExecution`: `bildZustand`/
   `storeReg`/`storeFlags`; `ValidatorSkeleton`: the optional-check
   pattern; `FloatSourceObservations`: `null_beobachtung_zeuge`):
   the optional strengthened FP entry check (`valFpEintrittStark`:
   mapping AND containment AND execute byte AND successful FP
   fetch-and-decode from actual loaded bytes AND MXCSR profile
   admission AND entry discipline with the control word bound to the
   entry word) with its mapping, entry, permission, fetch-existence,
   profile, discipline and word-binding projections, the
   feature-readiness transfer (`valFp_gibt_bereit`), the generic
   entry-at-decoded-start consequence (`valFp_gibt_bytes`) and the
   loaded-step consequence (`valFp_schritt`: the same decoded step
   runs, the successor keeps the admitted control word, mapping and
   entry observations stay put), four planted refusal shapes
   (truncated bytes, refused MXCSR at three doors, W^X/data-RIP map,
   forged entry word), one admitted loaded MOVSD store of `+∞` with a
   real memory change under untouched executable bytes and an
   untouched control word, and the joint witness with the reached
   source table write.
   NOT proved here, and not claimed:
   - No `valX86_sound` and no source-to-final-loaded-bytes closure:
     nothing here claims the admitted bytes are the emitted form of
     any source program or refine any contract, duty, cost, lock or
     budget. The joint witness pairs the two sides side by side; the
     generic closing proof stays OPEN (shared IR of lane 287 is
     PENDING; no substitute is invented).
   - No hardware claim: bytes are model `Byte` lists, memory the model
     `Speicher`, MXCSR admission the accepted `mxcsrGueltig` profile;
     silicon, caches, TLBs, store buffers (per-byte TSO is not
     multi-byte atomicity), interrupts, faults beyond the decoded
     refusal, NaN payloads, sNaN quieting, sticky flags and timing are
     OPEN. Refusal `Bool`s are validator admission, never fault claims.
   - No concurrency claim: `fpByteschritt` is sequential over one
     `Speicher`; per-access TSO granularity, tearing and the GX
     refinement stay with the TSO-bridge work. No cost, timing,
     budget or termination claim.
   - Canonical subset only (inherited from `ScalarFloatCodec`):
     MOVSD register/load/store and ADDSD register, low XMM/GPR, no
     REX; control-word load/store has no accepted byte form, so
     establishment of the word from entry bytes is OPEN
     (`kein_fpSchritt_installiert` is reused, never restated).
   - `valFpEintrittStark` is OPTIONAL and new: the old `valX86` goal,
     checker and admission are preserved untouched; nothing existing
     is re-decided or weakened. No second executor and no second
     decoder exist here: `FpZustand`/`fpByteschritt`/`fpDecode` are
     reused untouched. The absent `ExtendedExecution575` file of the
     task text has no counterpart in this clone; the shared
     certificate/state interface IS `FpZustand`/`fpByteschritt`, and
     nothing here would conflict with such an extension.
   - Rule 13 (inhabitation): no theorem here takes a premise
     universally quantifying over source syntax (`Vertrag`, `Stmt`,
     `Endblock`, `ErgExpr`, `Expr`, `Args`); contracts appear only at
     actual values. The joint non-degenerate witness is
     `fpVal_gelenk_zeuge`: an admitted loaded FP store with a real
     memory change beside a reached source run with a table-writing
     call and disagreeing bit patterns.
-/

#print axioms valFp_wohlgeformt
#print axioms valFp_eintrag
#print axioms valFp_ausfuehrbar
#print axioms valFp_fetch_exist
#print axioms valFp_fpEintritt
#print axioms valFp_mxcsrOk
#print axioms valFp_kontext
#print axioms valFp_gibt_bereit
#print axioms valFp_gibt_bytes
#print axioms valFp_schritt
#print axioms fpStoreInstr_laenge
#print axioms fpStore_wohlgeformt
#print axioms fpStore_fetch
#print axioms fpStore_ok
#print axioms fpStoreTief0
#print axioms fpStoreEffAddr
#print axioms fpStore_schreib
#print axioms fpStore_schritt
#print axioms fpStore_liest
#print axioms fpStore_aendert
#print axioms fpStore_code_bleibt
#print axioms fpStore_fp_bleibt
#print axioms fpStumpf_verweigert
#print axioms fpFtz_verweigert
#print axioms fpMap_verweigert
#print axioms fpEintritt_geschmiedet_verweigert
#print axioms fpVal_gelenk_zeuge

end Gabbro.Grammatik.X86
