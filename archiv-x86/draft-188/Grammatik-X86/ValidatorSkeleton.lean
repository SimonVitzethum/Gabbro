/-
  Validator skeleton for the direct x86-64 backend (lane 349, WORK-ALLOCATION C5).

  Decided syntactic admission over the accepted canonical vocabulary:
  `Bild.wohlgeformt`, `Codec.decode`, `Byteschritt.byteschritt`,
  `GateStub.torOkB`, `TableLayout.layoutOk`. No source admission is
  tightened; full final-byte/source/hardware correspondence stays OPEN.
-/
import Grammatik.X86.Bild
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.GateStub
import Grammatik.X86.TableLayout
import Grammatik.X86.ValidationBudget

namespace Gabbro.Grammatik.X86

/-- Syntactic validator refusal shapes (IMAGE-ABI sec. 15, non-exhaustive). -/
inductive ValFehler where
  | veraendertesByte
  | ungueltigeStelle
  | falscheAbi
  | ungepruefterFremdkoerper
  | geschmiedeterZeiger
  | bssFehler
  | nichtGelisteteAbbildung
  deriving DecidableEq, Repr

/-- File bytes owned by one section: `dateiLen` bytes from `dateiOff`. -/
def abschnittBytes (bild : Bild) (s : Abschnitt) : List Byte :=
  (bild.datei.drop s.dateiOff).take s.dateiLen

/-- Decode coverage of one section: executable sections must fully decode
    through the canonical decoder under explicit fuel; data sections carry
    arbitrary bytes and are not decoded. Reuses `validAllFuel`, no second
    decoder. Fuel `dateiLen + 1` covers the worst case of one byte per
    instruction plus the empty program. -/
def abschnittDeckung (bild : Bild) (s : Abschnitt) : Bool :=
  if s.ausfuehrbar then validAllFuel (s.dateiLen + 1) (abschnittBytes bild s)
  else true

/-- Decode coverage of the whole image: every section covered. -/
def bildDeckung (bild : Bild) : Bool :=
  bild.abschnitte.all (abschnittDeckung bild)

/-- Skeleton admission, re-read from untrusted backend bytes and
    re-validated: checked mapping AND full decode coverage of every
    executable section. Permissions, entries, relocations and mode come
    from `wohlgeformt`; coverage comes from the canonical decoder. -/
def valX86 (p : Profil) (bild : Bild) : Bool :=
  wohlgeformt p bild && bildDeckung bild

/-- The skeleton implies the checked mapping. -/
theorem valX86_wohlgeformt (p : Profil) (bild : Bild)
    (h : valX86 p bild = true) :
    wohlgeformt p bild = true := by
  unfold valX86 at h
  exact (Bool.and_eq_true_iff.mp h).1

/-- The skeleton implies decode coverage. -/
theorem valX86_deckung (p : Profil) (bild : Bild)
    (h : valX86 p bild = true) :
    bildDeckung bild = true := by
  unfold valX86 at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- Minimal witness code section: one `ret` byte, readable+executable,
    never writable, alignment 1 (divides every base). -/
def valZeugeCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 1, vaddr := 0x1000, memLen := 1,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 1 }

/-- Minimal accepted image prefix: one `ret` (byte 195) in executable
    memory, entry at its base, fixed bias. -/
def valZeuge : Bild :=
  { datei := [natByte 195]
    abschnitte := [valZeugeCode]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- ACCEPTANCE: the minimal image prefix validates. -/
theorem valZeuge_akzeptiert : valX86 .p48 valZeuge = true := by
  decide

/-- ALTERED-BYTE REFUSAL (IMAGE-ABI sec. 15): flipping the single opcode
    byte 195 (`ret`) to 0 (no canonical instruction) refuses. The mapping
    still checks, so this refusal comes from decode coverage, never from
    a trusted hint. -/
theorem valZeuge_mutiert_verweigert :
    valX86 .p48 { valZeuge with datei := [natByte 0] } = false := by
  decide

/-- The mapping alone still admits the mutated bytes: pinning that the
    refusal above is a decode refusal, not a mapping refusal. -/
theorem valZeuge_mutiert_mapping_bleibt :
    wohlgeformt .p48 { valZeuge with datei := [natByte 0] } = true := by
  decide

/-- INVALID-SITE REFUSAL: a code-operand relocation sited past the end
    of its section (offset 7 in a 1-byte section) refuses, even with a
    resolved value inside code. -/
def valFalscheStelle : Bild :=
  { valZeuge with
    reloks := [{ abschnitt := 0, siteOff := 7,
                 art := .codeOperand,
                 status := .aufgeloest 0x1000 }] }

theorem valFalscheStelle_verweigert :
    valX86 .p48 valFalscheStelle = false := by
  decide

/-- PERMISSION REFUSAL (W^X): a section both writable and executable
    refuses. The refusal Bool is validator admission, never an invented
    hardware fault: actual x86 permits many unaligned ordinary accesses;
    this Bool only decides what the validator admits. -/
def valWx : Bild :=
  { valZeuge with
    abschnitte := [{ valZeugeCode with schreibbar := true }] }

theorem valWx_verweigert : valX86 .p48 valWx = false := by
  decide

/-- Caller-gate admission: every listed gate meets the decided
    declaration checks (N063-N067 + Linux clobbers). Reuses `torOkB`,
    never trusted from a Rust print. -/
def valTore (tore : List TorDekl) : Bool :=
  tore.all torOkB

/-- Computed-layout admission: every entry plus pairwise disjointness.
    Reuses `layoutOk`; a Rust hint is re-decided via `hinweisOk`, never
    a premise here. -/
def valLayout (es : List TabLayout) : Bool :=
  layoutOk es

/-- Full skeleton with gate and layout halves: image AND gates AND
    layout, each re-decided. -/
def valX86Voll (p : Profil) (bild : Bild)
    (tore : List TorDekl) (es : List TabLayout) : Bool :=
  valX86 p bild && valTore tore && valLayout es

/-- The full skeleton implies the image skeleton. -/
theorem valX86Voll_bild (p : Profil) (bild : Bild)
    (tore : List TorDekl) (es : List TabLayout)
    (h : valX86Voll p bild tore es = true) :
    valX86 p bild = true := by
  unfold valX86Voll at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- WRONG-ABI REFUSAL (N064 shape): a gate whose out-register is
    clobbered refuses; the positive witness gate passes. -/
theorem valAbi_falsch_verweigert :
    valTore [torAusClobber] = false ∧ valTore [schreibTor] = true := by
  refine ⟨by decide, by decide⟩

/-- Full skeleton refuses the wrong-ABI gate on the accepted image. -/
theorem valVoll_abi_verweigert :
    valX86Voll .p48 valZeuge [torAusClobber] [] = false ∧
      valX86Voll .p48 valZeuge [schreibTor] [] = true := by
  refine ⟨by decide, by decide⟩

/-- Extern call-site bookkeeping: `bewiesen` means a proved x86 template
    correspondence exists for that callee. The declaration alone admits
    nothing; gate/OS contracts are user logic, never hardware axioms. -/
structure ExternStelle where
  ort : Nat
  bewiesen : Bool
  deriving DecidableEq, Repr

/-- Every extern site needs its proved correspondence. -/
def externOk (xs : List ExternStelle) : Bool :=
  xs.all (fun x => x.bewiesen)

/-- UNCHECKED-FOREIGN-BODY REFUSAL: a site without proved correspondence
    refuses; the empty site list passes. -/
theorem valFremd_verweigert :
    externOk [{ ort := 0, bewiesen := false }] = false ∧
      externOk [] = true := by
  refine ⟨by decide, by decide⟩

/-- Pointer-operand admission mirror: a number where a pointer is
    expected is forged and refused. Reuses `m140VerweigertB`. -/
def valZeigerOk (wartetZeiger : List Nat)
    (werte : List (Nat × StubenWert)) : Bool :=
  !m140VerweigertB wartetZeiger werte

/-- FORGED-POINTER REFUSAL (M140 shape): a bare number at a
    pointer-expecting site refuses; a base+extent pointer passes. -/
theorem valZeiger_geschmiedet_verweigert :
    valZeigerOk [0] [(0, .zahl 7)] = false ∧
      valZeigerOk [0] [(0, .zeiger 0x2000 8)] = true := by
  refine ⟨by decide, by decide⟩

/-- BSS-MISMATCH REFUSAL (`groesseOk` shape): a section claiming two
    file bytes with only one byte of extent (`dateiLen > memLen`,
    a negative BSS tail) refuses. Decode coverage stays intact (two
    `ret` bytes validate under fuel 3), pinning this as a mapping
    refusal. Loader-observed nonzero BSS is outside this pure function
    and stays OPEN. -/
def valBssNeg : Bild :=
  { datei := [natByte 195, natByte 195]
    abschnitte := [{ valZeugeCode with dateiLen := 2, memLen := 1 }]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

theorem valBssNeg_verweigert :
    valX86 .p48 valBssNeg = false ∧
      groesseOk { valZeugeCode with dateiLen := 2, memLen := 1 } = false := by
  refine ⟨by decide, by decide⟩

/-- Transfer-target admission: a branch/call target must lie in a
    listed section; anything else is an unlisted mapping and refuses.
    Reuses `abteilFinden`, no second register. -/
def transferOk (bild : Bild) (bias ziel : Nat) : Bool :=
  match abteilFinden bild.abschnitte bias ziel with
  | some _ => true
  | none => false

/-- UNLISTED-MAPPING REFUSAL: the hole address refuses, the code base
    passes. Existing direct CALL/RET make no unlisted address legal. -/
theorem valTransfer_unlisted_verweigert :
    transferOk valZeuge 0 0x1800 = false ∧
      transferOk valZeuge 0 0x1000 = true := by
  refine ⟨by decide, by decide⟩

/-- JOINT WITNESS: accepted minimal prefix, its one-byte-mutation
    refusal, and a real memory-changing write/read over canonically
    loaded image memory (`Bild.schreibLese_zeuge`, reused not redone).
    The memory conjunct is actual `Speicher` bytes changing, not a
    second model. -/
theorem valZeuge_gelenk :
    valX86 .p48 valZeuge = true ∧
      valX86 .p48 { valZeuge with datei := [natByte 0] } = false ∧
      (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
          m.bytes a ≠ m'.bytes a) := by
  refine ⟨by decide, by decide, schreibLese_zeuge⟩

/-- Future ISA extension: a decoder ONLY for bytes the canonical
    `decode` refuses. The extension never overrides, duplicates, or
    re-evaluates any of the existing 14 pilot forms: `decodeErw` tries
    the canonical `decode` first and consults `ext` solely on `none`.
    How the one target semantics is extended is exactly this field. -/
structure ErwDec where
  ext : List Byte → Option (Decodiert × List Byte)

/-- Extension decode: canonical first, extension only where canonical
    refuses. No existing form is re-decided. -/
def decodeErw (e : ErwDec) (bs : List Byte) :
    Option (Decodiert × List Byte) :=
  match decode bs with
  | some r => some r
  | none => e.ext bs

/-- The extension agrees with the canonical decoder on every byte
    string the canonical decoder accepts: no existing form is shadowed. -/
theorem decodeErw_kanonisch (e : ErwDec) (bs : List Byte)
    (d : Decodiert) (rest : List Byte)
    (h : decode bs = some (d, rest)) :
    decodeErw e bs = some (d, rest) := by
  unfold decodeErw
  rw [h]

/-- Witness machine state: zeroed registers/flags, `rip` at the witness
    entry, memory is the canonically loaded witness image. Reuses the
    shared `Zustand`/`geladen` vocabulary, no second state. -/
def valZeugeZustand : Zustand :=
  { register := fun _ => BitVec.ofNat 64 0
    flags := { cf := false, pf := false, af := none, zf := false,
               sf := false, of := false }
    rip := BitVec.ofNat 64 0x1000
    speicher := geladen valZeuge 0 }

/-- FETCH TIE: on the witness loaded state at the entry, the byte step's
    fetch (`Byteschritt.fetchDekodiert`, reusing the independent decoder
    over actual executable memory) sees exactly the validated `ret` with
    no remainder. The validator's accepted bytes are what the machine
    fetches; no caller-supplied decoded value is trusted. -/
theorem valZeuge_fetch_ret :
    fetchDekodiert valZeugeZustand = some (⟨.ret, 1⟩, []) := by
  decide

#print axioms valX86_wohlgeformt
#print axioms valX86_deckung
#print axioms valZeuge_akzeptiert
#print axioms valZeuge_mutiert_verweigert
#print axioms valZeuge_mutiert_mapping_bleibt
#print axioms valFalscheStelle_verweigert
#print axioms valWx_verweigert
#print axioms valX86Voll_bild
#print axioms valAbi_falsch_verweigert
#print axioms valVoll_abi_verweigert
#print axioms valFremd_verweigert
#print axioms valZeiger_geschmiedet_verweigert
#print axioms valBssNeg_verweigert
#print axioms valTransfer_unlisted_verweigert
#print axioms valZeuge_gelenk
#print axioms decodeErw_kanonisch
#print axioms valZeuge_fetch_ret

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Bild.wohlgeformt`
   with `groesseOk`/`dateiOk`/`virtuellOk`, `Codec.decode`,
   `ValidationBudget.validAllFuel`/`decodeFuel`, `Byteschritt`
   fetch (`fetchDekodiert` over actual executable memory),
   `GateStub.torOkB`/`m140VerweigertB`, `TableLayout.layoutOk`,
   `Bild.abteilFinden`/`geladen`/`schreibLese_zeuge`): the `valX86`
   skeleton (mapping AND decode coverage), its full half with gates
   and layout (`valX86Voll`), the extern-site bookkeeping (`externOk`),
   the pointer mirror (`valZeigerOk`), the transfer check
   (`transferOk`), the extension interface (`ErwDec`/`decodeErw` with
   the no-shadowing fact), one accepted minimal image prefix plus its
   one-byte-mutation refusal, and one proved refusal per IMAGE-ABI
   sec. 15 shape (altered byte, bad site, wrong ABI, unchecked
   foreign body, forged pointer, BSS mismatch, unlisted mapping),
   with the joint memory-changing witness and the fetch tie.
   OPEN, stated here as obligation and never as an assumed premise of
   any delivered theorem:
   - `valX86_sound`: no claim is made that `valX86 = true` implies any
     source correspondence, refinement, TSO/GX bridge, concurrency,
     contract, budget, cost/time, FP, flag-undefinedness, or hardware
     behaviour. The soundness proof WAITS on IR+TSO+decoder coupling
     (shared IR of lane 287 is PENDING; no substitute is invented).
   - No source correspondence: nothing here claims the bytes are the
     emitted form of any source program; no source admission is
     tightened and no `Stmt`/`Vertrag`-universal theorem is stated.
   - No hardware claim: bytes are model `Byte` lists, memory the model
     `Speicher`; silicon, caches, TLBs, store buffers (per-byte TSO is
     not multi-byte atomicity), interrupts, faults beyond the decoded
     refusal, FP control/NaNs and AF-undefinedness are open. The
     refusal Bool is validator admission, never a hardware fault.
   - No cost/time claim: fuel counts decoded instructions only.
   - Loader-observed nonzero BSS, data-in-code ranges, patched-site
     re-decode correspondence, control-flow/entry legality beyond
     containment, and callee-side (obligation (c)) template proofs
     stay with their owners.
   - Gate/OS contracts are user logic, never hardware axioms; the
     declaration alone admits nothing (`externOk` refuses without the
     proved correspondence, whose existence is bookkeeping here).
-/
end Gabbro.Grammatik.X86
