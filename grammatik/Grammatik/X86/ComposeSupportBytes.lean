/-
  Composition closing: support-bytes closing (lane 854).

  Producer/consumer interface closed here: the producers are the accepted
  validator halves (`ValidatorSkeleton.valX86` for image bytes with decode
  coverage, `GateStub.torOkB` for gate declarations, `TableLayout.layoutOk`
  for arena extents, `EntryState.eintrittOk` for thread-root/entry states,
  `Gleitprofil.mxcsrGueltig` for float control state) plus the accepted
  stub-shape facts (`bindungErstelltB`, `stubEndsTrapB` over the trap
  `trapBytes`) and the accepted byte-step execution (`Byteschritt`
  with `LoadedExecution.bildZustand` memory). The consumer is the closing
  step `stuetzSchritt`, which forces canonically loaded image memory so
  every reachable support byte comes from the validated image; unvalidated
  reachable bytes refuse. This file only composes already-accepted
  definitions and theorems; it re-proves no validator, decoder, fetch or
  step internals and defines no second interpreter or executor.
-/
import Grammatik.X86.Bild
import Grammatik.X86.Speicher
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.GateStub
import Grammatik.X86.TableLayout
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.EntryState
import Grammatik.X86.Gleitprofil
import Grammatik.X86.LoadedExecution

namespace Gabbro.Grammatik.X86

/-- Support-shim kinds closed here: `arena` (table extents via the computed
    layout), `faden` (thread-root entry state with its guard promise),
    `gleit` (float control state via the MXCSR profile). The gate-stub
    bytes cover every kind: each shim is reached through a checked stub. -/
inductive StuetzArt where
  | arena
  | faden
  | gleit
  deriving DecidableEq, Repr

/-- Checked support admission as one `Bool`: validated image bytes with
    decode coverage (`valX86`), an admitted gate (`torOkB` over the single
    gate this shim is reached through), an accepted arena layout
    (`valLayout`), established stub bindings with the `0F 05` trap suffix,
    an admitted entry state, and a valid float control word. Admission as
    `Bool`, never a hardware fault claim. -/
def stuetzOk (p : Profil) (bild : Bild) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand) : Bool :=
  valX86 p bild && torOkB tor && valLayout es &&
  bindungErstelltB tor moves &&
  stubEndsTrapB (moves.flatMap encode ++ trapBytes) &&
  eintrittOk p bild 0 art z && mxcsrGueltig z.mxcsr

/-- The one checked closing step: the byte step over canonically loaded
    image memory. Registers, flags and `rip` are the only caller inputs;
    memory is forced to `geladen`, so no caller-supplied byte ever becomes
    a trusted support byte. -/
def stuetzSchritt (bild : Bild) (bias : Nat) (s : Zustand) : ByteAusgang :=
  byteschritt { s with speicher := geladen bild bias }

/-- ADMISSION SPLIT: an admitted support tuple meets every accepted half:
    validated image bytes, an admitted gate, an accepted arena layout,
    established stub bindings, the trap suffix, an admitted entry state,
    and a valid float control word. Pure `Bool` inversion over the
    conjunction; no producer fact is re-proved here. -/
theorem stuetzOk_teile (p : Profil) (bild : Bild) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : stuetzOk p bild tor moves es art z = true) :
    valX86 p bild = true ∧ torOkB tor = true ∧ valLayout es = true ∧
    bindungErstelltB tor moves = true ∧
    stubEndsTrapB (moves.flatMap encode ++ trapBytes) = true ∧
    eintrittOk p bild 0 art z = true ∧ mxcsrGueltig z.mxcsr = true := by
  unfold stuetzOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩ := h
  exact ⟨hA, hB, hC, hD, hE, hF, hG⟩

/-- SUCCESS DIRECTION: a successful fetch through the closing step runs
    the existing `schritt` on the fetched support instruction. The closing
    step is execution, not a conjunction of checks: composes the accepted
    `byteschritt_weiter` over the forced loaded memory. -/
theorem stuetzSchritt_weiter (bild : Bild) (bias : Nat) (s s' : Zustand)
    (d : Decodiert) (rest : List Byte)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } =
      some (d, rest))
    (hs : schritt d { s with speicher := geladen bild bias } = some s') :
    stuetzSchritt bild bias s = .weiter s' := by
  unfold stuetzSchritt
  exact byteschritt_weiter _ _ _ _ hf hs

/-- REFUSAL CORE: where the forced loaded memory yields no fetch, the
    closing step has no transition. Unvalidated reachable bytes refuse:
    nothing outside the validated image is ever fetched. Composes the
    accepted `byteschritt_verweigert_ohne_fetch`. -/
theorem stuetzSchritt_verweigert_ohne_fetch (bild : Bild) (bias : Nat)
    (s : Zustand)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } = none) :
    stuetzSchritt bild bias s = .verweigert := by
  unfold stuetzSchritt
  exact byteschritt_verweigert_ohne_fetch _ hf

/-- STEP REFUSAL: a fetched support instruction whose `schritt` fails is
    no transition. Composes the accepted
    `byteschritt_verweigert_ohne_schritt`. -/
theorem stuetzSchritt_verweigert_ohne_schritt (bild : Bild) (bias : Nat)
    (s : Zustand) (d : Decodiert) (rest : List Byte)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } =
      some (d, rest))
    (hs : schritt d { s with speicher := geladen bild bias } = none) :
    stuetzSchritt bild bias s = .verweigert := by
  unfold stuetzSchritt
  exact byteschritt_verweigert_ohne_schritt _ _ _ hf hs

/-- IMAGE REFUSAL: support bytes outside a validated image admit nothing.
    Uses the failed image check. -/
theorem stuetz_verweigert_ohne_bild (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : valX86 p bild = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- GATE REFUSAL: a support shim reached through an unadmitted gate
    admits nothing. Uses the failed gate check. -/
theorem stuetz_verweigert_ohne_tor (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : torOkB tor = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- ARENA REFUSAL: support bytes over a refused arena layout admit
    nothing. Uses the failed layout check. -/
theorem stuetz_verweigert_ohne_layout (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : valLayout es = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- BINDING REFUSAL: a stub that never establishes its gate parameters
    admits nothing. Uses the failed binding check. -/
theorem stuetz_verweigert_ohne_bindung (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : bindungErstelltB tor moves = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- TRAP REFUSAL: a stub without the `0F 05` trap suffix admits nothing.
    Uses the failed suffix check. -/
theorem stuetz_verweigert_ohne_trap (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : stubEndsTrapB (moves.flatMap encode ++ trapBytes) = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- ENTRY REFUSAL: a support shim entered through a refused entry state
    (thread root without its guard, XMM touched without a save, wrong IF)
    admits nothing. Uses the failed entry check. -/
theorem stuetz_verweigert_ohne_eintritt (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : eintrittOk p bild 0 art z = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- FLOAT REFUSAL: a shim with an invalid float control word admits
    nothing. Uses the failed MXCSR profile check. -/
theorem stuetz_verweigert_ohne_mxcsr (p : Profil) (bild : Bild)
    (tor : TorDekl) (moves : List Befehl) (es : List TabLayout)
    (art : EintrittArt) (z : EintrittZustand)
    (h : mxcsrGueltig z.mxcsr = false) :
    stuetzOk p bild tor moves es art z = false := by
  unfold stuetzOk
  rw [h]
  simp

/-- SUPPORT-BY­TES CLOSING through the checked step, generic over
    arbitrary admitted inputs: admission meets every accepted half
    (image bytes with decode coverage, gate, arena layout, stub bindings,
    trap suffix, entry state, float control), a successful fetch through
    loaded image memory runs the existing `schritt`, and no fetch means
    no transition. Composes `stuetzOk_teile`, `stuetzSchritt_weiter` and
    `stuetzSchritt_verweigert_ohne_fetch`; no producer fact is re-proved. -/
theorem ComposeSupportBytes_verbindung (p : Profil) (bild : Bild)
    (bias : Nat) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (art : EintrittArt) (z : EintrittZustand)
    (s : Zustand) :
    (stuetzOk p bild tor moves es art z = true →
      valX86 p bild = true ∧ valTore [tor] = true ∧ valLayout es = true ∧
      torOkB tor = true ∧ bindungErstelltB tor moves = true ∧
      stubEndsTrapB (moves.flatMap encode ++ trapBytes) = true ∧
      eintrittOk p bild 0 art z = true ∧ mxcsrGueltig z.mxcsr = true) ∧
    (∀ (d : Decodiert) (rest : List Byte) (s' : Zustand),
      fetchDekodiert { s with speicher := geladen bild bias } =
        some (d, rest) →
      schritt d { s with speicher := geladen bild bias } = some s' →
      stuetzSchritt bild bias s = .weiter s') ∧
    (fetchDekodiert { s with speicher := geladen bild bias } = none →
      stuetzSchritt bild bias s = .verweigert) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨hA, hB, hC, hD, hE, hF, hG⟩ :=
      stuetzOk_teile p bild tor moves es art z h
    refine ⟨hA, ?_, hC, hB, hD, hE, hF, hG⟩
    unfold valTore
    simp [hB]
  · intro d rest s' hf hs
    exact stuetzSchritt_weiter bild bias s s' d rest hf hs
  · intro hf
    exact stuetzSchritt_verweigert_ohne_fetch bild bias s hf

/-- Witness caller state for the composed run: the store-image registers,
    flags and entry `rip`; memory is arbitrary here because the closing
    step forces canonically loaded memory. -/
def stuetzWitS : Zustand :=
  { register := storeReg
    flags := storeFlags
    rip := BitVec.ofNat 64 0x101000
    speicher := zeugenSpeicherE }

/-- The closing step over the witness caller state is the accepted loaded
    store step: forcing loaded memory erases the caller-supplied bytes. -/
theorem stuetzWit_schritt :
    stuetzSchritt bildStore 0x100000 stuetzWitS =
      byteschritt bildStoreStart := rfl

/-- ADMISSION: the concrete support tuple validates: the minimal accepted
    image with decode coverage, the witness gate, the computed arena layout
    of the table-writing unit, the witness stub with its trap suffix, the
    hosted entry state, and the reset MXCSR word. -/
theorem stuetzWit_ok :
    stuetzOk .p48 valZeuge schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) .hostedMain zeugenEintrittHosted
      = true := by
  decide

/-- PLANTED IMAGE REFUSAL at the closing predicate: the W^X-violating
    image admits no support shim, whatever the gate, stub, layout and
    entry are. -/
theorem stuetzWit_wx_verweigert :
    stuetzOk .p48 valWx schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) .hostedMain zeugenEintrittHosted
      = false := by
  decide

/-- Witness caller state aimed at the data section: registers and flags
    of the store image, `rip` at the data base. Memory is arbitrary here
    because the closing step forces canonically loaded memory. -/
def stuetzWitDaten : Zustand :=
  { register := storeReg
    flags := storeFlags
    rip := BitVec.ofNat 64 0x102000
    speicher := zeugenSpeicherE }

/-- PLANTED MAPPING REFUSAL through the closing step: starting the
    instruction pointer in the data section admits no support step. The
    forced state is the accepted data-rip state, whose accepted refusal
    (`bildStore_datenRip_verweigert`) inverts to `verweigert`. -/
theorem stuetzWit_daten_verweigert :
    stuetzSchritt bildStore 0x100000 stuetzWitDaten = .verweigert := by
  have h : stuetzSchritt bildStore 0x100000 stuetzWitDaten =
      byteschritt (bildZustand bildStore 0x100000
        (BitVec.ofNat 64 0x102000) storeReg storeFlags) := rfl
  rw [h]
  cases hbs : byteschritt (bildZustand bildStore 0x100000
    (BitVec.ofNat 64 0x102000) storeReg storeFlags) with
  | weiter s =>
    have hnone := bildStore_datenRip_verweigert
    simp [hbs, ausgangRip] at hnone
  | verweigert => rfl

/-- Witness caller state over the mutated image: the store-image
    registers, flags and code entry; memory is forced by the step. -/
def stuetzWitMutiert : Zustand :=
  { register := storeReg
    flags := storeFlags
    rip := BitVec.ofNat 64 0x101000
    speicher := zeugenSpeicherE }

/-- PLANTED DECODE REFUSAL through the closing step: the forged opcode
    byte turns the loaded support step into a refusal, while the checked
    mapping still holds. Inverts the accepted mutation refusal
    (`bildStore_mutiert_verweigert`) to `verweigert`. -/
theorem stuetzWit_mutiert_verweigert :
    stuetzSchritt bildStoreMutiert 0x100000 stuetzWitMutiert =
      .verweigert := by
  have h : stuetzSchritt bildStoreMutiert 0x100000 stuetzWitMutiert =
      byteschritt bildStoreStartMutiert := rfl
  rw [h]
  cases hbs : byteschritt bildStoreStartMutiert with
  | weiter s =>
    have hnone := bildStore_mutiert_verweigert
    simp [hbs, ausgangRip] at hnone
  | verweigert => rfl

/-- JOINT WITNESS for `ComposeSupportBytes_verbindung`: the closing
    instantiated jointly at the accepted store tuple (step legs through
    the composed `stuetzSchritt`), the reached memory-changing run (42
    into the data cell through loaded image memory, zero before), planted
    refusals through the composed step (data-section start, forged opcode
    byte), the admitted support tuple on the minimal accepted image, the
    non-degenerate source side (computed arena layout accepted, nonempty
    carrier enumeration, `setze` writes `konto`), a real memory-changing
    write/read, and planted admission refusals (W^X image, FTZ control
    word). -/
theorem ComposeSupportBytes_verbindung_zeuge :
    (∀ (d : Decodiert) (rest : List Byte) (s' : Zustand),
      fetchDekodiert { stuetzWitS with speicher := geladen bildStore 0x100000 } = some (d, rest) →
      schritt d { stuetzWitS with speicher := geladen bildStore 0x100000 } = some s' →
      stuetzSchritt bildStore 0x100000 stuetzWitS = .weiter s') ∧
    (fetchDekodiert { stuetzWitS with speicher := geladen bildStore 0x100000 } = none →
      stuetzSchritt bildStore 0x100000 stuetzWitS = .verweigert) ∧
    ausgangByte (BitVec.ofNat 64 0x102000)
      (stuetzSchritt bildStore 0x100000 stuetzWitS) =
      some (natByte 42) ∧
    bildStoreStart.speicher.bytes (BitVec.ofNat 64 0x102000) =
      BitVec.ofNat 8 0 ∧
    stuetzSchritt bildStore 0x100000 stuetzWitDaten = .verweigert ∧
    stuetzSchritt bildStoreMutiert 0x100000 stuetzWitMutiert =
      .verweigert ∧
    stuetzOk .p48 valZeuge schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) .hostedMain zeugenEintrittHosted
      = true ∧
    layoutOk (layoutFuer zeugenU 4096 8) = true ∧
    slotAufz zeugenU ≠ [] ∧
    (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
    (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a) ∧
    stuetzOk .p48 valWx schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) .hostedMain zeugenEintrittHosted
      = false ∧
    mxcsrGueltig 0x9F80 = false := by
  obtain ⟨_, hstep, href⟩ := ComposeSupportBytes_verbindung .p48 bildStore
    0x100000 schreibTor zeugenMoves (layoutFuer zeugenU 4096 8) .hostedMain
    zeugenEintrittHosted stuetzWitS
  have hrun := bildStore_schritt_speichert
  rw [← stuetzWit_schritt] at hrun
  exact ⟨hstep, href, hrun.1, hrun.2, stuetzWit_daten_verweigert,
    stuetzWit_mutiert_verweigert, stuetzWit_ok, zeugenLayout_ok,
    zeugenSlot_ne, zeugenU_schreibt, schreibLese_zeuge,
    stuetzWit_wx_verweigert, mxcsr_ftz_verweigert⟩

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second loader/decoder/executor/ISA): the one
    checked closing step `stuetzSchritt` (state memory forced to
    `geladen`, so every reachable support byte comes from the validated
    image), the checked support admission `stuetzOk` (image bytes with
    decode coverage AND gate AND arena layout AND stub bindings AND trap
    suffix AND entry state AND float control word), its split into the
    accepted halves (`stuetzOk_teile`), the success direction through the
    existing `schritt`, the fetch/step refusal core, one admission
    refusal per support kind (image, gate, arena layout, stub bindings,
    trap suffix, entry, float word), the generic closing
    (`ComposeSupportBytes_verbindung` over arbitrary admitted inputs),
    and one joint witness with a reached memory-changing run through the
    composed step plus planted step-level and admission-level refusals.
    NOT proved here, and not claimed:
    - No source correspondence: nothing here claims the support bytes are
      the emitted form of any source program, or that duties, contracts,
      costs, locks or call logs refine anything. The lowering closure
      waits on the shared IR (lane 287, pending); no substitute is
      invented here.
    - No hardware correspondence: fetch runs over the model `Speicher`
      function, not silicon; caches, TLBs, store buffers (per-byte TSO is
      not multi-byte atomicity), interrupts, faults beyond the decoded
      refusal, FP control/NaN observability beyond the profile `Bool`
      and timing are OPEN.
    - No TSO/W/GX bridge: per-access refinement of support-byte accesses
      (arena data, thread stacks, float spills) into W/GX stays with the
      bridge lanes (owners: 573-574, waiting on accepted 567/570
      interfaces); the `schwach_ist_gX` source leg is reused, never
      assumed for the target.
    - No budget/cost transfer: relating `stuetzSchritt` runs to source
      budgets (`budget_simulation`, `CostSummary.expandBound`) stays OPEN
      with the budget lanes.
    - No whole-binary theorem: no multi-step control-flow validation, no
      relocation patched-site re-decoding (owner: lane 561), no ABI or
      loader contract beyond the admission `Bool`s, no kernel behaviour
      beyond the named assumption (`EntryState.KernAntwort`).
    - No single-image end-to-end witness: admission is witnessed on the
      minimal accepted image (`valZeuge`), the storing run and the
      step-level refusals on the accepted store image (`bildStore`);
      the generic closing itself is over one arbitrary image, but an
      admitted thread-root entry combined with a storing run on the same
      image is not exhibited here.
    - `verweigert` is the absence of a transition, never a termination
      claim.
-/

#print axioms stuetzOk_teile
#print axioms stuetzSchritt_weiter
#print axioms stuetzSchritt_verweigert_ohne_fetch
#print axioms stuetzSchritt_verweigert_ohne_schritt
#print axioms stuetz_verweigert_ohne_bild
#print axioms stuetz_verweigert_ohne_tor
#print axioms stuetz_verweigert_ohne_layout
#print axioms stuetz_verweigert_ohne_bindung
#print axioms stuetz_verweigert_ohne_trap
#print axioms stuetz_verweigert_ohne_eintritt
#print axioms stuetz_verweigert_ohne_mxcsr
#print axioms ComposeSupportBytes_verbindung
#print axioms stuetzWit_schritt
#print axioms stuetzWit_ok
#print axioms stuetzWit_wx_verweigert
#print axioms stuetzWit_daten_verweigert
#print axioms stuetzWit_mutiert_verweigert
#print axioms ComposeSupportBytes_verbindung_zeuge

end Gabbro.Grammatik.X86
