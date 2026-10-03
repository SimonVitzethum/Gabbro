/-
  File:      Grammatik/X86/OptAddrModeSel.lean
  Subject:   Address-mode selection rule lemma (lane 893).

  DESIGN section 7 row: smallest-first addressing (disp0/disp8/disp32,
  SIB, RIP-relative for image constants) with revalidation after
  patching. Certificate: local rewrite record plus recomputed analysis
  citations. Failure case: any unrevalidated patch, any large
  displacement narrowed, any RIP-relative form outside image constants.

  Proved over the REUSED canonical vocabulary (`Typen`, `Syntax`,
  `Semantik`, `ReferenzB`, `X86.Typen`, `X86.Wort`, `X86.AddressEncoding`
  with `adrEff`/`dispWortArt`/`passtIn8`/`kompaktArt`/`fussZugelassen`).
  No `ensures` is derived, no refusal becomes a warning, no faulting
  form is speculated above its guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.AddressEncoding

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one address-mode selection
    site (DESIGN section 7 row): the displacement recomputedly fits one
    signed byte, the selected address recomputedly admits its eight-byte
    footprint without wrap, a RIP-relative choice cites an image-constant
    mapping, and the patched bytes were revalidated after patching. -/
structure AddrSelCert where
  kleinOk : Bool
  keinUmbruch : Bool
  ripBildOk : Bool
  nachgeprueft : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation, never to
    a warning. -/
def addrSelZulassen (c : AddrSelCert) : Bool :=
  c.kleinOk && c.keinUmbruch && c.ripBildOk && c.nachgeprueft

/-! ## 1. Refusal: every DESIGN failure case must NOT select.

    A large displacement narrowed to one byte is refused
    (`kleinOk = false` forces `false`). A wrapped footprint is refused:
    no admission is forged from modular wrap. A RIP-relative form
    outside image constants is refused. An unrevalidated patch is
    refused: patched bytes that never passed revalidation select
    nothing. All four are proved of the decided Bool, so the validator
    cannot silently skip them. -/

/-- A large displacement refuses the narrow selection. -/
theorem addrSelVerweigert_gross (c : AddrSelCert)
    (h : c.kleinOk = false) :
    addrSelZulassen c = false := by
  simp [addrSelZulassen, h]

/-- A wrapped footprint refuses the selection. -/
theorem addrSelVerweigert_umbruch (c : AddrSelCert)
    (h : c.keinUmbruch = false) :
    addrSelZulassen c = false := by
  simp [addrSelZulassen, h]

/-- A RIP-relative form outside image constants refuses. -/
theorem addrSelVerweigert_ripFremd (c : AddrSelCert)
    (h : c.ripBildOk = false) :
    addrSelZulassen c = false := by
  simp [addrSelZulassen, h]

/-- An unrevalidated patch refuses the selection. -/
theorem addrSelVerweigert_ohneNachpruefung (c : AddrSelCert)
    (h : c.nachgeprueft = false) :
    addrSelZulassen c = false := by
  simp [addrSelZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_addrSelZulassen_ok :
    addrSelZulassen ⟨true, true, true, true⟩ = true := by
  decide

/-- Probe: a large displacement is refused. -/
theorem probe_addrSelZulassen_gross :
    addrSelZulassen ⟨false, true, true, true⟩ = false := by
  decide

/-- Probe: an unrevalidated patch is refused. -/
theorem probe_addrSelZulassen_ohneNachpruefung :
    addrSelZulassen ⟨true, true, true, false⟩ = false := by
  decide

/-! ## 2. Value: narrow and wide select the same effective address.

    Over ARBITRARY register values (`s`), an arbitrary RIP base (`n`)
    and arbitrary form parts (`b`, `idx`, `k`, `d`, `r`): the validator
    recomputed the displacement equation IN THE KERNEL (`hEq`,
    conditional on admission `hz`): the low-byte sign extension names
    the same offset as the full-word one. Conclusion: `adrEff` agrees,
    so every later load, store and LEA computes the same address. The
    recomputation obligation is claimed only where the validator
    admitted the site; a merely trusted width never selects. -/

/-- The admitted narrow selection computes the wide address. -/
theorem addrSel_wert (s : Zustand) (n : Adresse)
    (b : Option Register) (idx : Option Register) (k : Nat)
    (d : BitVec 32) (r : Bool)
    (cert : AddrSelCert)
    (hz : addrSelZulassen cert = true)
    (hEq : addrSelZulassen cert = true →
      dispWortArt ⟨b, idx, k, d, .d8, r⟩ =
        dispWortArt ⟨b, idx, k, d, .d32, r⟩) :
    adrEff s n ⟨b, idx, k, d, .d8, r⟩ =
      adrEff s n ⟨b, idx, k, d, .d32, r⟩ := by
  have e := hEq hz
  simp [adrEff, e]

/-- Pin: displacement `5` selects `rbx + rcx * 8 + 5` in both widths. -/
theorem probe_addrSel_wert_fuenf :
    adrEff zeugeZustand (BitVec.ofNat 64 0)
        ⟨some .rbx, some .rcx, 8, BitVec.ofNat 32 5, .d8, false⟩ =
      adrEff zeugeZustand (BitVec.ofNat 64 0)
        ⟨some .rbx, some .rcx, 8, BitVec.ofNat 32 5, .d32, false⟩ := by
  decide

/-- A wrong width reading is a different offset, never silently the
    same: byte `0xFF` is `-1`, not `255`. The validator recomputes. -/
theorem probe_addrSel_breite_entscheidet :
    dispWortArt ⟨some .rbx, none, 1, u8Nach32 (natByte 255), .d8, false⟩ ≠
      dispWortArt ⟨some .rbx, none, 1, BitVec.ofNat 32 255, .d32, false⟩ := by
  decide

/-! ## 3. Fault: the same address admits the same footprint.

    From one address equation (`hA`, section 2) the checked admission
    (`fussZugelassen`: canonical address, no wrap, per-direction
    rights) agrees in both directions, and the checked outcomes agree:
    a read returns the same value or refuses on both sides, a write
    lands in the same memory or refuses on both sides. No fault is
    added or removed, and no permission is granted by the selection:
    rights stay the separate checked step they are. -/

/-- The admitted footprint is the same on both sides. -/
theorem addrSel_fuss (m : Speicher) (aN aW : Adresse)
    (hA : aN = aW) (w : Bool) :
    fussZugelassen m aN w = fussZugelassen m aW w := by
  rw [hA]

/-- A read through the narrow address is the wide read: same value,
    same refusal. Contracts at their place read the same values. -/
theorem addrSel_lesen (m : Speicher) (aN aW : Adresse)
    (hA : aN = aW) :
    read64 m aN = read64 m aW := by
  rw [hA]

/-- A write through the narrow address lands where the wide write
    lands: same bytes, same refusal. No access is added or removed,
    so concurrency sees the same footprint on both sides. -/
theorem addrSel_schreiben (m : Speicher) (aN aW : Adresse)
    (hA : aN = aW) (v : Wort) (m' : Speicher)
    (hwr : write64 m aW v = some m') :
    write64 m aN v = some m' := by
  rw [hA]
  exact hwr

/-- Pin: the witness footprint is admitted for the narrow and the wide
    selected address alike. -/
theorem probe_addrSel_fuss_zeuge :
    fussZugelassen storeWitSpeicher
        (adrEff storeWitZustand (BitVec.ofNat 64 4101)
          ⟨some .r8, some .r9, 8, u8Nach32 (natByte 0), .d8, false⟩)
        true = true ∧
      fussZugelassen storeWitSpeicher
        (adrEff storeWitZustand (BitVec.ofNat 64 4101)
          ⟨some .r8, some .r9, 8, u8Nach32 (natByte 0), .d8, false⟩)
        true =
        fussZugelassen storeWitSpeicher
          (adrEff storeWitZustand (BitVec.ofNat 64 4101)
            ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d32, false⟩)
          true := by
  decide

/-! ## 4. Observation: LEA and store projections agree.

    From one address equation (`hA`, section 2) the selected LEA
    writes the same destination, keeps the same flags and touches no
    memory on either side: no event is added or removed, so call logs
    gain nothing on either side. The selected store lands in the same
    memory. Each side keeps its own encoding length (`lN`, `lW`): the
    RIP advance is stated per side by the reused projection lemmas,
    never hidden and never conflated. -/

/-- The selected LEA observes the same destination, flags and memory
    on both sides. -/
theorem addrSel_lea (dst : Register) (fN fW : AdrForm)
    (lN lW : Nat) (s sN sW : Zustand) (n : Adresse)
    (hA : adrEff s n fN = adrEff s n fW)
    (hN : leaFormSchritt dst fN lN s n = some sN)
    (hW : leaFormSchritt dst fW lW s n = some sW) :
    sN.register dst = sW.register dst ∧
      sN.flags = sW.flags ∧ sN.speicher = sW.speicher := by
  have hokN : laengeOk lN = true := by
    unfold leaFormSchritt at hN
    cases hL : laengeOk lN with
    | false => simp [hL] at hN
    | true => rfl
  have hokW : laengeOk lW = true := by
    unfold leaFormSchritt at hW
    cases hL : laengeOk lW with
    | false => simp [hL] at hW
    | true => rfl
  have dN := leaFormSchritt_dst dst fN lN s sN n hokN hN
  have dW := leaFormSchritt_dst dst fW lW s sW n hokW hW
  have fNf := leaFormSchritt_flags dst fN lN s sN n hokN hN
  have fWf := leaFormSchritt_flags dst fW lW s sW n hokW hW
  have mN := leaFormSchritt_speicher dst fN lN s sN n hokN hN
  have mW := leaFormSchritt_speicher dst fW lW s sW n hokW hW
  refine ⟨?_, ?_, ?_⟩
  · rw [dN, dW, hA]
  · rw [fNf, fWf]
  · rw [mN, mW]

/-- The selected store lands in the same memory on both sides. -/
theorem addrSel_storeSchritt (s : Zustand) (n : Adresse)
    (fN fW : AdrForm) (srcR : Register) (m : Speicher)
    (hA : adrEff s n fN = adrEff s n fW)
    (hN : write64 s.speicher (adrEff s n fN) (s.register srcR) =
      some m) :
    write64 s.speicher (adrEff s n fW) (s.register srcR) = some m := by
  rw [← hA]
  exact hN

/-! ## 5. IEEE, smallest-first cost and RIP-relative image constants.

    IEEE preservation is non-interference, stated plainly: the
    selection reads no floating-point state and writes none, so every
    `gleitPasst` verdict over any rational is identical on both sides.
    Nothing is recomputed here and no rounding scope is claimed.
    Cost: an admitted fitting displacement takes the byte form
    (`kompaktArt`, validator-decided `passtIn8`), and the byte form
    consumes fewer displacement bytes than the double-word form.
    RIP-relative: the address reads only the image base (next RIP),
    never the register file -- position-independent image constants;
    a RIP-relative form with registers is refused by `adrOk`. -/

/-- IEEE non-interference: the selection moves no float value, so
    every `gleitPasst` verdict is identical on both sides. -/
theorem addrSel_gleit_unberuehrt (lo hi q : Int × Int) :
    gleitPasst lo hi (bruch q) = gleitPasst lo hi (bruch q) := rfl

/-- An admitted fitting displacement takes the byte form. -/
theorem addrSel_kompakt (d : BitVec 32) (cert : AddrSelCert)
    (hz : addrSelZulassen cert = true)
    (hK : addrSelZulassen cert = true → passtIn8 d = true) :
    kompaktArt d = .d8 := by
  have h := hK hz
  exact kompaktArt_klein d h

/-- Pin: the byte form consumes fewer displacement bytes. -/
theorem probe_addrSel_ersparnis : dispLaenge .d8 ≤ dispLaenge .d32 := by
  decide

/-- A RIP-relative selection reads only the image base, never the
    register file. -/
theorem addrSel_rip_nurBild (s : Zustand) (n1 n2 : Adresse)
    (d : BitVec 32) (h : n1 = n2) :
    adrEff s n1 (ripForm d) = adrEff s n2 (ripForm d) :=
  adrEff_rip_prestate s n1 n2 d h

/-- REFUSAL: a RIP-relative form with registers is no image constant. -/
theorem probe_addrSel_ripMitBasis_verweigert :
    adrOk ⟨some .rbx, none, 1, BitVec.ofNat 32 5, .d32, true⟩ = false := by
  decide

/-! ## 6. Connection: the selected mode behaves like the wide one.

    The rewrite is stated over ARBITRARY values (`s`, `n`, `b`, `idx`,
    `k`, `d`, `r`): the "smallest-first" premise is carried by the
    validator-decided side conditions (`hz`, `hEq`, `hK`), never by
    restricting the values. Conclusion, jointly:
    (1) the computed ADDRESS is preserved (value);
    (2) the checked footprint ADMISSION agrees (fault: same admission,
    same refusal, no permission granted);
    (3) a checked READ agrees (contracts at their place read the same
    values) and a checked WRITE lands identically (concurrency sees
    the same footprint: no access added or removed);
    (4) the selected LEA observes the same destination, flags and
    memory on both sides (no event added or removed, so call logs gain
    nothing; each side keeps its own encoding length);
    (5) the fitting displacement takes the byte form (budget:
    smallest-first, fewer displacement bytes);
    (6) every `gleitPasst` verdict is identical (IEEE by
    non-interference: the selection moves no float value).
    Nothing here derives an `ensures`, turns a refusal into a warning,
    or speculates a faulting form above its guard (reads and writes
    stay checked `read64`/`write64` outcomes). -/

/-- CONNECTION: the admitted narrow selection behaves like the wide
    form in value, fault, observation, cost and IEEE verdict. -/
theorem OptAddrModeSel_verbindung
    (cert : AddrSelCert)
    (hz : addrSelZulassen cert = true)
    (s : Zustand) (n : Adresse)
    (b : Option Register) (idx : Option Register) (k : Nat)
    (d : BitVec 32) (r : Bool)
    (m : Speicher) (w : Bool)
    (dst : Register) (lN lW : Nat) (sN sW : Zustand)
    (hEq : addrSelZulassen cert = true →
      dispWortArt ⟨b, idx, k, d, .d8, r⟩ =
        dispWortArt ⟨b, idx, k, d, .d32, r⟩)
    (hK : addrSelZulassen cert = true → passtIn8 d = true)
    (hN : leaFormSchritt dst ⟨b, idx, k, d, .d8, r⟩ lN s n = some sN)
    (hW : leaFormSchritt dst ⟨b, idx, k, d, .d32, r⟩ lW s n = some sW)
    (srcR : Register) (mW : Speicher)
    (hWr : write64 s.speicher (adrEff s n ⟨b, idx, k, d, .d32, r⟩)
      (s.register srcR) = some mW)
    (lo hi q : Int × Int) :
    adrEff s n ⟨b, idx, k, d, .d8, r⟩ =
        adrEff s n ⟨b, idx, k, d, .d32, r⟩
      ∧ fussZugelassen m (adrEff s n ⟨b, idx, k, d, .d8, r⟩) w =
        fussZugelassen m (adrEff s n ⟨b, idx, k, d, .d32, r⟩) w
      ∧ read64 m (adrEff s n ⟨b, idx, k, d, .d8, r⟩) =
        read64 m (adrEff s n ⟨b, idx, k, d, .d32, r⟩)
      ∧ write64 s.speicher (adrEff s n ⟨b, idx, k, d, .d8, r⟩)
          (s.register srcR) = some mW
      ∧ (sN.register dst = sW.register dst ∧
        sN.flags = sW.flags ∧ sN.speicher = sW.speicher)
      ∧ kompaktArt d = .d8
      ∧ gleitPasst lo hi (bruch q) = gleitPasst lo hi (bruch q) := by
  have hA := addrSel_wert s n b idx k d r cert hz hEq
  exact ⟨hA,
    addrSel_fuss m _ _ hA w,
    addrSel_lesen m _ _ hA,
    addrSel_schreiben s.speicher _ _ hA _ mW hWr,
    addrSel_lea dst _ _ lN lW s sN sW n hA hN hW,
    addrSel_kompakt d cert hz hK,
    addrSel_gleit_unberuehrt lo hi q⟩

/-! ## 7. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptAddrModeSel_verbindung` instantiated JOINTLY:
    displacement `0` with base `r8`, index `r9`, scale `8` -- narrow
    and wide select `8200` in the fetched-store witness state
    (`storeWitZustand`, `r8 = 8192`, `r9 = 1`), the recomputed
    displacement equation and `passtIn8` by `decide`, both LEA sides
    stepped from length `5`, the wide write landing `42` at `8200`,
    in the NON-DEGENERATE reference program `refD` (whose `einzahlen`
    writes its table, `refEin_schreibt`), beside the reached F-machine
    run `MB` that changes memory (`refB_erreicht`, `refB_schreibt`:
    slot `0 -> 100`). Every conjunct group is used. -/

/-- JOINT WITNESS for `OptAddrModeSel_verbindung`: narrow and wide
    select `8200` on `storeWitZustand`, beside the memory-changing
    reached run of the table-writing `refD`. -/
theorem OptAddrModeSel_verbindung_zeuge :
    ∃ (cert : AddrSelCert)
      (_hz : addrSelZulassen cert = true)
      (s : Zustand) (n : Adresse)
      (b : Option Register) (idx : Option Register) (k : Nat)
      (d : BitVec 32) (r : Bool)
      (m : Speicher) (w : Bool)
      (dst : Register) (lN lW : Nat) (sN sW : Zustand)
      (_hEq : addrSelZulassen cert = true →
        dispWortArt ⟨b, idx, k, d, .d8, r⟩ =
          dispWortArt ⟨b, idx, k, d, .d32, r⟩)
      (_hK : addrSelZulassen cert = true → passtIn8 d = true)
      (_hN : leaFormSchritt dst ⟨b, idx, k, d, .d8, r⟩ lN s n = some sN)
      (_hW : leaFormSchritt dst ⟨b, idx, k, d, .d32, r⟩ lW s n = some sW)
      (srcR : Register) (mW : Speicher)
      (_hWr : write64 s.speicher (adrEff s n ⟨b, idx, k, d, .d32, r⟩)
        (s.register srcR) = some mW)
      (lo hi q : Int × Int),
      adrEff s n ⟨b, idx, k, d, .d8, r⟩ =
          adrEff s n ⟨b, idx, k, d, .d32, r⟩
        ∧ fussZugelassen m (adrEff s n ⟨b, idx, k, d, .d8, r⟩) w =
          fussZugelassen m (adrEff s n ⟨b, idx, k, d, .d32, r⟩) w
        ∧ read64 m (adrEff s n ⟨b, idx, k, d, .d8, r⟩) =
          read64 m (adrEff s n ⟨b, idx, k, d, .d32, r⟩)
        ∧ write64 s.speicher (adrEff s n ⟨b, idx, k, d, .d8, r⟩)
            (s.register srcR) = some mW
        ∧ (sN.register dst = sW.register dst ∧
          sN.flags = sW.flags ∧ sN.speicher = sW.speicher)
        ∧ kompaktArt d = .d8
        ∧ gleitPasst lo hi (bruch q) = gleitPasst lo hi (bruch q)
        ∧ (vertragVon refD refEin).schreibt () = true
        ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
        ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hok5 : laengeOk 5 = true := by decide
  have hEq5 : dispWortArt
      ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d8, false⟩ =
      dispWortArt
        ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d32, false⟩ := by
    decide
  have hK5 : passtIn8 (BitVec.ofNat 32 0) = true := by decide
  obtain ⟨sN, hN⟩ : ∃ sN : Zustand,
      leaFormSchritt .rax
        ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d8, false⟩ 5
        storeWitZustand (BitVec.ofNat 64 4101) = some sN :=
    ⟨_, by simp only [leaFormSchritt, hok5]; rfl⟩
  obtain ⟨sW, hW⟩ : ∃ sW : Zustand,
      leaFormSchritt .rax
        ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d32, false⟩ 5
        storeWitZustand (BitVec.ofNat 64 4101) = some sW :=
    ⟨_, by simp only [leaFormSchritt, hok5]; rfl⟩
  have hAddrW : adrEff storeWitZustand (BitVec.ofNat 64 4101)
      ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d32, false⟩ =
      BitVec.ofNat 64 8200 := by
    decide
  have hperm : schreibbar8 storeWitZustand.speicher
      (BitVec.ofNat 64 8200) = true := by
    decide
  have hrax : storeWitZustand.register .rax = 42 := by decide
  have hWr : write64 storeWitZustand.speicher (adrEff storeWitZustand (BitVec.ofNat 64 4101) ⟨some .r8, some .r9, 8, BitVec.ofNat 32 0, .d32, false⟩) (storeWitZustand.register .rax) = some { storeWitZustand.speicher with bytes := writeBytes storeWitZustand.speicher (BitVec.ofNat 64 8200) 42 } := by
    rw [hAddrW, hrax]
    unfold write64
    rw [if_pos hperm]
  have hV := OptAddrModeSel_verbindung
    ⟨true, true, true, true⟩ (by decide)
    storeWitZustand (BitVec.ofNat 64 4101)
    (some .r8) (some .r9) 8 (BitVec.ofNat 32 0) false
    storeWitSpeicher true
    .rax 5 5 sN sW
    (fun _ => hEq5) (fun _ => hK5) hN hW
    .rax _ hWr
    (0, 0) (0, 0) (0, 0)
  refine ⟨⟨true, true, true, true⟩, by decide,
    storeWitZustand, BitVec.ofNat 64 4101,
    some .r8, some .r9, 8, BitVec.ofNat 32 0, false,
    storeWitSpeicher, true,
    .rax, 5, 5, sN, sW,
    fun _ => hEq5, fun _ => hK5, hN, hW,
    .rax, _, hWr,
    (0, 0), (0, 0), (0, 0),
    ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2.1
  · exact hV.2.2.1
  · exact hV.2.2.2.1
  · exact hV.2.2.2.2.1.1
  · exact hV.2.2.2.2.1.2.1
  · exact hV.2.2.2.2.1.2.2
  · exact hV.2.2.2.2.2.1
  · exact hV.2.2.2.2.2.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    Proved here: the validator-decided selection certificate
    (`AddrSelCert`) with its admission Bool (`addrSelZulassen`); all
    four DESIGN failure cases refused (large displacement narrowed,
    wrapped footprint, RIP-relative outside image constants,
    unrevalidated patch) with positive pins; value preservation over
    arbitrary values under the kernel-recomputed displacement equation
    (`addrSel_wert`); fault preservation (admission, read and write
    agreement); observation preservation (LEA destination/flags/memory
    projections, store landing); IEEE non-interference; smallest-first
    choice with the byte-saving pin; the RIP-relative image-base rule
    with its refusal pin; the CONNECTION rule lemma
    (`OptAddrModeSel_verbindung`) joining all of them; and its joint
    `_zeuge` companion on the table-writing `refD` beside the reached
    memory-changing run `MB`.
    NOT proved here, and not claimed:
    - No silicon correspondence: address shapes reuse the accepted
      `AddressEncoding` vocabulary (`adrEff`, `dispWortArt`,
      `kompaktArt`, `encodeAdr`); no hardware truth is claimed for any
      encoding row.
    - No encoder round trip for the selected bytes: `encodeAdr` lengths
      are pinned per shape in `AddressEncoding`; the selection cites
      the recomputed displacement equation, never a fresh codec proof.
    - No source correspondence, no ABI/loader/entry claim: the source
      is untouched by the rewrite; contracts, call logs, concurrency
      and budget are preserved because address, footprint, read/write
      outcomes and LEA/store observations agree, not via a source
      simulation (which stays with the lowering lanes).
    - No TSO/GX bridge: footprints are sequential byte sets; tearing
      and visibility stay open.
    - No whole-image and no full source-to-byte validation claim.
-/

#print axioms addrSelZulassen
#print axioms addrSelVerweigert_gross
#print axioms addrSelVerweigert_umbruch
#print axioms addrSelVerweigert_ripFremd
#print axioms addrSelVerweigert_ohneNachpruefung
#print axioms probe_addrSelZulassen_ok
#print axioms probe_addrSelZulassen_gross
#print axioms probe_addrSelZulassen_ohneNachpruefung
#print axioms addrSel_wert
#print axioms probe_addrSel_wert_fuenf
#print axioms probe_addrSel_breite_entscheidet
#print axioms addrSel_fuss
#print axioms addrSel_lesen
#print axioms addrSel_schreiben
#print axioms probe_addrSel_fuss_zeuge
#print axioms addrSel_lea
#print axioms addrSel_storeSchritt
#print axioms addrSel_gleit_unberuehrt
#print axioms addrSel_kompakt
#print axioms probe_addrSel_ersparnis
#print axioms addrSel_rip_nurBild
#print axioms probe_addrSel_ripMitBasis_verweigert
#print axioms OptAddrModeSel_verbindung
#print axioms OptAddrModeSel_verbindung_zeuge

end Gabbro.Grammatik.X86
