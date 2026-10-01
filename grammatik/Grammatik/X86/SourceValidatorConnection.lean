/-
  Source-to-byte certificate connection (lane 632).

  Connects ONE genuinely checked finite source/byte certificate to its
  covered source-step representation relation. The source side is the
  accepted `SourceMemory` witness fragment (`witD`: one table with one
  `.int 0 100` field, `srcStmt` writes 42 into row 0, recomputed here in
  Lean from the typed AST, never from a Rust print). The target side is
  the accepted `LoadedExecution` store image (`bildStore`: fetched bytes
  decode to `store64 rbx rax 0`, one loaded byte step moves 42 into the
  data section), admitted by the accepted `ValidatorExecution`
  strengthened entry check. The checked Bool `srcCertOk` recomputes every
  side in Lean; `srcCert_sound` derives the joint representation,
  read-back, footprint and validator consequences from it. Mutated
  bytes/profile/map/certificate witnesses are refused by decision.
-/
import Grammatik.X86.SourceMemory
import Grammatik.X86.ValidatorExecution
import Grammatik.X86.AccessExecution

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Finite checked source/byte certificate: pure data only (profile,
    image, load bias, entry, layout extent). No proof-valued field, no
    assumed simulation, no trusted external print. -/
structure SrcByteCert where
  profil : Profil
  bild : Bild
  bias : Nat
  eintritt : Nat
  basis : Nat
  len : Nat
  off : Nat

/-- Loaded start state named by the certificate. -/
def certStart (c : SrcByteCert) : Zustand :=
  bildZustand c.bild c.bias (BitVec.ofNat 64 c.eintritt) storeReg storeFlags

/-- The source-side statement, recomputed in Lean from the typed AST:
    write 42 into row 0 of the witness table. -/
def srcStmt :=
  Stmt.assignSlot (l := false) (t := ()) (f := ()) witI witE witHw witHL

/-- The good certificate: profile 48, the accepted store image at its
    checked bias/entry, layout extent base `0x102000` length 16 offset 0
    (the data section cell the decoded store writes). -/
def srcCert : SrcByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x101000, 0x102000, 16, 0⟩

/-- The checked certificate Bool: representation admission, profile
    scope pin (the validation below is proved under `.p48`; `.p57`
    accepts the same map, so the scope is pinned explicitly), the
    strengthened entry admission, the fetched-decode shape, the source
    value in its register, effective-address agreement with the layout
    slot, readability of the target cell and the observed lowest target
    byte. Every side is recomputed in Lean from the certificate data;
    no Rust print and no assumed simulation enters. -/
def srcCertOk (c : SrcByteCert) : Bool :=
  repOk (.int 0 100) c.basis c.len c.off &&
  decide (c.profil = .p48) &&
  valEintrittStark c.profil c.bild c.bias c.eintritt storeReg storeFlags &&
  decide (fetchDekodiert (certStart c) =
    some (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0))) &&
  decide (storeReg .rax = zahlWort witVal) &&
  decide (effAddr (certStart c) .rbx 0 = slotAddr c.basis c.off) &&
  lesbar8 (certStart c).speicher (slotAddr c.basis c.off) &&
  decide (ausgangByte (slotAddr c.basis c.off) (byteschritt (certStart c)) =
    some (natByte 42))

/-- ACCEPTANCE: the good certificate passes every recomputed check:
    representation admission, profile scope, strengthened entry
    admission, fetched-decode shape, register value, address agreement,
    cell readability and the observed target byte. -/
theorem srcCert_ok : srcCertOk srcCert = true := by
  decide

/-! ## Mutated witnesses: bytes, profile, map, certificate. -/

/-- Mutated bytes: the forged opcode image at the same bias/entry. -/
def srcCertMutiertBytes : SrcByteCert :=
  ⟨.p48, bildStoreMutiert, 0x100000, 0x101000, 0x102000, 16, 0⟩

/-- Mutated profile: the same image under `.p57`, outside the pinned scope. -/
def srcCertProfil57 : SrcByteCert :=
  ⟨.p57, bildStore, 0x100000, 0x101000, 0x102000, 16, 0⟩

/-- Mutated map: the writable-code image refuses the mapping leg. -/
def srcCertWx : SrcByteCert :=
  ⟨.p48, bildStoreWx, 0x100000, 0x101000, 0x102000, 16, 0⟩

/-- Mutated certificate: the same image and entry, but the layout base
    names `4096` instead of the store target `0x102000`. Representation
    admission still holds there; the address agreement does not. -/
def srcCertFalschBasis : SrcByteCert :=
  ⟨.p48, bildStore, 0x100000, 0x101000, 4096, 16, 0⟩

/-- BYTES REFUSAL: the forged opcode byte defeats fetch-and-decode,
    so the strengthened entry leg and the decode-shape leg both fail
    while the checked mapping still holds. -/
theorem srcCert_mutiert_bytes_verweigert :
    srcCertOk srcCertMutiertBytes = false := by
  decide

/-- PROFILE REFUSAL: `.p57` accepts the same map, but the certificate
    scope is pinned to `.p48`, so the profile leg fails. -/
theorem srcCert_profil57_verweigert :
    srcCertOk srcCertProfil57 = false := by
  decide

/-- MAP REFUSAL: writable code is not an accepted image, so the
    strengthened entry leg fails. -/
theorem srcCert_wx_verweigert :
    srcCertOk srcCertWx = false := by
  decide

/-- CERTIFICATE REFUSAL: the wrong layout base keeps representation
    admission but breaks the effective-address agreement. -/
theorem srcCert_falschBasis_verweigert :
    srcCertOk srcCertFalschBasis = false := by
  decide

/-- SOURCE EXECUTION (recomputed in Lean): the AST statement runs on
    the witness world, writing 42 into row 0 (zero before). This is the
    covered source step the certificate claims; the statement is the
    Lean text above, evaluated by the goal's own `execStmt`. -/
theorem srcStmt_ausgefuehrt :
    ∃ (σ' : World witD) (ρ' : Env witD []),
      execStmt witO 0 witR srcStmt witSigma Env.nil = .ok σ' ρ' ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 := by
  have hExecFull : ∃ σ' ρ',
      execStmt witO 0 witR srcStmt witSigma Env.nil = .ok σ' ρ' := by
    simp only [srcStmt, execStmt]
    exact ⟨_, _, rfl⟩
  obtain ⟨σ', ρ', hExec⟩ := hExecFull
  refine ⟨σ', ρ', hExec, rfl, ?_⟩
  cases hExec
  rfl

/-! ## Certificate soundness: the accepted Bool implies the joint
    source/target representation. -/

/-- CERTIFICATE SOUNDNESS: from the accepted Bool, the covered source
    step (`srcStmt` writes 42 into the witness slot) and the decoded
    loaded step (fetched `store64 rbx rax 0` writes the same value)
    agree on the admitted slot: the representation holds at the joint
    post-states, the source slot reads 42, the target word reads back
    and parses to the source value, the image stays accepted with its
    entry contained, and the realised footprint is exactly the slot.
    Every premise is used: `hRep` admits the slot, `hProf` pins the
    profile of the validator leg, `hVal` admits the entry and yields
    the mapping legs, `hFetch` identifies the decoded store,
    `hReg`/`hAddr` tie the stored word and address to the source side,
    `hLesbar` feeds both read-backs, `hByte` excludes the refused
    byte step. -/
theorem srcCert_sound (c : SrcByteCert) (h : srcCertOk c = true) :
    ∃ (σ' : World witD) (ρ' : Env witD []) (s' : Zustand),
      execStmt witO 0 witR srcStmt witSigma Env.nil = .ok σ' ρ' ∧
      byteschritt (certStart c) = .weiter s' ∧
      RepSlot () 0 () 0 100 witHT (slotAddr c.basis c.off) s'.speicher σ' ∧
      (σ'.slots () 0 ()).n = 42 ∧
      read64 s'.speicher (slotAddr c.basis c.off) = some (zahlWort witVal) ∧
      wortZahl 0 100 (zahlWort witVal) = some witVal ∧
      wohlgeformt .p48 c.bild = true ∧
      eintragEnthalten c.bias c.bild.abschnitte c.eintritt = true ∧
      (zugriff ⟨.store64 .rbx .rax 0, 7⟩ (certStart c)).schreiben =
        Fuss (slotAddr c.basis c.off) := by
  have hSplit := h
  unfold srcCertOk at hSplit
  simp only [Bool.and_eq_true_iff] at hSplit
  obtain ⟨⟨⟨⟨⟨⟨⟨hRep, hProf⟩, hVal⟩, hFetch⟩, hReg⟩, hAddr⟩, hLesbar⟩,
    hByte⟩ := hSplit
  have hProfEq : c.profil = .p48 := of_decide_eq_true hProf
  rw [hProfEq] at hVal
  have hWf : wohlgeformt .p48 c.bild = true :=
    valStark_wohlgeformt .p48 c.bild c.bias c.eintritt storeReg storeFlags hVal
  have hEintrag : eintragEnthalten c.bias c.bild.abschnitte c.eintritt = true :=
    valStark_eintrag .p48 c.bild c.bias c.eintritt storeReg storeFlags hVal
  have hOk : repOk (witD.typ () ()) c.basis c.len c.off = true := by
    rw [witHT]; exact hRep
  have hFetchEq : fetchDekodiert (certStart c) =
      some (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0)) :=
    of_decide_eq_true hFetch
  have hByteEq : ausgangByte (slotAddr c.basis c.off)
      (byteschritt (certStart c)) = some (natByte 42) :=
    of_decide_eq_true hByte
  have hRegEq : storeReg .rax = zahlWort witVal := of_decide_eq_true hReg
  have hAddrEq : effAddr (certStart c) .rbx 0 = slotAddr c.basis c.off :=
    of_decide_eq_true hAddr
  match hs : byteschritt (certStart c) with
  | .weiter s' =>
    have hDecomp := byte_aus_weiter (certStart c) s' hs
    obtain ⟨d', rest', hf, hst⟩ := hDecomp
    have hPair : (d', rest') =
        (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0)) :=
      Option.some_inj.mp (by rw [← hf]; exact hFetchEq)
    have hdEq : d' = ⟨.store64 .rbx .rax 0, 7⟩ := congrArg Prod.fst hPair
    have hbef : d'.befehl = .store64 .rbx .rax 0 := by rw [hdEq]
    have hlen : d'.laenge = 7 := by rw [hdEq]
    have hok7 : laengeOk d'.laenge = true := by rw [hlen]; decide
    have hFound := realisiert_store64_gefunden d' (certStart c) s' .rbx .rax
      0 hok7 hbef hst
    obtain ⟨m, hTgt0, -, -, -⟩ := hFound
    have hStartReg : (certStart c).register = storeReg := rfl
    have hTgt : write64 (certStart c).speicher (slotAddr c.basis c.off)
        (zahlWort witVal) = some m := by
      rw [← hAddrEq, ← hRegEq, ← hStartReg]
      exact hTgt0
    have hSchritt := schritt_store64_erfolg d' (certStart c) .rbx .rax 0 m
      hok7 hbef hTgt0
    have hMem : s'.speicher = m := by
      have hEq := hst.symm.trans hSchritt
      have hInj := Option.some_inj.mp hEq
      have h2 := congrArg Zustand.speicher hInj
      simpa using h2
    have hTgt' : write64 (certStart c).speicher (slotAddr c.basis c.off)
        (zahlWort witVal) = some s'.speicher := by
      rw [hMem]; exact hTgt
    obtain ⟨σSrc, ρSrc, hExec, -, hAfter⟩ := srcStmt_ausgefuehrt
    have hRepMain := rep_schritt_bleibt (D := witD) (V := witV) (l := false)
      (Γ := []) (Λ := []) witO 0 witR () () 0 100 witHT
      c.basis c.len c.off hOk witI witE witHw witHL
      witSigma Env.nil witSL rfl 0 witVal rfl rfl
      (slotAddr c.basis c.off) _ _ _ _ hExec hTgt' hLesbar
    have hRead : read64 s'.speicher (slotAddr c.basis c.off) =
        some (zahlWort witVal) :=
      read64_nach_write64 _ _ _ _ hTgt' hLesbar
    have hRound : wortZahl 0 100 (zahlWort witVal) = some witVal :=
      zahlWort_wortZahl witVal (by decide) (by decide)
    have hFuss := realisiert_store64_fuss d' (certStart c) s' .rbx .rax 0
      hok7 hbef hst
    have hFussEq : (zugriff ⟨.store64 .rbx .rax 0, 7⟩
        (certStart c)).schreiben = Fuss (slotAddr c.basis c.off) := by
      have h2 := hFuss.2.1
      rw [hdEq, hAddrEq] at h2
      exact h2
    exact ⟨σSrc, ρSrc, s', hExec, rfl, hRepMain.1, hAfter, hRead, hRound,
      hWf, hEintrag, hFussEq⟩
  | .verweigert =>
    have hNone : ausgangByte (slotAddr c.basis c.off) .verweigert = none :=
      rfl
    rw [hs] at hByteEq
    rw [hNone] at hByteEq
    cases hByteEq

/-! ## Joint witness: nondegenerate source table-write and reached
    memory-changing steps on both sides, plus planted refusals. -/

/-- JOINT WITNESS for `srcCert_sound`: every premise holds jointly on
    the good certificate — the accepted Bool, the covered source run
    (table written 0 → 42 by the witness function) and the certified
    loaded step (target lowest byte 0 → 42) with the representation at
    the joint post-states — together with all four planted refusals.
    The source side is nondegenerate (one table the function writes);
    both runs reach a memory-changing step. -/
theorem srcCert_sound_zeuge :
    ∃ (σ' : World witD) (ρ' : Env witD []) (s' : Zustand),
      srcCertOk srcCert = true ∧
      execStmt witO 0 witR srcStmt witSigma Env.nil = .ok σ' ρ' ∧
      byteschritt (certStart srcCert) = .weiter s' ∧
      RepSlot () 0 () 0 100 witHT (slotAddr srcCert.basis srcCert.off)
        s'.speicher σ' ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (σ'.slots () 0 ()).n = 42 ∧
      (certStart srcCert).speicher.bytes
        (slotAddr srcCert.basis srcCert.off) = BitVec.ofNat 8 0 ∧
      ausgangByte (slotAddr srcCert.basis srcCert.off)
        (byteschritt (certStart srcCert)) = some (natByte 42) ∧
      srcCertOk srcCertMutiertBytes = false ∧
      srcCertOk srcCertProfil57 = false ∧
      srcCertOk srcCertWx = false ∧
      srcCertOk srcCertFalschBasis = false := by
  obtain ⟨σ', ρ', s', hExec, hStep, hRep, hAfter, -, -, -, -, -⟩ :=
    srcCert_sound srcCert srcCert_ok
  have hPre : (certStart srcCert).speicher.bytes
      (slotAddr srcCert.basis srcCert.off) = BitVec.ofNat 8 0 := by
    decide
  have hPost : ausgangByte (slotAddr srcCert.basis srcCert.off)
      (byteschritt (certStart srcCert)) = some (natByte 42) := by
    decide
  exact ⟨σ', ρ', s', srcCert_ok, hExec, hStep, hRep, rfl, hAfter, hPre,
    hPost, srcCert_mutiert_bytes_verweigert, srcCert_profil57_verweigert,
    srcCert_wx_verweigert, srcCert_falschBasis_verweigert⟩

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary
    (`SourceMemory.repOk`/`zahlWort`/`wortZahl`/`RepSlot`/
    `rep_schritt_bleibt` with the `witD` witness fragment,
    `ValidatorExecution.valEintrittStark`/`valStark_wohlgeformt`/
    `valStark_eintrag`, `LoadedExecution.bildStore`/`bildZustand`,
    `Byteschritt.fetchDekodiert`/`byteschritt`/`byte_aus_weiter`,
    `AccessExecution.realisiert_store64_gefunden`/
    `realisiert_store64_fuss`, `Ausfuehrung.schritt_store64_erfolg`,
    `Speicher.read64_nach_write64`): one genuinely checked finite
    source/byte certificate (`SrcByteCert`: profile, image, bias, entry,
    layout extent — pure data, no proof-valued field, no assumed
    simulation) with its recomputed Bool (`srcCertOk`: admission,
    profile scope, strengthened entry admission, fetched-decode shape,
    register value, address agreement, cell readability, observed byte),
    the recomputed source statement (`srcStmt`, evaluated by the goal's
    own `execStmt`), the soundness theorem (`srcCert_sound`: the covered
    source step and the decoded loaded step agree — representation at
    the joint post-states, source slot 42, target word read-back and
    parse, mapping and entry legs, realised footprint exactly the slot),
    acceptance by decision, four planted refusals (mutated bytes,
    mutated profile, mutated map, mutated certificate base) and one
    joint nondegenerate memory-changing witness on both sides.
    NOT proved here, and not claimed:
    - No `valX86_sound`: nothing here claims an admitted image is the
      emitted form of an arbitrary source program. The connection covers
      exactly one fragment: one `.int 0 100` slot, one `assignSlot`
      form, one decoded store image. General CFG, calls, loops,
      concurrency, other widths/forms stay OPEN.
    - No hardware claim: bytes are model `Byte` lists, memory the model
      `Speicher`; silicon, caches, TLBs, store buffers, interrupts,
      faults beyond the decoded refusal and timing are OPEN.
    - No multi-step control-flow, relocation re-decode, gate/OS contract
      (user logic, never an assumption), cost/time or termination claim.
      `verweigert` is the absence of a transition.
    - Profile scope is pinned to `.p48`: `.p57` accepts the same map, so
      the certificate refuses it by an explicit scope leg, not by a
      mapping difference.
    - Full source-to-final-loaded-bytes validation remains OPEN until a
      generic closing proof is derived.
-/

#print axioms srcCert_ok
#print axioms srcCert_mutiert_bytes_verweigert
#print axioms srcCert_profil57_verweigert
#print axioms srcCert_wx_verweigert
#print axioms srcCert_falschBasis_verweigert
#print axioms srcStmt_ausgefuehrt
#print axioms srcCert_sound
#print axioms srcCert_sound_zeuge

end Gabbro.Grammatik.X86
