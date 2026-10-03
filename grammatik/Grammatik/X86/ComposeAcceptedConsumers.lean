/-
  File:      Grammatik/X86/ComposeAcceptedConsumers.lean
  Subject:   Close the accepted consumers through the common dispatcher.

  Lane 1104: ONE fetched-execution closing over HwMaschine from
  already-accepted pieces: the 824 decode-to-execution closing as
  dispatch backbone, the 720 integer-to-TSO rows, the 730 address
  adapter, the 738 fault-priority relation, and 728 descriptor/stack
  inputs where entry-adjacent rows need them. Reuses
  decodeExt/stepExt/extByteschritt (575/660 line) and the 824
  composition lemmas; no second executor. Every not-yet-accepted
  producer family stays an explicit pending extension enumerated in
  CUTS, never imported, never assumed.
-/
import Grammatik.X86.ComposeDecodeExec
import Grammatik.X86.ConcurrentIntegerExecution
import Grammatik.X86.AddressedHardwareExecution
import Grammatik.X86.ExceptionPriorityHardware
import Grammatik.X86.InterruptDescriptorHardware
import Grammatik.X86.HardwareExecution

namespace Gabbro.Grammatik.X86

/-- Pending producer families, by owning lane number: width rows
    696/698, LOCK 722, scalar FP 724, paging 726, control 734,
    context 736, AVX2 690, returns 708. Explicit, never imported,
    never assumed, never closed by a premise shaped like the
    conclusion. -/
inductive PendingFam where
  | breite696
  | breite698
  | lock722
  | fp724
  | seiten726
  | steuer734
  | kontext736
  | avx690
  | rueck708
  deriving DecidableEq, Repr

/-- Owning lane number of each pending family (audit only). -/
def familienCode : PendingFam → Nat
  | .breite696 => 696
  | .breite698 => 698
  | .lock722 => 722
  | .fp724 => 724
  | .seiten726 => 726
  | .steuer734 => 734
  | .kontext736 => 736
  | .avx690 => 690
  | .rueck708 => 708

/-- Dispatcher-refusal pin per pending family: representative bytes
    from each family's region that the accepted unified dispatcher
    refuses today. The LOCK pin reuses the closed 730 witness bytes
    (`lockAdrWitBild`): the adapter takes exactly what the dispatcher
    refuses. Near `ret` (`0xC3`) stays accepted pilot, so the returns
    pin uses `iret` (`0xCF`). These pins show refusal, not row
    ownership: which bytes each family will accept stays with the
    owning lanes. -/
def istOffen : PendingFam → Prop
  | .breite696 => decodeExt [natByte 102, natByte 137, natByte 216] = none
  | .breite698 => decodeExt [natByte 64, natByte 144] = none
  | .lock722 => decodeExt [natByte 240, natByte 77, natByte 15, natByte 193,
      natByte 68, natByte 200, natByte 0] = none
  | .fp724 => decodeExt [natByte 243, natByte 15, natByte 16,
      natByte 192] = none
  | .seiten726 => decodeExt [natByte 15, natByte 1, natByte 56] = none
  | .steuer734 => decodeExt [natByte 15, natByte 11] = none
  | .kontext736 => decodeExt [natByte 15, natByte 174, natByte 0] = none
  | .avx690 => decodeExt [natByte 197, natByte 248, natByte 119] = none
  | .rueck708 => decodeExt [natByte 207] = none

/-- LUECKEN: every pending family stays open through its refusal pin.
    The explicit `cases ... with` arms enumerate all nine families,
    so adding a family without a pin is a type error. -/
theorem composeAccepted_luecken (p : PendingFam) : istOffen p := by
  cases p with
  | breite696 => unfold istOffen; decide
  | breite698 => unfold istOffen; decide
  | lock722 => unfold istOffen; decide
  | fp724 => unfold istOffen; decide
  | seiten726 => unfold istOffen; decide
  | steuer734 => unfold istOffen; decide
  | kontext736 => unfold istOffen; decide
  | avx690 => unfold istOffen; decide
  | rueck708 => unfold istOffen; decide

/-- The gap enumeration is inhabited: the LOCK family is open. -/
theorem composeAccepted_luecken_zeuge : ∃ (p : PendingFam), istOffen p :=
  ⟨.lock722, composeAccepted_luecken .lock722⟩

/-- A silent ordered row carries no fetch candidate (738 interface). -/
theorem reiheOhneAbruf (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool)
    (h : ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = none) :
    abrufKandidat t = none := by
  cases ha : abrufKandidat t with
  | some f => simp [ersteWahl, kandidatenReihe, ha] at h
  | none => rfl

/-- A silent ordered row carries no decode candidate. -/
theorem reiheOhneDekodiere (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool)
    (h : ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = none) :
    dekodiereKandidat t ill = none := by
  have ha := reiheOhneAbruf t z pg st ill teiltFalle h
  cases hd : dekodiereKandidat t ill with
  | some f => simp [ersteWahl, kandidatenReihe, ha, hd] at h
  | none => rfl

/-- A silent ordered row carries no address candidate. -/
theorem reiheOhneAdresse (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool)
    (h : ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = none) :
    adressKandidat z = none := by
  have ha := reiheOhneAbruf t z pg st ill teiltFalle h
  have hd := reiheOhneDekodiere t z pg st ill teiltFalle h
  cases had : adressKandidat z with
  | some f => simp [ersteWahl, kandidatenReihe, ha, hd, had] at h
  | none => rfl

/-- A silent ordered row carries no access candidate. -/
theorem reiheOhneZugriff (t : FpZustand) (z : ZugriffsBeschreibung)
    (pg : SeitenInfo) (st : SteuerInfo) (ill : IllegalInfo)
    (teiltFalle : Bool)
    (h : ersteWahl (kandidatenReihe t z pg st ill teiltFalle) = none) :
    zugriffKandidat t z pg = none := by
  have ha := reiheOhneAbruf t z pg st ill teiltFalle h
  have hd := reiheOhneDekodiere t z pg st ill teiltFalle h
  have had := reiheOhneAdresse t z pg st ill teiltFalle h
  cases hz : zugriffKandidat t z pg with
  | some f => simp [ersteWahl, kandidatenReihe, ha, hd, had, hz] at h
  | none => rfl

/-- CLOSING through the common dispatcher over `HwMaschine`: a
    fetched instruction whose unified rule succeeds with unchanged
    canonical memory runs as a coherent `HwSchritt.reg` step, with
    decoder agreement (824 backbone) and a silent ordered row (738:
    no address and no access candidate pending). The pending families
    thread through as still open, never assumed. -/
theorem composeAccepted_gesamt (m : HwMaschine) (c : Nat)
    (i : ExtInstr) (rest : List Byte) (t' : FpZustand)
    (z : ZugriffsBeschreibung) (pg : SeitenInfo) (st : SteuerInfo)
    (ill : IllegalInfo) (teiltFalle : Bool)
    (hfetch : fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (i, rest))
    (hstep : stepExt i (projFp m c) (m.bereit c) = .weiter t')
    (hmem : t'.kern.speicher = m.mem)
    (hquiet : ersteWahl (kandidatenReihe (projFp m c) z pg st ill
      teiltFalle) = none) :
    decodeExt (geholt (projZustand m c)) = some (i, rest) ∧
      extByteschritt (projFp m c) (m.bereit c) = .weiter t' ∧
      HwSchritt m (setKernVonFp m c t') (.regAusf c i) ∧
      adressKandidat z = none ∧
      zugriffKandidat (projFp m c) z pg = none ∧
      ∀ (p : PendingFam), istOffen p := by
  refine ⟨(fetchTrifftDekodierer (projFp m c) i rest hfetch).1,
    extByteschritt_weiter (projFp m c) (m.bereit c) i rest (.weiter t')
      hfetch hstep,
    HwSchritt.reg c i t' hstep hmem,
    reiheOhneAdresse (projFp m c) z pg st ill teiltFalle hquiet,
    reiheOhneZugriff (projFp m c) z pg st ill teiltFalle hquiet,
    composeAccepted_luecken⟩

/-- Witness instruction: pilot `movReg64 rax, rcx` (register-only,
    so the `HwSchritt.reg` memory gate holds). -/
def gesamtWitBf : Befehl := .movReg64 .rax .rcx

/-- Witness image: the single pilot encoding at 4096. -/
def gesamtWitBild : List Byte := encode gesamtWitBf

/-- Witness code bytes: the image at 4096, zeroes elsewhere. -/
def gesamtWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match gesamtWitBild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness code permission: exactly the 3 image bytes, so the
    fetched window is exactly the encoding with an empty suffix. -/
def gesamtWitCode (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 3)

/-- Witness data permission: eight bytes at 8192. -/
def gesamtWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness shared memory: code is execute-only, data read/write. -/
def gesamtWitMem : Speicher :=
  { bytes := gesamtWitBytes, lesbar := gesamtWitDaten,
    schreibbar := gesamtWitDaten, ausfuehrbar := gesamtWitCode }

/-- Witness core-0 registers: value 9 in rcx, 5 in rax. -/
def gesamtWitReg : Register → Wort := fun q =>
  if q = Register.rcx then BitVec.ofNat 64 9
  else if q = Register.rax then BitVec.ofNat 64 5
  else if q = Register.rsp then BitVec.ofNat 64 8704
  else BitVec.ofNat 64 0

/-- Witness cores: core 0 runs at 4096, others idle on data. -/
def gesamtWitKern : Nat → HwKern
  | 0 => ⟨gesamtWitReg, zeugeFlags, BitVec.ofNat 64 4096,
      fun _ => BitVec.ofNat 128 0, kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 8192, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness machine: shared memory, running core, empty buffers,
    full silicon with the admitted readiness profile. -/
def gesamtWitM : HwMaschine :=
  ⟨gesamtWitMem, gesamtWitKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- The pilot encoding is 3 bytes long. -/
theorem gesamtWit_len3 : (encode gesamtWitBf).length = 3 := by
  decide

/-- The fetched window is exactly the pilot encoding. -/
theorem gesamtWit_hwin :
    geholt (projFp gesamtWitM 0).kern = encode gesamtWitBf ++ [] := by
  decide

/-- The 3 image bytes are executable. -/
theorem gesamtWit_hexe :
    ausfuehrbarN (projFp gesamtWitM 0).kern.speicher
      (projFp gesamtWitM 0).kern.rip
      (encode gesamtWitBf).length = true := by
  decide

/-- The dispatcher fetches the pilot move with an empty suffix. -/
theorem gesamtWit_fetch :
    fetchExt (projFp gesamtWitM 0) (geholt (projZustand gesamtWitM 0)) =
      some (.pilot ⟨gesamtWitBf, (encode gesamtWitBf).length⟩, []) :=
  (pilotKanonischErreicht (projFp gesamtWitM 0) (gesamtWitM.bereit 0)
    gesamtWitBf [] gesamtWit_hwin gesamtWit_hexe).1

/-- Witness successor core state: rax holds 9, RIP past the move. -/
def gesamtWitS1 : Zustand :=
  schrittRegister (projZustand gesamtWitM 0)
    (ripNach (projZustand gesamtWitM 0).rip (encode gesamtWitBf).length)
    (projZustand gesamtWitM 0).flags .rax
    ((projZustand gesamtWitM 0).register .rcx)

/-- Witness successor FP state after the move. -/
def gesamtWitT1 : FpZustand := { projFp gesamtWitM 0 with kern := gesamtWitS1 }

/-- The unified rule runs the register move: rax takes rcx. -/
theorem gesamtWit_step :
    stepExt (.pilot ⟨gesamtWitBf, (encode gesamtWitBf).length⟩)
      (projFp gesamtWitM 0) (gesamtWitM.bereit 0) =
      .weiter gesamtWitT1 := by
  apply hwPilot_weiter
  exact schritt_movReg64 _ _ .rax .rcx (by decide) rfl

/-- The move keeps canonical memory: the `HwSchritt.reg` gate. -/
theorem gesamtWit_hmem : gesamtWitT1.kern.speicher = gesamtWitM.mem := rfl

/- CUTS:
   Proved here so far: the pending-family enumeration `PendingFam`
   with its lane-number audit `familienCode`, and the gap closing
   `composeAccepted_luecken` (every family refused through its pin,
   exhaustive arms) with its inhabitant.
   NOT proved here, and not claimed: the fetched-execution closing,
   the integer/TSO, address, priority and descriptor/stack
   composition, the joint witness and the planted probes. Pending
   families are never imported (especially not modules owned by lanes
   718/722/724/726/734/736/690/708/696/698), never assumed, and never
   closed by a premise shaped like the conclusion. The `istOffen`
   pins show dispatcher refusal, not row ownership.
-/

#print axioms familienCode
#print axioms composeAccepted_luecken
#print axioms composeAccepted_luecken_zeuge

end Gabbro.Grammatik.X86
