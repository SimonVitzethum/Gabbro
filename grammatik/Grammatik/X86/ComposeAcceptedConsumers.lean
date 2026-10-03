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

/-- Same window through the core projection (definitional twin). -/
theorem gesamtWit_hwin' :
    geholt (projZustand gesamtWitM 0) = encode gesamtWitBf ++ [] :=
  gesamtWit_hwin

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

/-- Admission holds over the fetched pilot window. -/
theorem gesamtWit_zugelassen :
    extZugelassen (projFp gesamtWitM 0)
      (geholt (projZustand gesamtWitM 0))
      (.pilot ⟨gesamtWitBf, (encode gesamtWitBf).length⟩) [] = true := by
  have hlen : (geholt (projZustand gesamtWitM 0)).length =
      (encode gesamtWitBf).length := by
    have h := congrArg List.length gesamtWit_hwin'
    simpa using h
  have hok : laengeOk (encode gesamtWitBf).length = true := by
    decide
  unfold extZugelassen
  simp [extLen, hlen, hok, gesamtWit_hexe]

/-- The fetched window decodes to the pilot move. -/
theorem gesamtWit_hdec :
    decodeExt (geholt (projFp gesamtWitM 0).kern) =
      some ((.pilot ⟨gesamtWitBf, (encode gesamtWitBf).length⟩), []) := by
  rw [gesamtWit_hwin]
  exact decodeExt_kanonisch _ _ _ (roundtrip gesamtWitBf [])

/-- No fetch candidate over the admitted pilot window. -/
theorem gesamtWit_abruf : abrufKandidat (projFp gesamtWitM 0) = none := by
  apply abruf_zugelassen_keiner _ _ _ kanonisch_code _ gesamtWit_hdec
    gesamtWit_zugelassen
  rw [gesamtWit_hwin]
  decide

/-- No decode candidate over the admitted pilot window. -/
theorem gesamtWit_nodec :
    dekodiereKandidat (projFp gesamtWitM 0) illLeer = none :=
  dekodiere_erfolg_keiner _ _ _ _ gesamtWit_hdec

/-- The ordered row is silent at the witness: no data access, a quiet
    divide flag, disarmed control. -/
theorem gesamtWit_quiet :
    ersteWahl (kandidatenReihe (projFp gesamtWitM 0) divZ pgHell stStumpf
      illLeer false) = none := by
  have habruf := gesamtWit_abruf
  have hdec := gesamtWit_nodec
  have hadr : adressKandidat divZ = none := rfl
  have hzug : zugriffKandidat (projFp gesamtWitM 0) divZ pgHell = none := rfl
  have hteil : teilungsKandidat false = none := rfl
  have hst : steuerKandidat divZ stStumpf = none :=
    steuerung_entschaerft_keiner divZ stStumpf rfl
  simp [ersteWahl, kandidatenReihe, habruf, hdec, hadr, hzug, hteil, hst]

/-- Joint inhabitant of the closing: every premise holds together on
    the reached pilot-move run (RIP 4096 to 4099, rax 5 to 9); the
    memory gate holds because the move is register-only. The
    `HwSchritt` leg reuses the closing itself. -/
theorem composeAccepted_gesamt_zeuge :
    ∃ (m : HwMaschine) (c : Nat) (i : ExtInstr) (rest : List Byte)
      (t' : FpZustand),
      (fetchExt (projFp m c) (geholt (projZustand m c)) = some (i, rest)) ∧
      (stepExt i (projFp m c) (m.bereit c) = .weiter t') ∧
      t'.kern.speicher = m.mem ∧
      ersteWahl (kandidatenReihe (projFp m c) divZ pgHell stStumpf
        illLeer false) = none ∧
      HwSchritt m (setKernVonFp m c t') (.regAusf c i) := by
  refine ⟨gesamtWitM, 0, _, _, _, gesamtWit_fetch, gesamtWit_step,
    gesamtWit_hmem, gesamtWit_quiet, ?_⟩
  exact (composeAccepted_gesamt gesamtWitM 0 _ _ gesamtWitT1 divZ pgHell
    stStumpf illLeer false gesamtWit_fetch gesamtWit_step
    gesamtWit_hmem gesamtWit_quiet).2.2.1

/-- JOINT WITNESS across the accepted consumers: a fetched
    register-only run on the coherent machine, an integer store
    drained into shared memory (0 becomes 4), a fetched LOCK XADD
    through a scaled address (byte 8201 becomes 32), both address
    spellings naming 8200, the divide-trap priority choice on fetched
    bytes with its halt verdict, the same-level stack input, and the
    three planted pending refusals (width, LOCK, FP). Non-degenerate:
    two independent memory-changing runs beside the reached
    register run. -/
theorem composeAccepted_zeuge :
    hwRipOut hwWitO1 0 = some (BitVec.ofNat 64 4099) ∧
      hwRegOut hwWitO1 0 .rax = some (BitVec.ofNat 64 9) ∧
      concWitMem.bytes concWitA = BitVec.ofNat 8 0 ∧
      concWitNachFlush = some (some (BitVec.ofNat 8 4)) ∧
      (lockAdrWit.zu.speicher.bytes (BitVec.ofNat 64 8201) =
          BitVec.ofNat 8 0 ∧
        (match lockXaddGeholt 0 lockAdrWit with
        | .ok m' ev =>
          some (m'.zu.speicher.bytes (BitVec.ofNat 64 8201),
            ev.gelesen, ev.geschrieben, m'.zu.register .r8, m'.zu.rip)
        | _ => none) =
        some (BitVec.ofNat 8 32, some 0,
          some (BitVec.ofNat 64 8192), 0, BitVec.ofNat 64 4103)) ∧
      (adrEff lockAdrWit.zu (ripNach lockAdrWit.zu.rip 7)
          ⟨some .r8, some .rcx, 8, u8Nach32 (natByte 0), .d8, false⟩ =
          BitVec.ofNat 64 8200 ∧
        adrEff lockRipWit.zu (ripNach lockRipWit.zu.rip 9)
            (ripForm (BitVec.ofNat 32 4095)) =
          BitVec.ofNat 64 8200) ∧
      ersteWahl
          (kandidatenReihe divFalleStart divZ pgDunkel stStumpf illLeer
            true) = some ⟨.teilung, .de⟩ ∧
      bindeUrteil (extByteschritt divFalleStart extWitBereit)
          (ersteWahl
            (kandidatenReihe divFalleStart divZ pgDunkel stStumpf illLeer
              true)) = .fehler ⟨.teilung, .de⟩ ∧
      waehleStapel concWitMem idtWitSteuer 0 0 false 0 = .behalten 0 ∧
      decodeExt [natByte 102, natByte 137, natByte 216] = none ∧
      decodeExt [natByte 240, natByte 77, natByte 15, natByte 193,
        natByte 68, natByte 200, natByte 0] = none ∧
      decodeExt [natByte 243, natByte 15, natByte 16,
        natByte 192] = none := by
  refine ⟨hwWit_o1_rip, hwWit_o1_rax, concWit_anfang_null,
    concWit_spuelung, lockXaddGeholt_zeuge, adress_formen_alias_pin,
    wahl_divFalle, urteil_divFalle,
    waehleStapel_behalten concWitMem idtWitSteuer 0 0, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

/- CUTS:
   Proved here (all by composing already-accepted theorems; no
   decoder, evaluator, fetch, admission, address, priority,
   descriptor or stack fact is re-proved, and no second executor
   is defined):
   - the pending-family enumeration `PendingFam` (width rows
     696/698, LOCK 722, FP 724, paging 726, control 734, context
     736, AVX2 690, returns 708) with its lane-number audit
     `familienCode`;
   - the gap closing `composeAccepted_luecken` (every family
     refused through its dispatcher pin, exhaustive arms, so a
     silent widening is a type error) with its inhabitant;
   - the 738 quiet-row projections (`reiheOhneAbruf/Dekodiere/
     Adresse/Zugriff`: a silent ordered row carries no per-stage
     candidate);
   - the fetched-execution closing `composeAccepted_gesamt`
     (fetched bytes to `HwSchritt.reg` runs: 824 decoder agreement
     and dispatcher selection, the 660 register-path gate, 738
     priority silence on address and access, pending families
     threaded through as still open);
   - the joint inhabitant `composeAccepted_gesamt_zeuge` (all
     closing premises together on a reached pilot-move run);
   - the cross-piece joint witness `composeAccepted_zeuge`
     (fetched register run, integer drain 0 to 4, fetched LOCK
     XADD, both address spellings of 8200, divide-trap choice with
     halt verdict, same-level stack input, three planted pending
     refusals).
   NOT proved here, and not claimed:
   - No per-family canonical-byte closing beyond the accepted pins;
     the `istOffen` pins show dispatcher refusal, not row
     ownership (which bytes each pending family will accept stays
     with lanes 696/698/722/724/726/734/736/690/708).
   - No hardware correspondence, no source/IR correspondence, no
     TSO/W/GX bridge beyond the reused accepted rows, no ABI/
     loader/entry/budget connection, no whole-image coverage.
   - `verweigert` is the absence of a transition, never a
     termination claim. Near `ret` (`0xC3`) stays accepted pilot;
     the returns pin uses `iret`.
   - At the hardware layer there is no Gabbro source program, so
     "table-writing function" has no literal witness here:
     non-degeneracy is witnessed by two independent
     memory-changing reached runs beside the register run.
   - Pending families are never imported (especially not modules
     owned by lanes 718/722/724/726/734/736/690/708/696/698),
     never assumed, and never closed by a premise shaped like the
     conclusion.
-/

#print axioms familienCode
#print axioms composeAccepted_luecken
#print axioms composeAccepted_luecken_zeuge
#print axioms reiheOhneAbruf
#print axioms reiheOhneDekodiere
#print axioms reiheOhneAdresse
#print axioms reiheOhneZugriff
#print axioms composeAccepted_gesamt
#print axioms composeAccepted_gesamt_zeuge
#print axioms composeAccepted_zeuge

end Gabbro.Grammatik.X86
