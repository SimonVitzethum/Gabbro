/-
  File:      Grammatik/X86/IndirectCallProv.lean
  Subject:   Indirect CALL target provenance for function pointers and
             entry-fn values.

  Lane 770 (hardware completion): per-call target sets over the accepted
  indirect forms (`IndirectControlHardwareForms`: `FF /2 CALL r/m64`,
  register-direct and checked base+disp32 memory). A provenance row binds
  one call site to one allowed target with its origin: a function-pointer
  value resolves to a decoded instruction start, an entry-fn value to a
  listed entry (the `entry fn` discipline of checker `N575`-`N577`: the
  type stands only at contract position, no Gabbro caller takes one, one
  whole hand-over outside every loop). Execution reuses the accepted
  constructors only; nothing is re-decoded or re-executed here. See CUTS.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.IndirectControlHardwareForms

namespace Gabbro.Grammatik.X86

/-- Manual provenance for every form claimed here (same snapshot as lane
    680, no new hardware claim): Intel SDM 325462-093US Vol.2A Ch.3
    `CALL-Call Procedure` (opcode table `FF /2 CALL r/m64`, near-call
    absolute operation, `Vol.2A 3-121`); Vol.1 `6.4.1 Near CALL and RET
    Operation` (push next-RIP, branch). Local snapshot
    `.tmp/HARDWARE-REFERENCES` (`REFERENCES.json`, verified 2026-10-02).
    AMD retrieval failed; no AMD claim. -/
def rufProvHandbuch : String :=
  "Intel SDM 325462-093US Vol.2A Ch.3 CALL (FF /2 r/m64, p.3-121); " ++
  "Vol.1 s.6.4.1 near CALL/RET. Local snapshot .tmp/HARDWARE-REFERENCES."

/-- Origin of one allowed indirect-call target: a function-pointer value
    (resolves to a decoded instruction start) or an entry-fn value (resolves
    to a listed entry handed once by the driver). -/
inductive RufHerkunft where
  | fnZeiger : RufHerkunft
  | eintrittFn : RufHerkunft
  deriving DecidableEq, Repr

/-- One provenance row: call-site address, allowed target, its origin. -/
structure RufZeile where
  aufruf : Adresse
  ziel : Adresse
  herkunft : RufHerkunft
  deriving DecidableEq, Repr

/-! ## 1. Per-call admission.

    A call site admits exactly the targets its provenance row names, and
    only with the matching origin check: function-pointer targets must be
    decoded instruction starts, entry-fn targets must be listed entries.
    This `Bool` is compiler/validator provenance, NOT a hardware fault
    (an unadmitted target still executes at step level; see the accepted
    separation `zielOhneHerkunft_fuehrt_aus`). -/

/-- Per-call admission: the exact row is listed, and the target has the
    origin its provenance claims. -/
def rufProvOk (tabelle : List RufZeile) (starts eintraege : List Adresse)
    (aufruf ziel : Adresse) (h : RufHerkunft) : Bool :=
  decide (⟨aufruf, ziel, h⟩ ∈ tabelle) &&
    match h with
    | .fnZeiger => decide (ziel ∈ starts)
    | .eintrittFn => decide (ziel ∈ eintraege)

/-- Admission carries the exact provenance row. -/
theorem rufProvOk_zeile (tabelle : List RufZeile)
    (starts eintraege : List Adresse) (aufruf ziel : Adresse)
    (h : RufHerkunft)
    (hadm : rufProvOk tabelle starts eintraege aufruf ziel h = true) :
    ⟨aufruf, ziel, h⟩ ∈ tabelle := by
  unfold rufProvOk at hadm
  simp only [Bool.and_eq_true] at hadm
  obtain ⟨hzeile, _⟩ := hadm
  exact of_decide_eq_true hzeile

/-- A function-pointer admission resolves to a decoded start. -/
theorem rufProvOk_fnZeiger (tabelle : List RufZeile)
    (starts eintraege : List Adresse) (aufruf ziel : Adresse)
    (hadm : rufProvOk tabelle starts eintraege aufruf ziel
      .fnZeiger = true) :
    ziel ∈ starts := by
  unfold rufProvOk at hadm
  simp only [Bool.and_eq_true] at hadm
  obtain ⟨_, hstart⟩ := hadm
  exact of_decide_eq_true hstart

/-- An entry-fn admission resolves to a listed entry. -/
theorem rufProvOk_eintrittFn (tabelle : List RufZeile)
    (starts eintraege : List Adresse) (aufruf ziel : Adresse)
    (hadm : rufProvOk tabelle starts eintraege aufruf ziel
      .eintrittFn = true) :
    ziel ∈ eintraege := by
  unfold rufProvOk at hadm
  simp only [Bool.and_eq_true] at hadm
  obtain ⟨_, heintritt⟩ := hadm
  exact of_decide_eq_true heintritt

/-! ## 2. Function-pointer connection.

    A register-indirect call carries a function-pointer value: the
    executed control transfer lands on the pre-state register word, that
    word is a decoded start by provenance, and the pushed return word
    reads back from the successor state. Every premise is used: `hok`
    and `hwr` select the accepted success constructor, `hstep` fixes the
    successor, `hrd` feeds the read-back, `hprov` the start membership. -/

/-- CONNECTION (function pointer): the executed register-indirect call
    lands on the provenanced decoded start with the return word stored. -/
theorem IndirectCallProv_verbindung (tabelle : List RufZeile)
    (starts eintraege : List Adresse)
    (s s' : Zustand) (tgt : Register) (len : Nat) (m : Speicher)
    (hok : laengeOk len = true)
    (hwr : write64 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = some m)
    (hrd : lesbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstep : callRegSchritt len s tgt = some s')
    (hprov : rufProvOk tabelle starts eintraege s.rip (s.register tgt)
      .fnZeiger = true) :
    s'.rip = s.register tgt ∧
      s'.rip ∈ starts ∧
      read64 s'.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) =
        some (ripNach s.rip len) := by
  have hcall := callRegSchritt_erfolg len s tgt m hok hwr
  rw [hcall] at hstep
  cases hstep
  refine ⟨rfl, ?_, ?_⟩
  · show s.register tgt ∈ starts
    exact rufProvOk_fnZeiger tabelle starts eintraege s.rip
      (s.register tgt) hprov
  · show read64 m (s.register Register.rsp - BitVec.ofNat 64 8) =
      some (ripNach s.rip len)
    exact read64_nach_write64 _ _ _ _ hwr hrd

/-- FRAME: the register-indirect call keeps every register except the
    stack pointer and preserves the flags (observable-register
    discipline for the provenanced call). -/
theorem rufProv_rahmen (s s' : Zustand) (tgt : Register) (len : Nat)
    (m : Speicher)
    (hok : laengeOk len = true)
    (hwr : write64 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = some m)
    (hstep : callRegSchritt len s tgt = some s')
    (q : Register) (hq : q ≠ Register.rsp) :
    s'.register q = s.register q ∧ s'.flags = s.flags := by
  have hcall := callRegSchritt_erfolg len s tgt m hok hwr
  rw [hcall] at hstep
  cases hstep
  refine ⟨?_, rfl⟩
  show (regSet s.register Register.rsp
    (s.register Register.rsp - BitVec.ofNat 64 8)) q = s.register q
  simp [regSet, hq]

/-! ## 3. Entry-fn connection.

    A memory-indirect call carries an entry-fn value: the target word is
    read first from the pre-state effective address (no speculation of a
    target fault away, inherited from `callMemSchritt_lesefehler`), the
    executed transfer lands on the read word, that word is a listed entry
    by provenance, and the pushed return word reads back. Every premise
    is used: `hok`, `hrd` and `hwr` select the accepted success
    constructor, `hstep` fixes the successor, `hrdStapel` feeds the
    read-back, `hprov` the entry membership. -/

/-- CONNECTION (entry-fn value): the executed memory-indirect call lands
    on the provenanced listed entry with the return word stored. -/
theorem IndirectCallProv_verbindung_eintritt (tabelle : List RufZeile)
    (starts eintraege : List Adresse)
    (s s' : Zustand) (base : Register) (disp : BitVec 32) (len : Nat)
    (ziel : Wort) (m : Speicher)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = some ziel)
    (hwr : write64 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip len) = some m)
    (hrdStapel : lesbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstep : callMemSchritt len s base disp = some s')
    (hprov : rufProvOk tabelle starts eintraege s.rip ziel
      .eintrittFn = true) :
    s'.rip = ziel ∧
      s'.rip ∈ eintraege ∧
      read64 s'.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) =
        some (ripNach s.rip len) := by
  have hcall := callMemSchritt_erfolg len s base disp ziel m hok hrd hwr
  rw [hcall] at hstep
  cases hstep
  refine ⟨rfl, ?_, ?_⟩
  · show ziel ∈ eintraege
    exact rufProvOk_eintrittFn tabelle starts eintraege s.rip ziel hprov
  · show read64 m (s.register Register.rsp - BitVec.ofNat 64 8) =
      some (ripNach s.rip len)
    exact read64_nach_write64 _ _ _ _ hwr hrdStapel

/-! ## 4. Pinned bytes and provenance refusals.

    Closed machine-byte computations (`decide`): the register-indirect
    call through `rax` is `FF D0`, the memory-indirect call through
    `rbx` with disp32 16 is `REX.W FF 93` plus the displacement; the
    `/0` neighbour (`FF C0`) has no indirect arm. Provenance refusals are
    closed `Bool` computations over the witness tables below: an
    off-table target, an unknown call site and a provenance mismatch all
    refuse loudly. -/

/-- Witness provenance: the call site 4096 may target 4200 as a
    function-pointer value. -/
def provTabelle : List RufZeile :=
  [⟨BitVec.ofNat 64 4096, BitVec.ofNat 64 4200, .fnZeiger⟩]

/-- Witness decoded starts: the call site and its target. -/
def provStarts : List Adresse :=
  [BitVec.ofNat 64 4096, BitVec.ofNat 64 4200]

/-- Witness listed entries: empty (no entry-fn value here). -/
def provEintraege : List Adresse := []

/-- Witness entry-fn provenance: the call site 4096 may target 4200 as
    an entry-fn value handed once by the driver. -/
def provTabelleEintritt : List RufZeile :=
  [⟨BitVec.ofNat 64 4096, BitVec.ofNat 64 4200, .eintrittFn⟩]

/-- Witness entry list for the entry-fn value. -/
def provEintraegeEintritt : List Adresse := [BitVec.ofNat 64 4200]

/-- PIN: register-indirect call through `rax` is `FF D0`. -/
theorem pin_prov_callReg_rax :
    encodeIndReg true .rax = [natByte 255, natByte 208] := by
  decide

/-- PIN: it decodes to the `rax` call form with length 2. -/
theorem pin_prov_callReg_rax_dekode :
    decodeIndirekt [natByte 255, natByte 208] =
      some (((.callReg .rax 2)), []) := by
  decide

/-- PIN: memory-indirect call through `rbx` with disp32 16 is
    `REX.W FF 93` plus the displacement. -/
theorem pin_prov_callMem_rbx :
    encodeIndMem true .rbx (BitVec.ofNat 32 16) =
      [natByte 72, natByte 255, natByte 147, natByte 16,
        natByte 0, natByte 0, natByte 0] := by
  decide

/-- PIN: it decodes to the `rbx`-based call form with length 7. -/
theorem pin_prov_callMem_rbx_dekode :
    decodeIndirekt [natByte 72, natByte 255, natByte 147, natByte 16,
        natByte 0, natByte 0, natByte 0] =
      some (((.callMem .rbx (BitVec.ofNat 32 16) 7)), []) := by
  decide

/-- REFUSAL: the `/0` neighbour (`FF C0`) has no indirect arm. -/
theorem prov_nachbar_verweigert :
    decodeIndirekt [natByte 255, natByte 192] = none := by
  decide

/-- REFUSAL: a target off the call site's row is not admitted. -/
theorem prov_fremd_verweigert :
    rufProvOk provTabelle provStarts provEintraege
      (BitVec.ofNat 64 4096) (BitVec.ofNat 64 4201) .fnZeiger = false := by
  decide

/-- REFUSAL: an unknown call site admits nothing. -/
theorem prov_unbekannt_verweigert :
    rufProvOk provTabelle provStarts provEintraege
      (BitVec.ofNat 64 5000) (BitVec.ofNat 64 4200) .fnZeiger = false := by
  decide

/-- REFUSAL: an entry-fn row does not admit a function-pointer call. -/
theorem prov_herkunft_verweigert :
    rufProvOk provTabelleEintritt provStarts provEintraegeEintritt
      (BitVec.ofNat 64 4096) (BitVec.ofNat 64 4200) .fnZeiger = false := by
  decide

/-- The entry-fn row admits the entry-fn call at the listed entry. -/
theorem prov_eintritt_akzeptiert :
    rufProvOk provTabelleEintritt provStarts provEintraegeEintritt
      (BitVec.ofNat 64 4096) (BitVec.ofNat 64 4200) .eintrittFn = true := by
  decide

/-- The function-pointer row admits the call at the decoded start. -/
theorem prov_fnZeiger_akzeptiert :
    rufProvOk provTabelle provStarts provEintraege
      (BitVec.ofNat 64 4096) (BitVec.ofNat 64 4200) .fnZeiger = true := by
  decide

/-! ## 5. Joint witnesses: reached memory-changing runs.

    Both connections hold jointly on the accepted fetched witnesses:
    the register-indirect call `CALL rbx` (`indS0`/`indS1`, return word
    4098 at 8184, control at 4200) and the RSP-based memory-indirect
    call (`memS0`/`memS1`, return word 4104 at 8192, control at the read
    word 4200). The stack slot observably changes in both runs (zero to
    return word); the memory difference is projected from the accepted
    chain witnesses. Non-degenerate: a reached call step that changes
    memory, plus a planted provenance refusal beside it. -/

/-- JOINT WITNESS for `IndirectCallProv_verbindung`: every premise
    holds jointly on the fetched `CALL rbx` state, the conclusion holds
    at the provenanced start, and the stack slot observably changed. -/
theorem IndirectCallProv_verbindung_zeuge :
    (rufProvOk provTabelle provStarts provEintraege indS0.rip
      (indS0.register Register.rbx) .fnZeiger = true) ∧
    (callRegSchritt 2 indS0 Register.rbx = some indS1) ∧
    (indS1.rip = BitVec.ofNat 64 4200 ∧
      indS1.rip ∈ provStarts ∧
      read64 indS1.speicher (BitVec.ofNat 64 8184) =
        some (BitVec.ofNat 64 4098)) ∧
    indS1.speicher.bytes (BitVec.ofNat 64 8184) ≠
      indS0.speicher.bytes (BitVec.ofNat 64 8184) := by
  have hok : laengeOk 2 = true := by decide
  have hschr : schreibbar8 indS0.speicher
      (indS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hwr : write64 indS0.speicher
      (indS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach indS0.rip 2) = some indM1 := by
    unfold write64 indM1
    rw [if_pos hschr]
    rfl
  have hrd : lesbar8 indS0.speicher
      (indS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hstep : callRegSchritt 2 indS0 Register.rbx = some indS1 :=
    callRegSchritt_erfolg 2 indS0 Register.rbx indM1 hok hwr
  have hprov : rufProvOk provTabelle provStarts provEintraege indS0.rip
      (indS0.register Register.rbx) .fnZeiger = true := by
    decide
  have hverb := IndirectCallProv_verbindung provTabelle provStarts
    provEintraege indS0 indS1 Register.rbx 2 indM1 hok hwr hrd hstep
    hprov
  obtain ⟨hrip, hstart, hrueck⟩ := hverb
  have epos : indS0.register Register.rsp - BitVec.ofNat 64 8 =
      BitVec.ofNat 64 8184 := by decide
  have eret : ripNach indS0.rip 2 = BitVec.ofNat 64 4098 := by decide
  have hziel : indS0.register Register.rbx = BitVec.ofNat 64 4200 := by
    decide
  rw [epos, eret] at hrueck
  rw [hrip, hziel]
  refine ⟨hprov, hstep, ⟨rfl, ?_, hrueck⟩, ?_⟩
  · simpa [hrip, hziel] using hstart
  · exact indKette_zeuge.2.2.2.2.2.2.2.1

/-- JOINT WITNESS for `IndirectCallProv_verbindung_eintritt`: every
    premise holds jointly on the fetched RSP-based memory call, the
    conclusion holds at the listed entry, and the stack slot observably
    changed. -/
theorem IndirectCallProv_verbindung_eintritt_zeuge :
    (rufProvOk provTabelleEintritt provStarts provEintraegeEintritt
      memS0.rip (BitVec.ofNat 64 4200) .eintrittFn = true) ∧
    (callMemSchritt 8 memS0 Register.rsp (BitVec.ofNat 32 0) =
      some memS1) ∧
    (memS1.rip = BitVec.ofNat 64 4200 ∧
      memS1.rip ∈ provEintraegeEintritt ∧
      read64 memS1.speicher (BitVec.ofNat 64 8192) =
        some (BitVec.ofNat 64 4104)) ∧
    memS1.speicher.bytes (BitVec.ofNat 64 8192) ≠
      memS0.speicher.bytes (BitVec.ofNat 64 8192) := by
  have hok : laengeOk 8 = true := by decide
  have hrd : read64 memS0.speicher
      (effAddr memS0 Register.rsp (BitVec.ofNat 32 0)) =
      some (BitVec.ofNat 64 4200) :=
    memS0_liest
  have hschr : schreibbar8 memS0.speicher
      (memS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hwr : write64 memS0.speicher
      (memS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach memS0.rip 8) = some memM1 := by
    unfold write64 memM1
    rw [if_pos hschr]
    rfl
  have hrdStapel : lesbar8 memS0.speicher
      (memS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    decide
  have hstep : callMemSchritt 8 memS0 Register.rsp
      (BitVec.ofNat 32 0) = some memS1 :=
    callMemSchritt_erfolg 8 memS0 Register.rsp (BitVec.ofNat 32 0)
      (BitVec.ofNat 64 4200) memM1 hok hrd hwr
  have hprov : rufProvOk provTabelleEintritt provStarts
      provEintraegeEintritt memS0.rip (BitVec.ofNat 64 4200)
      .eintrittFn = true := by
    decide
  have hverb := IndirectCallProv_verbindung_eintritt provTabelleEintritt
    provStarts provEintraegeEintritt memS0 memS1 Register.rsp
    (BitVec.ofNat 32 0) 8 (BitVec.ofNat 64 4200) memM1 hok hrd hwr
    hrdStapel hstep hprov
  obtain ⟨hrip, heintritt, hrueck⟩ := hverb
  have epos : memS0.register Register.rsp - BitVec.ofNat 64 8 =
      BitVec.ofNat 64 8192 := by decide
  have eret : ripNach memS0.rip 8 = BitVec.ofNat 64 4104 := by decide
  rw [epos, eret] at hrueck
  rw [hrip]
  exact ⟨hprov, hstep, ⟨rfl, heintritt, hrueck⟩,
    memCall_zeuge.2.2.2.2⟩

/- CUTS:
   Proved here: per-call indirect-CALL provenance (`rufProvOk`) with the
   row guarantee and the two origin guarantees (function-pointer target
   in decoded starts, entry-fn target in listed entries); the two
   execution connections (`IndirectCallProv_verbindung` for
   register-indirect function-pointer values,
   `IndirectCallProv_verbindung_eintritt` for memory-indirect entry-fn
   values) tying the accepted step constructors to the provenance table
   with return-word read-back; the observable-register/flag frame of the
   provenanced call; closed byte pins (`FF D0` register call,
   `REX.W FF 93`+disp32 memory call) with decode shapes; the `/0`
   neighbour refusal; provenance refusals (off-table target, unknown
   site, origin mismatch) with one acceptance per origin; joint
   witnesses with reached memory-changing runs reusing the accepted
   fetched states.
   NOT proved here, and not claimed:
   - No new decoding or execution: every byte row and every step reuses
     the accepted `decodeIndirekt`/`callRegSchritt`/`callMemSchritt`
     constructors; no `Befehl` constructor is added and `Typen.lean`
     is untouched.
   - No hardware correspondence beyond the stated manual headings: the
     provenance table is validator data, and an unadmitted target still
     executes at step level (accepted separation
     `zielOhneHerkunft_fuehrt_aus`); no silicon behaviour is proved.
   - No source/checker bridge: the `N575`-`N577` discipline is the named
     origin of the two provenances, but no theorem here speaks about
     Gabbro source, contracts, the checker or the emitter.
   - No TSO/GX, concurrency, gate/OS-contract, cost, time, fairness or
     termination claim; absence of a transition is never a termination
     statement. The frame theorem covers registers and flags only, not
     memory footprints beyond the read-back.
   - No whole-image coverage and no loader/ABI/entry/budget connection:
     `starts`/`eintraege` are checked inputs.
-/

#print axioms rufProvOk_zeile
#print axioms rufProvOk_fnZeiger
#print axioms rufProvOk_eintrittFn
#print axioms IndirectCallProv_verbindung
#print axioms rufProv_rahmen
#print axioms IndirectCallProv_verbindung_eintritt
#print axioms pin_prov_callReg_rax
#print axioms pin_prov_callReg_rax_dekode
#print axioms pin_prov_callMem_rbx
#print axioms pin_prov_callMem_rbx_dekode
#print axioms prov_nachbar_verweigert
#print axioms prov_fremd_verweigert
#print axioms prov_unbekannt_verweigert
#print axioms prov_herkunft_verweigert
#print axioms prov_eintritt_akzeptiert
#print axioms prov_fnZeiger_akzeptiert
#print axioms IndirectCallProv_verbindung_zeuge
#print axioms IndirectCallProv_verbindung_eintritt_zeuge

end Gabbro.Grammatik.X86
