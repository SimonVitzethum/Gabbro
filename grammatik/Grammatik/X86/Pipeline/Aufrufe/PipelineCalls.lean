/-
  File:      Grammatik/X86/PipelineCalls.lean
  Subject:   Pipeline calls over the accepted frame/ABI vocabulary: stack-passed
             integer parameters past the six registers, callee-saved discipline,
             no red zone, return value in `rax`, 16-byte alignment at the call,
             bounded recursion. Reuses `Stapel` (`Rahmen`, `Belegung`,
             `argReg`, `argStapelIdx`, `sichereListe`/`ladeListe`,
             `sichereErgebnis`/`ladeErgebnis`), `CallAlign16` (`rufAlignOk`,
             `nachRufVersatz`, `rsp8_versatz8`, `callGeprueft`) and
             `StackExecution` (`StapelGeholt`, `byteschritt_geholt_call`).
             No second machine, no second loader, no source claim.
-/
import Grammatik.X86.Kern.Stapel
import Grammatik.X86.Befehle.Kontrolle.CallAlign16
import Grammatik.X86.Laden.StackExecution

namespace Gabbro.Grammatik.X86.PipelineCalls

open Gabbro.Grammatik.X86

/-- Return-value register: integer results arrive in `rax`. -/
def rufErgebnisReg : Register := .rax

/-- Callee-saved registers (System V AMD64): a callee preserves these. -/
def calleeGerettet : List Register :=
  [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Red-zone refusal: the pipeline never uses the 128-byte red zone below
    `rsp`; any use (`benutztRot = true`) is refused loudly. -/
def rufRotVerbot (benutztRot : Bool) : Bool := !benutztRot

/-- Recursion budget: a call at depth `tiefe` is admitted only within
    the stated `budget`. Unbounded recursion is refused, never guessed. -/
def rekursionOk (tiefe budget : Nat) : Bool := decide (tiefe ≤ budget)

/-- THE CALL VALIDATOR: the layout fits the frame inside 64 bits, carries
    exactly the stack-passed words (`nArgs - 6`), keeps all six
    callee-saved words, and uses no red zone. -/
def rufOk (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool) : Bool :=
  Belegung.passt b r && decide (r.spitzeNat ≤ 2 ^ 64) &&
  decide (b.stapelArgs = nArgs - 6) && decide (6 ≤ b.gerettet) && !benutztRot

/-- Unpacking the call validator. -/
theorem rufOk_teile (b : Belegung) (r : Rahmen) (nArgs : Nat) (benutztRot : Bool)
    (h : rufOk b r nArgs benutztRot = true) :
    Belegung.passt b r = true ∧ r.spitzeNat ≤ 2 ^ 64 ∧
    b.stapelArgs = nArgs - 6 ∧ 6 ≤ b.gerettet ∧ benutztRot = false := by
  unfold rufOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hp, hle⟩, hst⟩, hg⟩, hr⟩ := h
  refine ⟨hp, hle, hst, hg, ?_⟩
  cases hb : benutztRot with
  | false => rfl
  | true => simp [hb] at hr

/-- The first six integer parameters travel in registers (System V order);
    the seventh and further travel on the stack, never in a register. -/
theorem rufParam_orte :
    argReg 0 = some .rdi ∧ argReg 1 = some .rsi ∧ argReg 2 = some .rdx ∧
    argReg 3 = some .rcx ∧ argReg 4 = some .r8 ∧ argReg 5 = some .r9 ∧
    ∀ i, 6 ≤ i → argReg i = none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro i hi
  exact argReg_ab_sechs i hi

/-- The return register is `rax`, and six callee-saved registers are named. -/
theorem rufErgebnis_ist_rax : rufErgebnisReg = .rax := rfl

theorem calleeGerettet_sechs : calleeGerettet.length = 6 := rfl

/-- RED-ZONE REFUSAL: any use of the red zone is refused loudly. -/
theorem rufRotVerbot_verweigert : rufRotVerbot true = false := rfl

theorem rufRotVerbot_frei : rufRotVerbot false = true := rfl

/-- RECURSION REFUSAL: a call past the stated budget is refused loudly. -/
theorem rekursion_verweigert (tiefe budget : Nat) (h : budget < tiefe) :
    rekursionOk tiefe budget = false := by
  unfold rekursionOk
  simp only [decide_eq_false_iff_not]
  omega

theorem rekursion_erlaubt (tiefe budget : Nat) (h : tiefe ≤ budget) :
    rekursionOk tiefe budget = true := by
  unfold rekursionOk
  simp only [decide_eq_true_eq]
  exact h

/-- A stack-passed argument of an admitted call lies in the frame. -/
theorem rufOk_argSchranke (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (i : Nat) (hi : i < nArgs) (h6 : 6 ≤ i)
    (hval : rufOk b r nArgs benutztRot = true) :
    argStapelIdx b i < r.schlitzZahl := by
  obtain ⟨hp, -, hst, -, -⟩ := rufOk_teile b r nArgs benutztRot hval
  have hpasst' : b.braucht * 8 ≤ r.tiefe := by
    unfold Belegung.passt at hp
    exact of_decide_eq_true hp
  exact argStapel_schranke b r i nArgs hi h6 hst hpasst'

/-- A callee-save slot shares no byte with a stack-argument slot. -/
theorem rufOk_getrennt (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (i j : Nat) (hi : i < 6) (hj : 6 + j < nArgs)
    (hval : rufOk b r nArgs benutztRot = true) :
    Disjunkt (r.schlitzAddr (b.gerettetIdx i))
      (r.schlitzAddr (b.stapelArgIdx j)) := by
  obtain ⟨hp, hle, hst, hg, -⟩ := rufOk_teile b r nArgs benutztRot hval
  have hpasst' : b.braucht * 8 ≤ r.tiefe := by
    unfold Belegung.passt at hp
    exact of_decide_eq_true hp
  have hi' : i < b.gerettet := by omega
  have hj' : j < b.stapelArgs := by omega
  exact gerettet_stapel_getrennt b r i j hi' hj' hpasst' hle

/-- A caller result word survives the stack-argument setup: every saved
    argument slot is disjoint from the result address. -/
theorem ladeErgebnis_nach_sichererListe (m1 m2 : Speicher) (r : Rahmen)
    (base : Nat) (vs : List Wort) (e : Adresse)
    (hwr : sichereListe m1 r base vs = some m2)
    (hdis : ∀ j, j < vs.length → Disjunkt (r.schlitzAddr (base + j)) e) :
    ladeErgebnis m2 e = ladeErgebnis m1 e := by
  induction vs generalizing base m1 with
  | nil =>
    cases hwr
    rfl
  | cons w ws ih =>
    unfold sichereListe at hwr
    cases hmw : sichereWort m1 r base w with
    | none =>
      simp only [hmw] at hwr
      cases hwr
    | some m' =>
      simp only [hmw] at hwr
      have hb : base < r.schlitzZahl := by
        by_cases h : base < r.schlitzZahl
        · exact h
        · exfalso
          have hnone := sichereWort_ausserhalb m1 r base w (by omega)
          rw [hnone] at hmw
          cases hmw
      have hmw64 : write64 m1 (r.schlitzAddr base) w = some m' := by
        unfold sichereWort at hmw
        rw [if_pos hb] at hmw
        exact hmw
      have hd0 := hdis 0 (by simp)
      simp only [Nat.add_zero] at hd0
      have hstep : ladeErgebnis m' e = ladeErgebnis m1 e := by
        unfold ladeErgebnis
        exact read64_rahmen m1 m' (r.schlitzAddr base) e w hmw64 hd0
      have hdis' : ∀ j, j < ws.length →
          Disjunkt (r.schlitzAddr ((base + 1) + j)) e := by
        intro j hj
        have hj' : j + 1 < (w :: ws).length := by
          simp only [List.length_cons] at hj ⊢
          omega
        have h := hdis (j + 1) hj'
        have heq : base + (j + 1) = (base + 1) + j := by omega
        rwa [heq] at h
      have ihtail := ih m' (base + 1) hwr hdis'
      rw [ihtail, hstep]

/-- CALL-FRAME CORRECTNESS: under the admitted validator, the caller result
    word is transported first and the stack arguments after it: every stack
    argument loads back, the result word loads back past the argument setup,
    every callee-save slot is untouched by the setup, and no red zone is
    used. Every premise is consumed: `hval` for fit, bound, arity, save
    room and red-zone freedom; `hvs` for the arity of every slot; `hret`
    and `hrde` for the result round-trip; `hwr` and `hrd` for the argument
    round-trip; `hdis` for result survival. -/
theorem pipeline_ruf_rahmen (b : Belegung) (r : Rahmen) (nArgs : Nat)
    (benutztRot : Bool) (m0 m1 m2 : Speicher) (vs : List Wort)
    (e : Adresse) (v : Wort)
    (hval : rufOk b r nArgs benutztRot = true)
    (hvs : vs.length = nArgs - 6)
    (hret : sichereErgebnis m0 e v = some m1)
    (hrde : lesbar8 m0 e = true)
    (hwr : sichereListe m1 r (b.spill + b.gerettet) vs = some m2)
    (hrd : ∀ j, j < vs.length →
      lesbar8 m1 (r.schlitzAddr (b.spill + b.gerettet + j)) = true)
    (hdis : ∀ j, j < vs.length →
      Disjunkt (r.schlitzAddr (b.spill + b.gerettet + j)) e) :
    ladeListe m2 r (b.spill + b.gerettet) vs.length = some vs ∧
    ladeErgebnis m2 e = some v ∧
    (∀ i, i < 6 → ladeWort m2 r (b.gerettetIdx i) =
      ladeWort m1 r (b.gerettetIdx i)) ∧
    benutztRot = false := by
  obtain ⟨hp, hle, hst, hg, hrot⟩ := rufOk_teile b r nArgs benutztRot hval
  have hpasst' : b.braucht * 8 ≤ r.tiefe := by
    unfold Belegung.passt at hp
    exact of_decide_eq_true hp
  have hfit : ∀ j, j < vs.length →
      b.spill + b.gerettet + j < r.schlitzZahl := by
    intro j hj
    have harg : 6 + j < nArgs := by omega
    have hsch := argStapel_schranke b r (6 + j) nArgs harg (by omega) hst hpasst'
    have heq : argStapelIdx b (6 + j) = b.spill + b.gerettet + j := by
      unfold argStapelIdx
      omega
    rwa [heq] at hsch
  have hargs := sichereListe_ladeListe_rundreise m1 m2 r
    (b.spill + b.gerettet) vs hle hfit hwr hrd
  have hergeb1 := sichere_lade_ergebnis_rundreise m0 m1 e v hret hrde
  have hergeb2 := ladeErgebnis_nach_sichererListe m1 m2 r
    (b.spill + b.gerettet) vs e hwr hdis
  have hsave : ∀ i, i < 6 → ladeWort m2 r (b.gerettetIdx i) =
      ladeWort m1 r (b.gerettetIdx i) := by
    intro i hi
    have hk : b.gerettetIdx i < r.schlitzZahl := by
      unfold Belegung.braucht at hpasst'
      unfold Belegung.gerettetIdx Rahmen.schlitzZahl
      omega
    have hsep : ∀ j, j < vs.length →
        b.gerettetIdx i ≠ b.spill + b.gerettet + j := by
      intro j _
      unfold Belegung.gerettetIdx
      omega
    unfold ladeWort
    by_cases hb : b.gerettetIdx i < r.schlitzZahl
    · rw [if_pos hb, if_pos hb]
      exact sichereListe_rahmen_fremd m1 m2 r (b.spill + b.gerettet) vs
        (b.gerettetIdx i) hle hk hfit hsep hwr
    · rw [if_neg hb, if_neg hb]
  refine ⟨hargs, ?_, hsave, hrot⟩
  rw [hergeb2]
  exact hergeb1

/-- CALL-GATE CORRECTNESS (byte level): from actual fetched call bytes at
    an aligned site, the byte machine takes the accepted call step, the
    post-call top drops exactly one word, and the post-call top carries
    offset 8. Every premise is consumed: `hwin` and `hexe` fetch the call,
    `hwr` stores the return word, `hali` transfers alignment to the
    post-call offset. -/
theorem pipeline_ruf_gate (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte) (m : Speicher)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length) = some m)
    (hali : rufAlignOk s = true) :
    byteschritt s = .weiter (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)) ∧
    nachRufVersatz ((schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)).register
      Register.rsp) = true := by
  have hstep := byteschritt_geholt_call s disp suffix m hwin hexe hwr
  have hrsp : (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)).register
      Register.rsp =
      s.register Register.rsp - BitVec.ofNat 64 8 := by
    unfold schrittCall
    show regSet s.register Register.rsp
      (s.register Register.rsp - BitVec.ofNat 64 8) Register.rsp = _
    exact regSet_gleich _ _ _
  have haliN : (s.register Register.rsp).toNat % 16 = 0 := by
    unfold rufAlignOk ausgerichtet16 at hali
    exact of_decide_eq_true hali
  have hvers : nachRufVersatz ((schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)).register
      Register.rsp) = true := by
    rw [hrsp]
    unfold nachRufVersatz
    rw [decide_eq_true_eq]
    exact rsp8_versatz8 _ haliN
  exact ⟨hstep, hvers⟩

/-- MISALIGNED CALL REFUSAL: at a misaligned site the checked call gate
    loudly refuses instead of stepping. -/
theorem pipeline_ruf_verweigert_fehlalign (d : Decodiert) (s : Zustand)
    (disp : BitVec 32) (hbef : d.befehl = .call32 disp)
    (hmis : rufAlignOk s = false) :
    callGeprueft d s = none :=
  callGeprueft_fehlalign d s disp hbef hmis

/-- RED-ZONE USE REFUSAL: no call that uses the red zone is admitted. -/
theorem pipeline_ruf_verweigert_rot (b : Belegung) (r : Rahmen)
    (nArgs : Nat) :
    rufOk b r nArgs true = false := by
  unfold rufOk
  simp

/-- OUT-OF-FRAME REFUSAL: a stack argument past the frame saves nothing. -/
theorem pipeline_ruf_verweigert_schranke (m : Speicher) (r : Rahmen)
    (idx : Nat) (v : Wort) (h : r.schlitzZahl ≤ idx) :
    sichereWort m r idx v = none :=
  sichereWort_ausserhalb m r idx v h

/-! ## Joint witness: a seven-argument call over concrete values. -/

/-- Witness frame: base 0, eight word slots. -/
def rufWitRahmen : Rahmen := { basis := 0, tiefe := 64 }

/-- Witness layout: one spill slot, six callee-save slots, one stack arg. -/
def rufWitBelegung : Belegung := { spill := 1, gerettet := 6, stapelArgs := 1 }

/-- Witness memory after the result write: word 9 at slot 0. -/
def rufWitM1 : Speicher :=
  { speicherZeuge with
    bytes := writeBytes speicherZeuge (rufWitRahmen.schlitzAddr 0) 9 }

/-- Witness memory after the argument setup: word 42 at slot 7. -/
def rufWitM2 : Speicher :=
  { rufWitM1 with
    bytes := writeBytes rufWitM1 (rufWitRahmen.schlitzAddr 7) 42 }

/-- The witness call is admitted: seven arguments, no red zone. -/
theorem rufWit_ok : rufOk rufWitBelegung rufWitRahmen 7 false = true := by
  decide

/-- Witness slot bounds: slots 0 and 7 lie inside the eight-slot frame. -/
theorem rufWit_schranke0 : 0 < rufWitRahmen.schlitzZahl := by
  decide

theorem rufWit_schranke7 : 7 < rufWitRahmen.schlitzZahl := by
  decide

/-- Witness slot readability before the writes. -/
theorem rufWit_lesbar0 :
    lesbar8 speicherZeuge (rufWitRahmen.schlitzAddr 0) = true := by
  decide

theorem rufWit_lesbar7 :
    lesbar8 rufWitM1 (rufWitRahmen.schlitzAddr 7) = true := by
  decide

/-- REACHED RESULT WRITE: word 9 lands at slot 0. -/
theorem rufWit_speichert_ergebnis :
    sichereErgebnis speicherZeuge (rufWitRahmen.schlitzAddr 0) 9 =
      some rufWitM1 := by
  unfold sichereErgebnis rufWitM1
  unfold write64
  rw [if_pos (by decide : schreibbar8 speicherZeuge
    (rufWitRahmen.schlitzAddr 0) = true)]

/-- REACHED ARGUMENT SETUP: word 42 lands at slot 7. -/
theorem rufWit_speichert_arg :
    sichereListe rufWitM1 rufWitRahmen
      (rufWitBelegung.spill + rufWitBelegung.gerettet) [42] =
      some rufWitM2 := by
  have hsave : sichereWort rufWitM1 rufWitRahmen 7 42 = some rufWitM2 := by
    unfold sichereWort rufWitM2
    rw [if_pos rufWit_schranke7]
    unfold write64
    rw [if_pos (by decide : schreibbar8 rufWitM1
      (rufWitRahmen.schlitzAddr 7) = true)]
  have hbase : rufWitBelegung.spill + rufWitBelegung.gerettet = 7 := rfl
  simp only [hbase, sichereListe, hsave]

/-- REACHED SINGLE SAVE: word 42 lands at slot 7 in one step. -/
theorem rufWit_speichert7 :
    sichereWort rufWitM1 rufWitRahmen 7 42 = some rufWitM2 := by
  unfold sichereWort rufWitM2
  rw [if_pos rufWit_schranke7]
  unfold write64
  rw [if_pos (by decide : schreibbar8 rufWitM1
    (rufWitRahmen.schlitzAddr 7) = true)]

/-- REACHED RELOAD: the saved argument word loads back. -/
theorem rufWit_rundreise :
    ladeWort rufWitM2 rufWitRahmen 7 = some 42 :=
  sichere_lade_rundreise rufWitM1 rufWitM2 rufWitRahmen 7 42
    rufWit_schranke7 rufWit_speichert7 rufWit_lesbar7

/-- MEMORY CHANGE: the result write observably changes the slot byte
    (zero becomes the low byte of 9). -/
theorem rufWit_wechselt :
    speicherZeuge.bytes (rufWitRahmen.schlitzAddr 0) ≠
      rufWitM1.bytes (rufWitRahmen.schlitzAddr 0) := by
  have hhit := writeBytesN_hit speicherZeuge (rufWitRahmen.schlitzAddr 0)
    9 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show BitVec.ofNat 8 0 ≠
    writeBytes speicherZeuge (rufWitRahmen.schlitzAddr 0) 9
      (rufWitRahmen.schlitzAddr 0)
  unfold writeBytes
  rw [hhit]
  decide

/-- The argument slot shares no byte with the result slot. -/
theorem rufWit_getrennt :
    Disjunkt (rufWitRahmen.schlitzAddr 7) (rufWitRahmen.schlitzAddr 0) :=
  schlitz_disjunkt rufWitRahmen 7 0 rufWit_schranke7 rufWit_schranke0
    (by decide) (by decide)

/-- Planted refusal: a misaligned call site is refused loudly. -/
theorem rufProbe_fehlalign :
    callGeprueft ⟨.call32 alignDisp, 5⟩ alignSmis = none :=
  callGeprueft_fehlalign _ _ _ rfl alignSmis_fehlalign

/-- Planted refusal: a call that uses the red zone is not admitted. -/
theorem rufProbe_rot :
    rufOk rufWitBelegung rufWitRahmen 7 true = false := by
  decide

/-- Planted refusal: recursion past the stated budget is refused. -/
theorem rufProbe_rekursion : rekursionOk 3 2 = false := by
  decide

/-- Planted refusal: a slot past the witness frame saves nothing. -/
theorem rufProbe_schranke :
    sichereWort speicherZeuge rufWitRahmen 8 42 = none :=
  sichereWort_ausserhalb _ _ _ _ (by decide)

/-- JOINT WITNESS for `pipeline_ruf_rahmen`: every premise holds jointly
    on a seven-argument call over concrete values -- the result write and
    the argument setup are reached saves, the result byte observably
    changes (zero becomes the low byte of 9), the argument word reads
    back -- beside an aligned call site, an admitted recursion depth and
    a misaligned refusal twin. -/
theorem pipeline_ruf_rahmen_zeuge :
    ∃ (b : Belegung) (r : Rahmen) (m0 m1 m2 : Speicher) (vs : List Wort)
      (e : Adresse) (v : Wort),
      rufOk b r 7 false = true ∧
      vs.length = 7 - 6 ∧
      sichereErgebnis m0 e v = some m1 ∧
      lesbar8 m0 e = true ∧
      sichereListe m1 r (b.spill + b.gerettet) vs = some m2 ∧
      (∀ j, j < vs.length →
        lesbar8 m1 (r.schlitzAddr (b.spill + b.gerettet + j)) = true) ∧
      (∀ j, j < vs.length →
        Disjunkt (r.schlitzAddr (b.spill + b.gerettet + j)) e) ∧
      m0.bytes e ≠ m1.bytes e ∧
      ladeWort m2 r 7 = some 42 ∧
      rufAlignOk alignS0 = true ∧
      rekursionOk 0 4 = true ∧
      callGeprueft ⟨.call32 alignDisp, 5⟩ alignSmis = none := by
  have hrd : ∀ j, j < [42].length →
      lesbar8 rufWitM1 (rufWitRahmen.schlitzAddr
        (rufWitBelegung.spill + rufWitBelegung.gerettet + j)) = true := by
    intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    show lesbar8 rufWitM1 (rufWitRahmen.schlitzAddr 7) = true
    exact rufWit_lesbar7
  have hdis : ∀ j, j < [42].length →
      Disjunkt (rufWitRahmen.schlitzAddr
        (rufWitBelegung.spill + rufWitBelegung.gerettet + j))
        (rufWitRahmen.schlitzAddr 0) := by
    intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    show Disjunkt (rufWitRahmen.schlitzAddr 7) (rufWitRahmen.schlitzAddr 0)
    exact rufWit_getrennt
  exact ⟨rufWitBelegung, rufWitRahmen, speicherZeuge, rufWitM1, rufWitM2,
    [42], rufWitRahmen.schlitzAddr 0, 9,
    rufWit_ok, rfl, rufWit_speichert_ergebnis, rufWit_lesbar0,
    rufWit_speichert_arg, hrd, hdis, rufWit_wechselt, rufWit_rundreise,
    alignS0_ausgerichtet, rekursion_erlaubt 0 4 (Nat.zero_le 4),
    rufProbe_fehlalign⟩

/- CUTS (exactly what is NOT proved here):
   Proved here (all over the REUSED canonical `Speicher`/`Zustand`
   vocabulary and the accepted `Stapel`, `CallAlign16` and
   `StackExecution` theorems -- no new machine, no new decoder row, no
   source claim):
   - call validator `rufOk` (layout fit inside 64 bits, exact stack-arg
     count, six callee-save words, no red zone) with its unpacking
     (`rufOk_teile`), frame bound (`rufOk_argSchranke`) and slot
     separation (`rufOk_getrennt`);
   - parameter places (`rufParam_orte`: six System V registers, the rest
     on the stack), return register (`rufErgebnis_ist_rax`), six named
     callee-saved registers (`calleeGerettet_sechs`);
   - red-zone refusal (`rufRotVerbot_verweigert`,
     `pipeline_ruf_verweigert_rot`) and recursion-budget refusal
     (`rekursion_verweigert`, `rekursion_erlaubt`);
   - frame correctness (`pipeline_ruf_rahmen`): admitted setup carries
     every stack argument, the caller result word, untouched
     callee-save slots and red-zone freedom, over one region induction
     (`ladeErgebnis_nach_sichererListe`) plus the accepted
     whole-region round-trip;
   - byte-gate correctness (`pipeline_ruf_gate`): fetched aligned call
     bytes step through the accepted byte step with a one-word drop
     and offset 8, from the accepted alignment arithmetic;
   - planted refusals on every path (misaligned gate, red-zone use,
     over-budget recursion, out-of-frame slot) and a joint
     memory-changing witness (`pipeline_ruf_rahmen_zeuge`).
   NOT proved here, and not claimed:
   - No source correspondence: nothing here maps a source `execBlock`,
     function contract or call log to the frame; the callee body is an
     abstracted result-word write, and callee-side preservation of the
     six registers is a stated caller-visible consequence of the setup,
     not a proved callee run. Full source-to-final-bytes validation
     stays OPEN.
   - No TSO/store-buffer/GX bridge: every fact is sequential over one
     canonical `Speicher`; the TSO spill-privacy leg stays with
     `ComposeSpillPrivacy_verbindung` (cited, not redone).
   - No callee-saved push/pop code is emitted or verified here; the
     push/pop restoration leg stays with `ComposeStackAbi_verbindung`
     and the fetched nested leg stays with
     `geholt_verschachtelt_wiederhergestellt` (both cited, not redone).
   - No silicon correspondence beyond the accepted producers; no
     float/pointer/aggregate parameters; no loader, entry, relocation,
     cost or time claim; recursion bound is a stated number, and who
     enforces it at run time stays OPEN.
-/

#print axioms rufErgebnisReg
#print axioms calleeGerettet
#print axioms rufRotVerbot
#print axioms rekursionOk
#print axioms rufOk
#print axioms rufOk_teile
#print axioms rufParam_orte
#print axioms rufErgebnis_ist_rax
#print axioms calleeGerettet_sechs
#print axioms rufRotVerbot_verweigert
#print axioms rufRotVerbot_frei
#print axioms rekursion_verweigert
#print axioms rekursion_erlaubt
#print axioms rufOk_argSchranke
#print axioms rufOk_getrennt
#print axioms ladeErgebnis_nach_sichererListe
#print axioms pipeline_ruf_rahmen
#print axioms pipeline_ruf_verweigert_fehlalign
#print axioms pipeline_ruf_verweigert_rot
#print axioms pipeline_ruf_verweigert_schranke
#print axioms pipeline_ruf_gate
#print axioms rufWitRahmen
#print axioms rufWitBelegung
#print axioms rufWitM1
#print axioms rufWitM2
#print axioms rufWit_ok
#print axioms rufWit_schranke0
#print axioms rufWit_schranke7
#print axioms rufWit_lesbar0
#print axioms rufWit_lesbar7
#print axioms rufWit_speichert_ergebnis
#print axioms rufWit_speichert7
#print axioms rufWit_speichert_arg
#print axioms rufWit_rundreise
#print axioms rufWit_wechselt
#print axioms rufWit_getrennt
#print axioms rufProbe_fehlalign
#print axioms rufProbe_rot
#print axioms rufProbe_rekursion
#print axioms rufProbe_schranke
#print axioms pipeline_ruf_rahmen_zeuge

end Gabbro.Grammatik.X86.PipelineCalls
