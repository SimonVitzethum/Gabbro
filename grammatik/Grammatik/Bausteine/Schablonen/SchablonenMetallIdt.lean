/-
  File:      Grammatik/SchablonenMetallIdt.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md): the GENERATED interrupt descriptor
             table of the bare-metal image (C-free lane, C3 slice 3, 2026-10-05).

  Row of `crates/gabbro-check/src/schablonen.rs`: `idt.metall` -- the IDT text the build writes
  beside the image (`treiber.rs::METALL_IDT`, `<unit>.metall.idt.c`; until 2026-10-05 a part of
  `laufzeit/metall/kern.c`): the table of 256 gate descriptors, `idt_setze` (one 64-bit
  interrupt gate: the handler address split into three fields, selector `0x18`, type byte
  `0x8E`), `metall_idt_bau` (the 32 exception stubs, the timer `0x40`, the wake vector `0x41`,
  the kernel service entry `0x80`, the spurious vector `0xFF`), `metall_idt_lade` (`lidt`), and
  the two installers a driver calls for the program's own entries, `metall_idt_setze` and
  `metall_idt_setze_fc`, each refusing (ending the machine) what it must not install.

  An ABSTRACT CORE like `arena.metall` (SchablonenMetall.lean). What is proved:

  * `kodiere_dekodiere`: the three address fields the template stores put back together are the
    handler's address, for every 64-bit address -- the CPU's reading of a gate (Intel SDM vol. 3
    6.14.1, the named hardware assumption every metal image carries) lands on the stub;
  * `art_ist_interrupt_gate`: the type byte `0x8E` is present, DPL 0, type 14 (a 64-bit
    INTERRUPT gate, which clears IF on entry -- what every stub of the runtime relies on);
  * `fehlercode_c_ist_die_liste`: the C test `hat_fehlercode` answers yes exactly on the
    vectors 8, 10..14, 17, 21, 29, 30 -- the SDM's list of exceptions that push an error code
    (table 6-1) -- for every vector of the table;
  * `installieren_bewahrt_laufzeit`, `installieren_passt`: after the build and ANY sequence of
    installer calls that return, the runtime's own vectors (`0x40`, `0x41`, `0xFF`) still hold
    the runtime's stubs, and every program entry sits on a vector of its own kind -- a plain
    stub never on an error-code vector, an error-code stub never elsewhere -- so no stub's
    `iretq` reads one word off; `installieren_ohne_wache_waere_falsch` shows the refusals are
    load-bearing.

  NOT proved: that the CPU decodes gates as the SDM says (the hardware assumption), that `lidt`
  makes the table the one every core dispatches through (the BSP and every AP execute it on
  bring-up, `kern.c`), and the stubs themselves (`start.S`, `eintritt_asm.h`: wall D of
  `messung/C3-WAENDE.md`).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL its
  premises jointly.
-/

namespace Gabbro.Grammatik

namespace MetallIdt

/-! ## 1. One gate descriptor -/

/-- The three address fields `idt_setze` stores: `off0 = (uint16_t)a`,
    `off1 = (uint16_t)(a >> 16)`, `off2 = (uint32_t)(a >> 32)`. -/
structure Felder where
  off0 : Nat
  off1 : Nat
  off2 : Nat

def kodiere (a : Nat) : Felder :=
  ⟨a % 65536, (a / 65536) % 65536, (a / 4294967296) % 4294967296⟩

/-- The CPU's reading of the handler address from a gate (SDM vol. 3 6.14.1). -/
def dekodiere (f : Felder) : Nat := f.off0 + f.off1 * 65536 + f.off2 * 4294967296

/-- **THE GATE POINTS AT THE STUB**, for every 64-bit address. -/
theorem kodiere_dekodiere (a : Nat) (h : a < 18446744073709551616) :
    dekodiere (kodiere a) = a := by
  unfold dekodiere kodiere
  simp only
  omega

/-- The type byte `0x8E`: present (bit 7), DPL 0 (bits 5-6), type 14 (bits 0-3): a 64-bit
    INTERRUPT gate, which clears IF on entry. -/
theorem art_ist_interrupt_gate :
    (0x8E / 128) % 2 = 1 ∧ (0x8E / 32) % 4 = 0 ∧ 0x8E % 16 = 14 := by decide

/-! ## 2. Which vectors push an error code -/

/-- The C test, as the template writes it:
    `v == 8u || (v >= 10u && v <= 14u) || v == 17u || v == 21u || v == 29u || v == 30u`. -/
def fehlercodeC (v : Nat) : Bool :=
  v == 8 || (v ≥ 10 && v ≤ 14) || v == 17 || v == 21 || v == 29 || v == 30

/-- The SDM's list of exceptions that push an error code (vol. 3 table 6-1): #DF, #TS, #NP, #SS,
    #GP, #PF, #AC, #CP, #VC, #SX. -/
def fehlercodeListe : List Nat := [8, 10, 11, 12, 13, 14, 17, 21, 29, 30]

/-- **THE C TEST IS THE LIST**, on every vector of the table. -/
theorem fehlercode_c_ist_die_liste : ∀ v, v < 256 → (fehlercodeC v = true ↔ v ∈ fehlercodeListe) := by
  intro v _
  simp only [fehlercodeC, fehlercodeListe, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq, List.mem_cons, List.mem_nil_iff, or_false]
  constructor <;> intro h <;> omega

/-! ## 3. The table, the build, the installers -/

/-- What a slot of the table holds: an exception stub of the runtime, one of the runtime's
    own entries, a program entry with the plain stub, or with the error-code twin. -/
inductive Eintrag where
  | leer
  | ausnahme (v : Nat)
  | takt
  | wecken
  | systemruf
  | unecht
  | programm (name : Nat)
  | programmFc (name : Nat)
  deriving DecidableEq

def Tafel := Nat → Eintrag

def setze (t : Tafel) (v : Nat) (e : Eintrag) : Tafel := fun w => if w = v then e else t w

/-- `metall_idt_bau`. -/
def bau : Tafel := fun v =>
  if v < 32 then .ausnahme v
  else if v = 0x40 then .takt
  else if v = 0x41 then .wecken
  else if v = 0x80 then .systemruf
  else if v = 0xFF then .unecht
  else .leer

/-- `metall_idt_setze`: refuses (the machine ends -- no table) a vector above `0xFE`, the timer
    and wake vectors, and every error-code vector. -/
def nimmt (v : Nat) : Bool := v ≤ 0xFE && v != 0x40 && v != 0x41 && !fehlercodeC v

/-- `metall_idt_setze_fc`: refuses every vector without an error code. -/
def nimmtFc (v : Nat) : Bool := fehlercodeC v

/-- One installer call of a driver: its kind (`fc`), the vector, the entry's name. -/
structure Ruf where
  fc : Bool
  vektor : Nat
  name : Nat

/-- The installer's effect, or `none` where it ends the machine. -/
def installiere (t : Tafel) (r : Ruf) : Option Tafel :=
  if r.fc then (if nimmtFc r.vektor then some (setze t r.vektor (.programmFc r.name)) else none)
  else (if nimmt r.vektor then some (setze t r.vektor (.programm r.name)) else none)

/-- A whole sequence of installer calls; `none` as soon as one ends the machine. -/
def installiereAlle : Tafel → List Ruf → Option Tafel
  | t, [] => some t
  | t, r :: rs => (installiere t r).bind (fun t' => installiereAlle t' rs)

/-- What every table the image can run with satisfies. -/
def Passt (t : Tafel) : Prop :=
  t 0x40 = .takt ∧ t 0x41 = .wecken ∧ t 0xFF = .unecht ∧
  (∀ v n, t v = .programm n → fehlercodeC v = false) ∧
  (∀ v n, t v = .programmFc n → fehlercodeC v = true)

theorem bau_passt : Passt bau := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro v n h
    unfold bau at h
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> cases h
  · intro v n h
    unfold bau at h
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> cases h

theorem installiere_passt {t t' : Tafel} {r : Ruf} (hp : Passt t) (h : installiere t r = some t') :
    Passt t' := by
  obtain ⟨h40, h41, hff, hpl, hfc⟩ := hp
  unfold installiere at h
  cases hr : r.fc <;> rw [hr] at h <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · -- the plain installer
    cases hn : nimmt r.vektor <;> rw [hn] at h <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, reduceCtorEq] at h
    subst h
    unfold nimmt at hn
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true'] at hn
    obtain ⟨⟨⟨hle, h1⟩, h2⟩, hf⟩ := hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (if (0x40 : Nat) = r.vektor then _ else _) = _
      rw [if_neg (Ne.symm h1)]; exact h40
    · show (if (0x41 : Nat) = r.vektor then _ else _) = _
      rw [if_neg (Ne.symm h2)]; exact h41
    · show (if (0xFF : Nat) = r.vektor then _ else _) = _
      rw [if_neg (by omega)]; exact hff
    · intro v n hv
      show fehlercodeC v = false
      unfold setze at hv
      by_cases e : v = r.vektor
      · subst e; exact hf
      · rw [if_neg e] at hv; exact hpl v n hv
    · intro v n hv
      unfold setze at hv
      by_cases e : v = r.vektor
      · rw [if_pos e] at hv; cases hv
      · rw [if_neg e] at hv; exact hfc v n hv
  · -- the error-code installer
    cases hn : nimmtFc r.vektor <;> rw [hn] at h <;> simp only [Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq, reduceCtorEq] at h
    subst h
    unfold nimmtFc at hn
    have hv0 : r.vektor ≠ 0x40 := by intro e; rw [e] at hn; exact absurd hn (by decide)
    have hv1 : r.vektor ≠ 0x41 := by intro e; rw [e] at hn; exact absurd hn (by decide)
    have hvf : r.vektor ≠ 0xFF := by intro e; rw [e] at hn; exact absurd hn (by decide)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (if (0x40 : Nat) = r.vektor then _ else _) = _
      rw [if_neg (Ne.symm hv0)]; exact h40
    · show (if (0x41 : Nat) = r.vektor then _ else _) = _
      rw [if_neg (Ne.symm hv1)]; exact h41
    · show (if (0xFF : Nat) = r.vektor then _ else _) = _
      rw [if_neg (Ne.symm hvf)]; exact hff
    · intro v n hv
      unfold setze at hv
      by_cases e : v = r.vektor
      · rw [if_pos e] at hv; cases hv
      · rw [if_neg e] at hv; exact hpl v n hv
    · intro v n hv
      unfold setze at hv
      by_cases e : v = r.vektor
      · subst e; exact hn
      · rw [if_neg e] at hv; exact hfc v n hv

theorem installiereAlle_passt : ∀ (rs : List Ruf) {t t' : Tafel}, Passt t →
    installiereAlle t rs = some t' → Passt t'
  | [], t, t', hp, h => by
      simp only [installiereAlle, Option.some.injEq] at h; subst h; exact hp
  | r :: rs, t, t', hp, h => by
      simp only [installiereAlle] at h
      cases hi : installiere t r with
      | none => rw [hi] at h; cases h
      | some t1 =>
          rw [hi] at h
          exact installiereAlle_passt rs (installiere_passt hp hi) h

/-- **THE RUNTIME'S VECTORS SURVIVE EVERY INSTALL**: after the build and any sequence of
    installer calls that return, the timer, the wake vector and the spurious vector hold the
    runtime's stubs. -/
theorem installieren_bewahrt_laufzeit (rs : List Ruf) {t : Tafel}
    (h : installiereAlle bau rs = some t) :
    t 0x40 = .takt ∧ t 0x41 = .wecken ∧ t 0xFF = .unecht :=
  let hp := installiereAlle_passt rs bau_passt h
  ⟨hp.1, hp.2.1, hp.2.2.1⟩

/-- **EVERY STUB ON A VECTOR OF ITS KIND**: a plain program stub never on an error-code vector,
    an error-code stub only on one. -/
theorem installieren_passt (rs : List Ruf) {t : Tafel} (h : installiereAlle bau rs = some t) :
    (∀ v n, t v = .programm n → v ∉ fehlercodeListe) ∧
    (∀ v n, t v = .programmFc n → v ∈ fehlercodeListe) := by
  have hp := installiereAlle_passt rs bau_passt h
  refine ⟨fun v n hv hm => ?_, fun v n hv => ?_⟩
  · have hf := hp.2.2.2.1 v n hv
    have hl : v < 256 := by
      simp only [fehlercodeListe, List.mem_cons, List.mem_nil_iff, or_false] at hm; omega
    have := (fehlercode_c_ist_die_liste v hl).mpr hm
    rw [hf] at this; cases this
  · have hf := hp.2.2.2.2 v n hv
    have hl : v < 256 := by
      unfold fehlercodeC at hf
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hf
      omega
    exact (fehlercode_c_ist_die_liste v hl).mp hf

/-- **The refusals are load-bearing**: an installer without its test would put a plain stub on
    #GP (13) and overwrite the timer. -/
theorem installieren_ohne_wache_waere_falsch :
    let t1 := setze bau 13 (.programm 1)
    let t2 := setze t1 0x40 (.programm 2)
    ¬ Passt t1 ∧ ¬ Passt t2 := by
  intro t1 t2
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have := hp.2.2.2.1 13 1 rfl
    exact absurd this (by decide)
  · have := hp.1
    exact absurd this (by decide)

/-- **Witness**: an NMI entry on 2, a device entry on `0xF0`, the kernel service vector `0x80`
    taken by the program, and a #GP entry on 13 through the error-code twin -- all installed;
    and the timer refused. -/
theorem idt_metall_zeuge :
    ∃ t, installiereAlle bau [⟨false, 2, 1⟩, ⟨false, 0xF0, 2⟩, ⟨false, 0x80, 3⟩, ⟨true, 13, 4⟩]
        = some t ∧ t 2 = .programm 1 ∧ t 13 = .programmFc 4 ∧ t 0x40 = .takt ∧
      installiere bau ⟨false, 0x40, 5⟩ = none ∧ installiere bau ⟨true, 2, 6⟩ = none ∧
      dekodiere (kodiere 0xFFFFFFFF80001234) = 0xFFFFFFFF80001234 := by
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, kodiere_dekodiere _ (by decide)⟩

end MetallIdt

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.MetallIdt.kodiere_dekodiere
#print axioms Gabbro.Grammatik.MetallIdt.art_ist_interrupt_gate
#print axioms Gabbro.Grammatik.MetallIdt.fehlercode_c_ist_die_liste
#print axioms Gabbro.Grammatik.MetallIdt.installieren_bewahrt_laufzeit
#print axioms Gabbro.Grammatik.MetallIdt.installieren_passt
#print axioms Gabbro.Grammatik.MetallIdt.installieren_ohne_wache_waere_falsch
#print axioms Gabbro.Grammatik.MetallIdt.idt_metall_zeuge
