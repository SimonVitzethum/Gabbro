/-
  File:      Grammatik/X86/AccessExecution.lean
  Subject:   Executed pilot instruction to realised access footprint.

  Lane 568: connects `Zugriffe.zugriff` (a checked POTENTIAL footprint from
  the pre-state) to ACTUAL successful `Ausfuehrung.schritt` and
  `Byteschritt.byteschritt` for all 14 pilot forms. Every footprint fact
  below is derived from a successful step premise (`schritt d s = some s'`
  or `byteschritt s = .weiter s'`); a computed list alone is never a
  realised trace. Reuses the `Speicher` read/write frame lemmas through
  the `Zugriffe` linkage theorems. The eight `Fuss` addresses stay a byte
  set, not one atomic TSO event; the full W/GX mapping stays OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Zugriffe
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- A realised step: the actual `schritt` succeeded. -/
def istRealisiert (d : Decodiert) (s s' : Zustand) : Prop :=
  schritt d s = some s'

/-- A realised byte step: actual fetch, decode and `schritt` succeeded. -/
def byteRealisiert (s s' : Zustand) : Prop :=
  byteschritt s = .weiter s'

/-- A realised step had a valid decode length. -/
theorem realisiert_laenge_ok (d : Decodiert) (s s' : Zustand)
    (hstep : istRealisiert d s s') : laengeOk d.laenge = true := by
  unfold istRealisiert at hstep
  match hm : laengeOk d.laenge with
  | true => rfl
  | false =>
    rw [schritt_laenge_verweigert d s hm] at hstep
    cases hstep

/-! ## 1. Byte-step decomposition: a realised byte step is a fetched `schritt`. -/

/-- A realised byte step runs the existing `schritt` on a fetched instruction. -/
theorem byte_aus_weiter (s s' : Zustand)
    (h : byteRealisiert s s') :
    ∃ d rest, fetchDekodiert s = some (d, rest) ∧ schritt d s = some s' := by
  unfold byteRealisiert byteschritt at h
  match hf : fetchDekodiert s with
  | none =>
    simp only [hf] at h
    cases h
  | some pr =>
    obtain ⟨d, rest⟩ := pr
    match hs : schritt d s with
    | none =>
      simp only [hf, hs] at h
      cases h
    | some s'' =>
      simp only [hf, hs] at h
      cases h
      exact ⟨d, rest, rfl, hs⟩

/-! ## 2. Realised permission success: derived from the step, never assumed. -/

/-- A realised `store` really wrote: the checked write succeeds and every
    permission map is preserved. -/
theorem realisiert_store64_gefunden (dd : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hstep : istRealisiert dd s s') :
    ∃ m, write64 s.speicher (effAddr s base disp) (s.register src) = some m ∧
      s'.speicher.lesbar = s.speicher.lesbar ∧
      s'.speicher.schreibbar = s.speicher.schreibbar ∧
      s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar := by
  unfold istRealisiert at hstep
  match hw : write64 s.speicher (effAddr s base disp) (s.register src) with
  | none =>
    rw [schritt_store64_verweigert dd s base src disp hok h hw] at hstep
    cases hstep
  | some m =>
    have hperm := schritt_store64_berechtigungen dd s s' base src disp m
      hok h hw hstep
    exact ⟨m, rfl, hperm.1, hperm.2.1, hperm.2.2⟩

/-- A realised `load` really read: the checked read succeeds, the
    destination holds the value that read returned, memory is unchanged. -/
theorem realisiert_load64_gefunden (dd : Decodiert) (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .load64 dst base disp)
    (hstep : istRealisiert dd s s') :
    ∃ v, read64 s.speicher (effAddr s base disp) = some v ∧
      s'.register dst = v ∧ s'.speicher = s.speicher := by
  unfold istRealisiert at hstep
  match hrd : read64 s.speicher (effAddr s base disp) with
  | none =>
    rw [schritt_load64_verweigert dd s dst base disp hok h hrd] at hstep
    cases hstep
  | some v =>
    rw [schritt_load64_erfolg dd s dst base disp v hok h hrd] at hstep
    cases hstep
    exact ⟨v, rfl, by simp [schrittRegister, regSet], rfl⟩

/-- A realised `push` really wrote below the old top: the checked write
    succeeds, the stack pointer moved, permissions are preserved. -/
theorem realisiert_push64_gefunden (dd : Decodiert) (s s' : Zustand)
    (src : Register)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .push64 src)
    (hstep : istRealisiert dd s s') :
    ∃ m, write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m ∧
      s'.register Register.rsp = s.register Register.rsp - BitVec.ofNat 64 8 ∧
      s'.speicher.lesbar = s.speicher.lesbar := by
  unfold istRealisiert at hstep
  match hw : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) with
  | none =>
    rw [schritt_push64_verweigert dd s src hok h hw] at hstep
    cases hstep
  | some m =>
    have hperm := schritt_push64_berechtigungen dd s s' src m hok h hw hstep
    rw [schritt_push64_erfolg dd s src m hok h hw] at hstep
    cases hstep
    exact ⟨m, rfl, by simp [schrittPush, regSet], hperm.1⟩

/-- A realised `pop` into another register really read the old top: the
    checked read succeeds, the destination holds that value, the stack
    pointer advanced past the word, memory is unchanged. -/
theorem realisiert_pop64_gefunden (dd : Decodiert) (s s' : Zustand)
    (dst : Register)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hstep : istRealisiert dd s s') :
    ∃ v, read64 s.speicher (s.register Register.rsp) = some v ∧
      s'.register dst = v ∧
      s'.register Register.rsp = s.register Register.rsp + BitVec.ofNat 64 8 ∧
      s'.speicher = s.speicher := by
  unfold istRealisiert at hstep
  match hrd : read64 s.speicher (s.register Register.rsp) with
  | none =>
    rw [schritt_pop64_verweigert dd s dst hok h hrd] at hstep
    cases hstep
  | some v =>
    rw [schritt_pop64_reg dd s dst v hok h hdst hrd] at hstep
    cases hstep
    exact ⟨v, rfl, by simp [schrittPopReg, regSet],
      by simp [schrittPopReg, regSet, Ne.symm hdst], rfl⟩

/-- A realised `call` really stored the actual next RIP below the old
    top: the checked write succeeds, control reaches post-decode plus the
    displacement, permissions are preserved. -/
theorem realisiert_call32_gefunden (dd : Decodiert) (s s' : Zustand)
    (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .call32 disp)
    (hstep : istRealisiert dd s s') :
    ∃ m, write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dd.laenge) = some m ∧
      s'.rip = ripNach s.rip dd.laenge + dispWort disp ∧
      s'.speicher.lesbar = s.speicher.lesbar := by
  unfold istRealisiert at hstep
  match hw : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dd.laenge) with
  | none =>
    rw [schritt_call32_verweigert dd s disp hok h hw] at hstep
    cases hstep
  | some m =>
    have hperm := schritt_call32_berechtigungen dd s s' disp m hok h hw hstep
    rw [schritt_call32_erfolg dd s disp m hok h hw] at hstep
    cases hstep
    exact ⟨m, rfl, rfl, hperm.1⟩

/-- A realised `ret` really read its target off the old top: the checked
    read succeeds, control reaches the value that read returned, the stack
    pointer advanced, memory is unchanged. -/
theorem realisiert_ret_gefunden (dd : Decodiert) (s s' : Zustand)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .ret)
    (hstep : istRealisiert dd s s') :
    ∃ ziel, read64 s.speicher (s.register Register.rsp) = some ziel ∧
      s'.rip = ziel ∧
      s'.register Register.rsp = s.register Register.rsp + BitVec.ofNat 64 8 ∧
      s'.speicher = s.speicher := by
  unfold istRealisiert at hstep
  match hrd : read64 s.speicher (s.register Register.rsp) with
  | none =>
    rw [schritt_ret_verweigert dd s hok h hrd] at hstep
    cases hstep
  | some ziel =>
    rw [schritt_ret_erfolg dd s ziel hok h hrd] at hstep
    cases hstep
    exact ⟨ziel, rfl, rfl, rfl, rfl⟩

/-! ## 3. Realised footprints: frame, shape and stored word from `hstep` alone. -/

/-- A realised `store` changes only its extracted footprint: every changed
    byte lies in the eight pre-state addresses, the footprint is exactly
    those addresses, and the stored word is the pre-state source register. -/
theorem realisiert_store64_fuss (dd : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hstep : istRealisiert dd s s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    (zugriff dd s).schreiben = Fuss (effAddr s base disp) ∧
    (zugriff dd s).speicherWert = some (s.register src) := by
  have hex := realisiert_store64_gefunden dd s s' base src disp hok h hstep
  have hwr := (Classical.choose_spec hex).1
  have hfuss := erfolg_store64_im_fuss s s' base src disp
    (Classical.choose hex) dd hok h hwr hstep
  have hzg := zugriff_store64 dd s base src disp h
  refine ⟨hfuss.1, by rw [hzg], by rw [hzg]⟩

/-- A realised `push` changes only below the old top: every changed byte
    lies in the eight extracted addresses, the footprint is exactly those
    addresses, and the stored word is the pre-state source register read
    before the move. -/
theorem realisiert_push64_fuss (dd : Decodiert) (s s' : Zustand)
    (src : Register)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .push64 src)
    (hstep : istRealisiert dd s s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    (zugriff dd s).schreiben = Fuss (stapelOben s) ∧
    (zugriff dd s).speicherWert = some (s.register src) := by
  have hex := realisiert_push64_gefunden dd s s' src hok h hstep
  have hwr := (Classical.choose_spec hex).1
  have hfuss := erfolg_push64_im_fuss s s' src
    (Classical.choose hex) dd hok h hwr hstep
  have hzg := zugriff_push64 dd s src h
  refine ⟨hfuss.1, by rw [hzg], by rw [hzg]⟩

/-- A realised `call` changes only below the old top: every changed byte
    lies in the eight extracted addresses, the footprint is exactly those
    addresses, and the stored word is the ACTUAL next RIP evaluated in the
    pre-state. -/
theorem realisiert_call32_fuss (dd : Decodiert) (s s' : Zustand)
    (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .call32 disp)
    (hstep : istRealisiert dd s s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    (zugriff dd s).schreiben = Fuss (stapelOben s) ∧
    (zugriff dd s).speicherWert = some (ripNach s.rip dd.laenge) := by
  have hex := realisiert_call32_gefunden dd s s' disp hok h hstep
  have hwr := (Classical.choose_spec hex).1
  have hfuss := erfolg_call32_im_fuss s s' disp
    (Classical.choose hex) dd hok h hwr hstep
  have hzg := zugriff_call32 dd s disp h
  refine ⟨hfuss.1, by rw [hzg], by rw [hzg]⟩

/-- A realised `load` reads exactly its extracted footprint: memory is
    unchanged, the read footprint is the eight pre-state addresses, nothing
    is written, and the destination holds the value the actual read at the
    footprint head returned. -/
theorem realisiert_load64_fuss (dd : Decodiert) (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .load64 dst base disp)
    (hstep : istRealisiert dd s s') :
    s'.speicher = s.speicher ∧
    (zugriff dd s).lesen = Fuss (effAddr s base disp) ∧
    (zugriff dd s).schreiben = [] ∧
    ∃ v, read64 s.speicher ((zugriff dd s).lesen.getD 0 0) = some v ∧
      s'.register dst = v := by
  have hex := realisiert_load64_gefunden dd s s' dst base disp hok h hstep
  have hspec := Classical.choose_spec hex
  have hliest := zugriff_load64_liest s s' dst base disp
    (Classical.choose hex) dd hok h hspec.1 hstep
  have hzg := zugriff_load64 dd s dst base disp h
  refine ⟨hspec.2.2, by rw [hzg], by rw [hzg], _, hliest.1, hspec.2.1⟩

/-- A realised `pop` into another register reads exactly the old top:
    memory is unchanged, the read footprint is the eight old-stack
    addresses, nothing is written, and the destination holds the value the
    actual read at the footprint head returned. -/
theorem realisiert_pop64_fuss (dd : Decodiert) (s s' : Zustand)
    (dst : Register)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hstep : istRealisiert dd s s') :
    s'.speicher = s.speicher ∧
    (zugriff dd s).lesen = Fuss (s.register Register.rsp) ∧
    (zugriff dd s).schreiben = [] ∧
    ∃ v, read64 s.speicher ((zugriff dd s).lesen.getD 0 0) = some v ∧
      s'.register dst = v := by
  have hex := realisiert_pop64_gefunden dd s s' dst hok h hdst hstep
  have hspec := Classical.choose_spec hex
  have hliest := zugriff_pop64_liest s s' dst
    (Classical.choose hex) dd hok h hdst hspec.1 hstep
  have hzg := zugriff_pop64 dd s dst h
  refine ⟨hspec.2.2.2, by rw [hzg], by rw [hzg], _, hliest.1, hspec.2.1⟩

/-- A realised `ret` reads exactly the old top: memory is unchanged, the
    read footprint is the eight old-stack addresses, nothing is written,
    and control reaches the value the actual read at the footprint head
    returned. -/
theorem realisiert_ret_fuss (dd : Decodiert) (s s' : Zustand)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .ret)
    (hstep : istRealisiert dd s s') :
    s'.speicher = s.speicher ∧
    (zugriff dd s).lesen = Fuss (s.register Register.rsp) ∧
    (zugriff dd s).schreiben = [] ∧
    ∃ ziel, read64 s.speicher ((zugriff dd s).lesen.getD 0 0) = some ziel ∧
      s'.rip = ziel := by
  have hex := realisiert_ret_gefunden dd s s' hok h hstep
  have hspec := Classical.choose_spec hex
  have hliest := zugriff_ret_liest s s'
    (Classical.choose hex) dd hok h hspec.1 hstep
  have hzg := zugriff_ret dd s h
  refine ⟨hspec.2.2.2, by rw [hzg], by rw [hzg], _, hliest.1, hliest.2⟩

/-! ## 4. Generic coverage: every realised pilot step respects its footprint. -/

/-- Vacuous frame: identical memories change no byte inside any list. -/
theorem frame_aus_speichergleich (s s' : Zustand) (z : Zugriff)
    (hmem : s'.speicher = s.speicher) :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x → x ∈ z.schreiben) := by
  intro x hx
  rw [hmem] at hx
  exact absurd rfl hx

/-- GENERIC COVERAGE over all 14 pilot forms: a realised step changes no
    byte outside its extracted write footprint, and both footprints are
    either empty or one eight-byte `Fuss`. Pure and read forms change no
    byte at all; write forms change only their eight pre-state addresses. -/
theorem realisiert_fuss_abdeckung (dd : Decodiert) (s s' : Zustand)
    (hok : laengeOk dd.laenge = true)
    (hstep : istRealisiert dd s s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    ((zugriff dd s).lesen = [] ∨ ∃ a, (zugriff dd s).lesen = Fuss a) ∧
    ((zugriff dd s).schreiben = [] ∨ ∃ a, (zugriff dd s).schreiben = Fuss a) := by
  match hb : dd.befehl with
  | .movImm64 dst v =>
    have hmem := schritt_movImm64_speicher dd s s' dst v hok hb hstep
    have hzg := zugriff_movImm64 dd s dst v hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .movReg64 dst src =>
    have hmem := schritt_movReg64_speicher dd s s' dst src hok hb hstep
    have hzg := zugriff_movReg64 dd s dst src hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .addReg64 dst src =>
    have hmem := schritt_addReg64_speicher dd s s' dst src hok hb hstep
    have hzg := zugriff_addReg64 dd s dst src hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .subReg64 dst src =>
    have hmem := schritt_subReg64_speicher dd s s' dst src hok hb hstep
    have hzg := zugriff_subReg64 dd s dst src hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .xorReg64 dst src =>
    have hmem := schritt_xorReg64_speicher dd s s' dst src hok hb hstep
    have hzg := zugriff_xorReg64 dd s dst src hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .cmpReg64 lhs rhs =>
    have hmem := schritt_cmpReg64_speicher dd s s' lhs rhs hok hb hstep
    have hzg := zugriff_cmpReg64 dd s lhs rhs hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .load64 dst base disp =>
    have hfuss := realisiert_load64_fuss dd s s' dst base disp hok hb hstep
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hfuss.1,
      Or.inr ⟨_, hfuss.2.1⟩, Or.inl hfuss.2.2.1⟩
  | .store64 base src disp =>
    have hfuss := realisiert_store64_fuss dd s s' base src disp hok hb hstep
    have hzg := zugriff_store64 dd s base src disp hb
    exact ⟨hfuss.1, Or.inl (by rw [hzg]), Or.inr ⟨_, hfuss.2.1⟩⟩
  | .jump32 disp =>
    have hmem := schritt_jump32_speicher dd s s' disp hok hb hstep
    have hzg := zugriff_jump32 dd s disp hb
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
      Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .jumpIf32 cond disp =>
    match hc : bedingung cond s.flags with
    | true =>
      have hmem := schritt_jumpIf32_genommen_speicher dd s s' cond disp
        hok hb hc hstep
      have hzg := zugriff_jumpIf32 dd s cond disp hb
      exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
        Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
    | false =>
      have hmem := schritt_jumpIf32_nicht_speicher dd s s' cond disp
        hok hb hc hstep
      have hzg := zugriff_jumpIf32 dd s cond disp hb
      exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
        Or.inl (by rw [hzg]), Or.inl (by rw [hzg])⟩
  | .push64 src =>
    have hfuss := realisiert_push64_fuss dd s s' src hok hb hstep
    have hzg := zugriff_push64 dd s src hb
    exact ⟨hfuss.1, Or.inl (by rw [hzg]), Or.inr ⟨_, hfuss.2.1⟩⟩
  | .pop64 dst =>
    by_cases hdst : dst = Register.rsp
    · subst hdst
      unfold istRealisiert at hstep
      match hrd : read64 s.speicher (s.register Register.rsp) with
      | none =>
        rw [schritt_pop64_verweigert dd s Register.rsp hok hb hrd] at hstep
        cases hstep
      | some v =>
        have hmem := schritt_pop64_speicher dd s s' Register.rsp v
          hok hb hrd hstep
        have hzg := zugriff_pop64 dd s Register.rsp hb
        exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hmem,
          Or.inr ⟨_, by rw [hzg]⟩, Or.inl (by rw [hzg])⟩
    · have hfuss := realisiert_pop64_fuss dd s s' dst hok hb hdst hstep
      exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hfuss.1,
        Or.inr ⟨_, hfuss.2.1⟩, Or.inl hfuss.2.2.1⟩
  | .call32 disp =>
    have hfuss := realisiert_call32_fuss dd s s' disp hok hb hstep
    have hzg := zugriff_call32 dd s disp hb
    exact ⟨hfuss.1, Or.inl (by rw [hzg]), Or.inr ⟨_, hfuss.2.1⟩⟩
  | .ret =>
    have hfuss := realisiert_ret_fuss dd s s' hok hb hstep
    exact ⟨frame_aus_speichergleich s s' (zugriff dd s) hfuss.1,
      Or.inr ⟨_, hfuss.2.1⟩, Or.inl hfuss.2.2.1⟩

/-! ## 5. Alias shapes: base-is-source, stack-source, next-RIP. -/

/-- BASE-IS-SOURCE ALIAS: a realised `store` whose base is its own source
    evaluates footprint and stored word at the same pre-state register: the
    address comes from the source value, and the stored word is that same
    value. -/
theorem realisiert_store_alias (dd : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hbase : base = src)
    (hstep : istRealisiert dd s s') :
    (zugriff dd s).schreiben = Fuss (s.register src + dispWort disp) ∧
    (zugriff dd s).speicherWert = some (s.register base) ∧
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) := by
  have hfuss := realisiert_store64_fuss dd s s' base src disp hok h hstep
  have hzg := zugriff_store64 dd s base src disp h
  refine ⟨by rw [hzg, ← hbase]; rfl, by rw [hzg, hbase], hfuss.1⟩

/-- STACK-SOURCE (`push rsp`): a realised `push` of the stack pointer stores
    the OLD top below itself: the stored word is the pre-state `rsp`, read
    before the move. -/
theorem realisiert_push_rsp (dd : Decodiert) (s s' : Zustand)
    (src : Register)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .push64 src)
    (hsrc : src = Register.rsp)
    (hstep : istRealisiert dd s s') :
    (zugriff dd s).schreiben = Fuss (stapelOben s) ∧
    (zugriff dd s).speicherWert = some (s.register Register.rsp) ∧
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) := by
  have hfuss := realisiert_push64_fuss dd s s' src hok h hstep
  have hzg := zugriff_push64 dd s src h
  refine ⟨by rw [hzg], by rw [hzg, hsrc], hfuss.1⟩

/-! ## 6. Byte bridge: realised byte steps carry realised footprints. -/

/-- BYTE-REALISED FOOTPRINT: a realised byte step fetched some instruction
    whose realised footprint covers every changed byte. The footprint comes
    from actual execution, never from a caller-supplied decoded value. -/
theorem byte_realisiert_fuss (s s' : Zustand)
    (h : byteRealisiert s s') :
    ∃ d rest, fetchDekodiert s = some (d, rest) ∧ istRealisiert d s s' ∧
      (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
        x ∈ (zugriff d s).schreiben) := by
  have hex := byte_aus_weiter s s' h
  have hs1 := Classical.choose_spec hex
  have hs2 := Classical.choose_spec hs1
  have hok := realisiert_laenge_ok (Classical.choose hex) s s' hs2.2
  have hab := realisiert_fuss_abdeckung (Classical.choose hex) s s' hok hs2.2
  exact ⟨_, _, hs2.1, hs2.2, hab.1⟩

/-- FETCHED-FROM-ACTUAL-BYTES: fetch plus `schritt` success is a realised
    byte step, and the fetched instruction decodes the actual fetched
    memory bytes at `rip`. -/
theorem byte_realisiert_aus_bytes (s s' : Zustand) (d : Decodiert)
    (rest : List Byte)
    (hf : fetchDekodiert s = some (d, rest))
    (hs : schritt d s = some s') :
    byteRealisiert s s' ∧ decode (geholt s) = some (d, rest) := by
  have hcorr := fetchDekodiert_entspricht s d rest hf
  refine ⟨?_, hcorr.1⟩
  unfold byteRealisiert
  exact byteschritt_weiter s s' d rest hf hs

/-! ## 7. Refusal: invalid length or failed fetch yields no realised trace. -/

/-- A bad decode length admits no realised step for any footprint. -/
theorem realisiert_versagt_laenge (dd : Decodiert) (s s' : Zustand)
    (h : laengeOk dd.laenge = false)
    (hstep : istRealisiert dd s s') : False :=
  zugriff_laenge_versagt_kein_erfolg s s' dd h hstep

/-- A failed fetch admits no realised byte step: without decode there is
    no transition, hence no footprint. -/
theorem byte_ohne_fetch_kein_realisiert (s s' : Zustand)
    (hf : fetchDekodiert s = none) :
    ¬ byteRealisiert s s' := by
  intro h
  have hex := byte_aus_weiter s s' h
  have hs1 := Classical.choose_spec hex
  have hs2 := Classical.choose_spec hs1
  simp [hf] at hs2

/-! ## 8. One word footprint is not one atomic TSO event. -/

/-- A realised `store` footprint is eight byte addresses carrying one word,
    and no extraction is one atomic multi-byte event: the byte set and the
    hardware event are distinguished by construction (`AtomarZugriff` is
    empty). The per-access W/GX mapping stays OPEN. -/
theorem realisiert_store64_wort_kein_atom (dd : Decodiert) (s s' : Zustand)
    (base src : Register) (disp : BitVec 32)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hstep : istRealisiert dd s s') :
    ¬ AtomarZugriff (zugriff dd s) ∧
    (zugriff dd s).schreiben.length = 8 ∧
    (zugriff dd s).speicherWert = some (s.register src) := by
  have hfuss := realisiert_store64_fuss dd s s' base src disp hok h hstep
  have hacht := zugriff_store64_acht s base src disp dd h
  exact ⟨kein_atomarer_zugriff _, hacht, hfuss.2.2⟩

/-! ## 9. Joint witness: a real reached memory-changing store step. -/

/-- Witness decoded store: `store [rsp], rax` with a valid length. -/
def zeugeStore : Decodiert :=
  { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0),
    laenge := 4 }

/-- Witness pre-state: `rax = 42` over the zeroed witness memory. -/
def zeugeStoreVor : Zustand :=
  { zeugeZustand with register := regSet zeugeReg Register.rax 42 }

/-- The witness store step observably changes byte 8192 from zero to 42. -/
theorem schritt_zeuge_speicher :
    ((schritt zeugeStore zeugeStoreVor).map
      (fun s' => s'.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) := by
  decide

/-- JOINT WITNESS for the generic coverage: the store step is realised
    (valid length, successful step), starts from zeroed memory and
    observably changes byte 8192 to 42. All premises of
    `realisiert_fuss_abdeckung` are instantiated jointly on this real
    reached memory-changing execution. -/
theorem realisiert_fuss_abdeckung_zeuge :
    ∃ dd s s', laengeOk dd.laenge = true ∧ istRealisiert dd s s' ∧
      s.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 0 ∧
      s'.speicher.bytes (BitVec.ofNat 64 8192) = BitVec.ofNat 8 42 := by
  match hs : schritt zeugeStore zeugeStoreVor with
  | none =>
    have h := schritt_zeuge_speicher
    simp [hs] at h
  | some s' =>
    have hb : s'.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 42 := by
      have h := schritt_zeuge_speicher
      simp only [hs, Option.map_some, Option.some.injEq] at h
      exact h
    exact ⟨zeugeStore, zeugeStoreVor, s', rfl, hs, rfl, hb⟩

/-- PLANTED REFUSAL: the truncated jump has no byte transition. -/
theorem byte_zeuge_verweigert :
    byteschritt stumpfStart = .verweigert := by
  match hb : byteschritt stumpfStart with
  | .weiter s' =>
    have h := praefix_abgeschnitten_verweigert
    rw [hb] at h
    have h2 : ausgangRip (ByteAusgang.weiter s') = some s'.rip := rfl
    rw [h2] at h
    cases h
  | .verweigert => rfl

/- CUTS:
    Proved here: `zugriff` connected to ACTUAL successful `schritt` and
    `byteschritt` for all 14 pilot forms. Realised permission success is
    derived from the step alone (§2: six `gefunden` lemmas); realised
    footprints give frame, exact shape and stored word or read value from
    `hstep` alone (§3: six `fuss` lemmas); the generic coverage theorem
    (§4: `realisiert_fuss_abdeckung`) cases over all 14 forms; alias
    shapes pin base-is-source and `push rsp` to pre-state evaluation (§5);
    realised byte steps carry realised footprints of instructions decoded
    from actual memory bytes (§6); bad length and failed fetch yield no
    realised trace (§7); the eight-byte word footprint is distinguished
    from one atomic TSO event by construction (§8); a joint
    memory-changing store witness plus a planted byte refusal (§9).
    NOT proved here, and not claimed:
    - No source correspondence: nothing links Gabbro source, IR, checker
      verdicts or contracts to these footprints; no entry, ABI, loader,
      relocation, image-layout or cost claim.
    - No W/GX simulation: per-access linearisation, TSO visibility, byte
      order beyond little-endian `wortByte`, grouping and tearing stay
      OPEN for the TSO-bridge lanes.
    - No concurrency claim: `lauf`/`laufBytes` are sequential folds, and
      `AblaufSpur` stays empty; LOCK/RMW/fence/narrow forms do not exist
      in `Befehl` and are not admitted here.
    - No termination claim: `verweigert` is the absence of a transition,
      never normal program termination.
    - `Classical.choice` is used only to name the witness of realised
      read/write existence; all axioms stay within the standard goal set
      (propext, Classical.choice, Quot.sound).
    - Consumer interface: downstream lanes cite `realisiert_fuss_abdeckung`
      (uniform frame plus empty-or-eight shape), `byte_realisiert_fuss`
      (byte-step to footprint) and `realisiert_fuss_abdeckung_zeuge`
      (joint witness); refusals cite `realisiert_versagt_laenge` and
      `byte_ohne_fetch_kein_realisiert`.
-/

#print axioms realisiert_laenge_ok
#print axioms byte_aus_weiter
#print axioms realisiert_store64_gefunden
#print axioms realisiert_load64_gefunden
#print axioms realisiert_push64_gefunden
#print axioms realisiert_pop64_gefunden
#print axioms realisiert_call32_gefunden
#print axioms realisiert_ret_gefunden
#print axioms realisiert_store64_fuss
#print axioms realisiert_push64_fuss
#print axioms realisiert_call32_fuss
#print axioms realisiert_load64_fuss
#print axioms realisiert_pop64_fuss
#print axioms realisiert_ret_fuss
#print axioms frame_aus_speichergleich
#print axioms realisiert_fuss_abdeckung
#print axioms realisiert_store_alias
#print axioms realisiert_push_rsp
#print axioms byte_realisiert_fuss
#print axioms byte_realisiert_aus_bytes
#print axioms realisiert_versagt_laenge
#print axioms byte_ohne_fetch_kein_realisiert
#print axioms realisiert_store64_wort_kein_atom
#print axioms schritt_zeuge_speicher
#print axioms realisiert_fuss_abdeckung_zeuge
#print axioms byte_zeuge_verweigert

end Gabbro.Grammatik.X86
