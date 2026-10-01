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

/- CUTS:
    - Skeleton only: realised predicates plus the length fact.
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

end Gabbro.Grammatik.X86
