/-
  Composition closing: per-access permission check to fetch/decode/execute
  (lane 857).

  Producer/consumer interface closed here: the producers are the accepted
  permission primitives (`Speicher.read64`/`write64` with their `lesbar8` /
  `schreibbar8` checks, `Byteschritt` fetch with its `ausfuehrbarN` check)
  together with the accepted step/footprint theorems (`Zugriffe`,
  `AccessExecution`, `WordAtomicity`); the consumer is the checked closing
  step below, which runs only the existing `byteschritt`. Nothing is
  redefined here: no second loader, decoder, executor or ISA model.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.Zugriffe
import Grammatik.X86.AccessExecution
import Grammatik.X86.WordAtomicity

namespace Gabbro.Grammatik.X86

/-- Checked permission bundle for one fetched instruction: the consumed
    fetch prefix is executable, and every footprint address the accepted
    extraction names carries its data permission. Stated per byte address,
    so an unchecked access is unrepresentable, not merely absent. -/
def PermGeprueft (s : Zustand) (d : Decodiert) : Prop :=
  ausfuehrbarN s.speicher s.rip d.laenge = true ∧
  (∀ x, x ∈ (zugriff d s).lesen → s.speicher.lesbar x = true) ∧
  (∀ x, x ∈ (zugriff d s).schreiben → s.speicher.schreibbar x = true)

/-! ## 1. Byte-permission bridge: `lesbar8`/`schreibbar8` to bytes. -/

/-- A checked eight-byte read footprint grants every footprint byte its
    read permission: reuse the accepted `fuss_mem` byte set. -/
theorem lesbar8_gibt_byte (m : Speicher) (a x : Adresse)
    (h : lesbar8 m a = true) (hx : x ∈ Fuss a) :
    m.lesbar x = true := by
  rw [fuss_mem] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hdis : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hdis with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [lesbar8]

/-- A checked eight-byte write footprint grants every footprint byte its
    write permission: reuse the accepted `fuss_mem` byte set. -/
theorem schreibbar8_gibt_byte (m : Speicher) (a x : Adresse)
    (h : schreibbar8 m a = true) (hx : x ∈ Fuss a) :
    m.schreibbar x = true := by
  rw [fuss_mem] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hdis : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hdis with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [schreibbar8]

/-- Contrapositive: one denied footprint byte fails the eight-byte read
    check, so no unchecked read is representable through `read64`. -/
theorem lesbar8_aus_byte_falsch (m : Speicher) (a x : Adresse)
    (hx : x ∈ Fuss a) (hb : m.lesbar x = false) :
    lesbar8 m a = false := by
  match he : lesbar8 m a with
  | true =>
    have ht := lesbar8_gibt_byte m a x he hx
    rw [ht] at hb
    cases hb
  | false => rfl

/-- Contrapositive: one denied footprint byte fails the eight-byte write
    check, so no unchecked store is representable through `write64`. -/
theorem schreibbar8_aus_byte_falsch (m : Speicher) (a x : Adresse)
    (hx : x ∈ Fuss a) (hb : m.schreibbar x = false) :
    schreibbar8 m a = false := by
  match he : schreibbar8 m a with
  | true =>
    have ht := schreibbar8_gibt_byte m a x he hx
    rw [ht] at hb
    cases hb
  | false => rfl

/-- A failed eight-byte read check admits no `read64` outcome at all:
    refusal by construction, mirroring the accepted `write64_verweigert`. -/
theorem read64_aus_lesbar_falsch (m : Speicher) (a : Adresse)
    (h : lesbar8 m a = false) : read64 m a = none := by
  unfold read64
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-! ## 2. Success: a realised step checked every footprint permission. -/

/-- SUCCESS: a successful step over an arbitrary admitted instruction
    checked every footprint permission: reads went through a successful
    `read64` (hence `lesbar8`, via the accepted `read64_braucht_lesbar`),
    writes through a successful `write64` (hence `schreibbar8`, via the
    accepted `write64_braucht_schreibbar`), and pure forms touch no byte.
    Case analysis reuses the accepted `zugriff_*` equations and the
    accepted `schritt_*_verweigert` refusals; no step fact is re-proved. -/
theorem zugriff_perm_aus_schritt (dd : Decodiert) (s s' : Zustand)
    (hok : laengeOk dd.laenge = true) (hstep : schritt dd s = some s') :
    (∀ x, x ∈ (zugriff dd s).lesen → s.speicher.lesbar x = true) ∧
    (∀ x, x ∈ (zugriff dd s).schreiben → s.speicher.schreibbar x = true) := by
  match hb : dd.befehl with
  | .movImm64 dst v =>
    have hzg := zugriff_movImm64 dd s dst v hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .movReg64 dst src =>
    have hzg := zugriff_movReg64 dd s dst src hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .addReg64 dst src =>
    have hzg := zugriff_addReg64 dd s dst src hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .subReg64 dst src =>
    have hzg := zugriff_subReg64 dd s dst src hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .xorReg64 dst src =>
    have hzg := zugriff_xorReg64 dd s dst src hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .cmpReg64 lhs rhs =>
    have hzg := zugriff_cmpReg64 dd s lhs rhs hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .load64 dst base disp =>
    have hzg := zugriff_load64 dd s dst base disp hb
    have hles : (zugriff dd s).lesen = Fuss (effAddr s base disp) := by rw [hzg]
    have hleer : (zugriff dd s).schreiben = [] := by rw [hzg]
    match hrd : read64 s.speicher (effAddr s base disp) with
    | none =>
      have hnone : schritt dd s = none :=
        schritt_load64_verweigert dd s dst base disp hok hb hrd
      rw [hnone] at hstep
      cases hstep
    | some v =>
      have h8 : lesbar8 s.speicher (effAddr s base disp) = true :=
        read64_braucht_lesbar _ _ v hrd
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hles] at hx
        exact lesbar8_gibt_byte _ _ _ h8 hx
      · rw [hleer] at hx
        simp at hx
  | .store64 base src disp =>
    have hzg := zugriff_store64 dd s base src disp hb
    have hleer : (zugriff dd s).lesen = [] := by rw [hzg]
    have hschr : (zugriff dd s).schreiben = Fuss (effAddr s base disp) := by
      rw [hzg]
    match hwr : write64 s.speicher (effAddr s base disp) (s.register src) with
    | none =>
      have hnone : schritt dd s = none :=
        schritt_store64_verweigert dd s base src disp hok hb hwr
      rw [hnone] at hstep
      cases hstep
    | some m =>
      have h8 : schreibbar8 s.speicher (effAddr s base disp) = true :=
        write64_braucht_schreibbar _ _ _ m hwr
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hleer] at hx
        simp at hx
      · rw [hschr] at hx
        exact schreibbar8_gibt_byte _ _ _ h8 hx
  | .jump32 disp =>
    have hzg := zugriff_jump32 dd s disp hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .jumpIf32 cond disp =>
    have hzg := zugriff_jumpIf32 dd s cond disp hb
    exact ⟨fun x hx => by simp [hzg] at hx, fun x hx => by simp [hzg] at hx⟩
  | .push64 src =>
    have hzg := zugriff_push64 dd s src hb
    have hleer : (zugriff dd s).lesen = [] := by rw [hzg]
    have hschr : (zugriff dd s).schreiben = Fuss (stapelOben s) := by rw [hzg]
    match hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (s.register src) with
    | none =>
      have hnone : schritt dd s = none :=
        schritt_push64_verweigert dd s src hok hb hwr
      rw [hnone] at hstep
      cases hstep
    | some m =>
      have h8 : schreibbar8 s.speicher (stapelOben s) = true := by
        have h8' : schreibbar8 s.speicher
            (s.register Register.rsp - BitVec.ofNat 64 8) = true :=
          write64_braucht_schreibbar _ _ _ m hwr
        simpa [stapelOben] using h8'
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hleer] at hx
        simp at hx
      · rw [hschr] at hx
        exact schreibbar8_gibt_byte _ _ _ h8 hx
  | .pop64 dst =>
    have hzg := zugriff_pop64 dd s dst hb
    have hles : (zugriff dd s).lesen = Fuss (s.register Register.rsp) := by
      rw [hzg]
    have hleer : (zugriff dd s).schreiben = [] := by rw [hzg]
    match hrd : read64 s.speicher (s.register Register.rsp) with
    | none =>
      have hnone : schritt dd s = none :=
        schritt_pop64_verweigert dd s dst hok hb hrd
      rw [hnone] at hstep
      cases hstep
    | some v =>
      have h8 : lesbar8 s.speicher (s.register Register.rsp) = true :=
        read64_braucht_lesbar _ _ v hrd
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hles] at hx
        exact lesbar8_gibt_byte _ _ _ h8 hx
      · rw [hleer] at hx
        simp at hx
  | .call32 disp =>
    have hzg := zugriff_call32 dd s disp hb
    have hleer : (zugriff dd s).lesen = [] := by rw [hzg]
    have hschr : (zugriff dd s).schreiben = Fuss (stapelOben s) := by rw [hzg]
    match hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip dd.laenge) with
    | none =>
      have hnone : schritt dd s = none :=
        schritt_call32_verweigert dd s disp hok hb hwr
      rw [hnone] at hstep
      cases hstep
    | some m =>
      have h8 : schreibbar8 s.speicher (stapelOben s) = true := by
        have h8' : schreibbar8 s.speicher
            (s.register Register.rsp - BitVec.ofNat 64 8) = true :=
          write64_braucht_schreibbar _ _ _ m hwr
        simpa [stapelOben] using h8'
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hleer] at hx
        simp at hx
      · rw [hschr] at hx
        exact schreibbar8_gibt_byte _ _ _ h8 hx
  | .ret =>
    have hzg := zugriff_ret dd s hb
    have hles : (zugriff dd s).lesen = Fuss (s.register Register.rsp) := by
      rw [hzg]
    have hleer : (zugriff dd s).schreiben = [] := by rw [hzg]
    match hrd : read64 s.speicher (s.register Register.rsp) with
    | none =>
      have hnone : schritt dd s = none :=
        schritt_ret_verweigert dd s hok hb hrd
      rw [hnone] at hstep
      cases hstep
    | some v =>
      have h8 : lesbar8 s.speicher (s.register Register.rsp) = true :=
        read64_braucht_lesbar _ _ v hrd
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hles] at hx
        exact lesbar8_gibt_byte _ _ _ h8 hx
      · rw [hleer] at hx
        simp at hx

/-! ## 3. Refusal: one denied footprint byte admits no step. -/

/-- REFUSAL: where one footprint byte lacks its permission, the
    instruction has no transition: the denied byte fails the eight-byte
    check (contrapositives above), the checked access returns `none`
    (`read64_aus_lesbar_falsch`, the accepted `write64_verweigert`), and
    the accepted `schritt_*_verweigert` refusal applies. Pure forms have
    empty footprints, so the permission failure is contradictory there. -/
theorem schritt_versagt_ohne_perm (dd : Decodiert) (s : Zustand)
    (hok : laengeOk dd.laenge = true)
    (hperm : (∃ x, x ∈ (zugriff dd s).lesen ∧ s.speicher.lesbar x = false) ∨
             (∃ x, x ∈ (zugriff dd s).schreiben ∧
               s.speicher.schreibbar x = false)) :
    schritt dd s = none := by
  match hb : dd.befehl with
  | .movImm64 dst v =>
    have hzg := zugriff_movImm64 dd s dst v hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .movReg64 dst src =>
    have hzg := zugriff_movReg64 dd s dst src hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .addReg64 dst src =>
    have hzg := zugriff_addReg64 dd s dst src hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .subReg64 dst src =>
    have hzg := zugriff_subReg64 dd s dst src hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .xorReg64 dst src =>
    have hzg := zugriff_xorReg64 dd s dst src hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .cmpReg64 lhs rhs =>
    have hzg := zugriff_cmpReg64 dd s lhs rhs hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .load64 dst base disp =>
    have hzg := zugriff_load64 dd s dst base disp hb
    have hles : (zugriff dd s).lesen = Fuss (effAddr s base disp) := by rw [hzg]
    have hleer : (zugriff dd s).schreiben = [] := by rw [hzg]
    have hnone : read64 s.speicher (effAddr s base disp) = none := by
      rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩
      · rw [hles] at hx
        have h8 : lesbar8 s.speicher (effAddr s base disp) = false :=
          lesbar8_aus_byte_falsch _ _ _ hx hbad
        exact read64_aus_lesbar_falsch _ _ h8
      · rw [hleer] at hx
        simp at hx
    exact schritt_load64_verweigert dd s dst base disp hok hb hnone
  | .store64 base src disp =>
    have hzg := zugriff_store64 dd s base src disp hb
    have hleer : (zugriff dd s).lesen = [] := by rw [hzg]
    have hschr : (zugriff dd s).schreiben = Fuss (effAddr s base disp) := by
      rw [hzg]
    have hnone : write64 s.speicher (effAddr s base disp) (s.register src) =
        none := by
      rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩
      · rw [hleer] at hx
        simp at hx
      · rw [hschr] at hx
        have h8 : schreibbar8 s.speicher (effAddr s base disp) = false :=
          schreibbar8_aus_byte_falsch _ _ _ hx hbad
        exact write64_verweigert _ _ _ h8
    exact schritt_store64_verweigert dd s base src disp hok hb hnone
  | .jump32 disp =>
    have hzg := zugriff_jump32 dd s disp hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .jumpIf32 cond disp =>
    have hzg := zugriff_jumpIf32 dd s cond disp hb
    rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩ <;> simp [hzg] at hx
  | .push64 src =>
    have hzg := zugriff_push64 dd s src hb
    have hleer : (zugriff dd s).lesen = [] := by rw [hzg]
    have hschr : (zugriff dd s).schreiben = Fuss (stapelOben s) := by rw [hzg]
    have hnone : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (s.register src) = none := by
      rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩
      · rw [hleer] at hx
        simp at hx
      · rw [hschr] at hx
        have h8 : schreibbar8 s.speicher (stapelOben s) = false :=
          schreibbar8_aus_byte_falsch _ _ _ hx hbad
        have h8' : schreibbar8 s.speicher
            (s.register Register.rsp - BitVec.ofNat 64 8) = false := by
          simpa [stapelOben] using h8
        exact write64_verweigert _ _ _ h8'
    exact schritt_push64_verweigert dd s src hok hb hnone
  | .pop64 dst =>
    have hzg := zugriff_pop64 dd s dst hb
    have hles : (zugriff dd s).lesen = Fuss (s.register Register.rsp) := by
      rw [hzg]
    have hleer : (zugriff dd s).schreiben = [] := by rw [hzg]
    have hnone : read64 s.speicher (s.register Register.rsp) = none := by
      rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩
      · rw [hles] at hx
        have h8 : lesbar8 s.speicher (s.register Register.rsp) = false :=
          lesbar8_aus_byte_falsch _ _ _ hx hbad
        exact read64_aus_lesbar_falsch _ _ h8
      · rw [hleer] at hx
        simp at hx
    exact schritt_pop64_verweigert dd s dst hok hb hnone
  | .call32 disp =>
    have hzg := zugriff_call32 dd s disp hb
    have hleer : (zugriff dd s).lesen = [] := by rw [hzg]
    have hschr : (zugriff dd s).schreiben = Fuss (stapelOben s) := by rw [hzg]
    have hnone : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip dd.laenge) = none := by
      rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩
      · rw [hleer] at hx
        simp at hx
      · rw [hschr] at hx
        have h8 : schreibbar8 s.speicher (stapelOben s) = false :=
          schreibbar8_aus_byte_falsch _ _ _ hx hbad
        have h8' : schreibbar8 s.speicher
            (s.register Register.rsp - BitVec.ofNat 64 8) = false := by
          simpa [stapelOben] using h8
        exact write64_verweigert _ _ _ h8'
    exact schritt_call32_verweigert dd s disp hok hb hnone
  | .ret =>
    have hzg := zugriff_ret dd s hb
    have hles : (zugriff dd s).lesen = Fuss (s.register Register.rsp) := by
      rw [hzg]
    have hleer : (zugriff dd s).schreiben = [] := by rw [hzg]
    have hnone : read64 s.speicher (s.register Register.rsp) = none := by
      rcases hperm with ⟨x, hx, hbad⟩ | ⟨x, hx, hbad⟩
      · rw [hles] at hx
        have h8 : lesbar8 s.speicher (s.register Register.rsp) = false :=
          lesbar8_aus_byte_falsch _ _ _ hx hbad
        exact read64_aus_lesbar_falsch _ _ h8
      · rw [hleer] at hx
        simp at hx
    exact schritt_ret_verweigert dd s hok hb hnone

/-! ## 4. The permission-check closing through `byteschritt`. -/

/-- PERMISSION-CHECK CLOSING, generic over arbitrary admitted inputs: every
    realised byte step went through checked permissions (fetch prefix
    executable plus every footprint byte permission-checked, with the
    fetched instruction that ran), and any footprint permission failure
    on a fetched instruction refuses the byte step. Composes the accepted
    byte-step decomposition (`byte_aus_weiter`), the accepted
    fetch-to-decoder facts (`fetchDekodiert_entspricht`) and the two
    directions above; the closing step is execution (`byteschritt`), never
    a conjunction of checks. -/
theorem ComposePermCheck_verbindung (s : Zustand) :
    (∀ s', byteschritt s = .weiter s' →
      ∃ d rest, fetchDekodiert s = some (d, rest) ∧
        ausfuehrbarN s.speicher s.rip d.laenge = true ∧
        (∀ x, x ∈ (zugriff d s).lesen → s.speicher.lesbar x = true) ∧
        (∀ x, x ∈ (zugriff d s).schreiben → s.speicher.schreibbar x = true) ∧
        schritt d s = some s') ∧
    (∀ d rest, fetchDekodiert s = some (d, rest) →
      ((∃ x, x ∈ (zugriff d s).lesen ∧ s.speicher.lesbar x = false) ∨
       (∃ x, x ∈ (zugriff d s).schreiben ∧
         s.speicher.schreibbar x = false)) →
      byteschritt s = .verweigert) := by
  refine ⟨?_, ?_⟩
  · intro s' hs
    obtain ⟨d, rest, hf, hstep⟩ := byte_aus_weiter s s' hs
    obtain ⟨_, _, hok, hexe⟩ := fetchDekodiert_entspricht s d rest hf
    obtain ⟨hles, hschr⟩ := zugriff_perm_aus_schritt d s s' hok hstep
    exact ⟨d, rest, hf, hexe, hles, hschr, hstep⟩
  · intro d rest hf hperm
    obtain ⟨_, _, hok, _⟩ := fetchDekodiert_entspricht s d rest hf
    have hnone := schritt_versagt_ohne_perm d s hok hperm
    exact byteschritt_verweigert_ohne_schritt s d rest hf hnone

/-! ## 5. Witness states: one store, permission bit governs. -/

/-- Witness decoded store: `store [rbx], rax`, seven bytes. -/
def permStoreDec : Decodiert :=
  { befehl := Befehl.store64 Register.rbx Register.rax (BitVec.ofNat 32 0),
    laenge := 7 }

/-- The fetch suffix behind the seven store bytes in a 15-byte window. -/
def permStoreRest : List Byte := List.replicate 8 (BitVec.ofNat 8 0)

/-- Witness registers: `rbx` names the data cell, `rax` holds 7. -/
def permStoreReg : Register → Wort := fun q =>
  if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rax then BitVec.ofNat 64 7
  else BitVec.ofNat 64 0

/-- Witness store bytes at 4096: the accepted `store [rbx], rax` encoding. -/
def permStoreBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 72
  else if a.toNat = 4097 then natByte 137
  else if a.toNat = 4098 then natByte 131
  else if a.toNat = 4099 then natByte 0
  else if a.toNat = 4100 then natByte 0
  else if a.toNat = 4101 then natByte 0
  else if a.toNat = 4102 then natByte 0
  else BitVec.ofNat 8 0

/-- Allowed state: store bytes executable, data cell readable/writable. -/
def permStoreErlaubt : Zustand :=
  { register := permStoreReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher :=
      { bytes := permStoreBytes
        lesbar := ketteDaten
        schreibbar := ketteDaten
        ausfuehrbar := ketteExec } }

/-- Denied state: identical bytes and registers, write permission denied. -/
def permSchreibVerweigertStart : Zustand :=
  { permStoreErlaubt with
    speicher := { permStoreErlaubt.speicher with
      schreibbar := fun _ => false } }

/-- FETCH PINNING (allowed): the window decodes to the store with the
    zero suffix; fetch checks data permissions never. -/
theorem perm_fetch_store :
    fetchDekodiert permStoreErlaubt = some (permStoreDec, permStoreRest) := by
  decide

/-- FETCH PINNING (denied): the same bytes decode identically; the write
    denial changes no fetch byte. -/
theorem perm_fetch_store_verweigert :
    fetchDekodiert permSchreibVerweigertStart =
      some (permStoreDec, permStoreRest) := by
  decide

/-- POSITIVE: with write permission the store step changes byte 8192
    from zero to 7 through the composed closing step. -/
theorem perm_schreib_erlaubt_schreitet :
    ausgangByte (BitVec.ofNat 64 8192) (byteschritt permStoreErlaubt) =
      some (natByte 7) ∧
    permStoreErlaubt.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 := by
  decide

/-- PLANTED DATA REFUSAL (observation): denying only the write bit leaves
    no next address: the fetched store has no transition. -/
theorem perm_schreib_verweigert_rip :
    ausgangRip (byteschritt permSchreibVerweigertStart) = none := by
  decide

/-- PLANTED DATA REFUSAL: denying only the write bit turns the same
    fetched store into no transition. -/
theorem perm_schreib_verweigert :
    byteschritt permSchreibVerweigertStart = .verweigert := by
  match hb : byteschritt permSchreibVerweigertStart with
  | .weiter s' =>
    have h := perm_schreib_verweigert_rip
    rw [hb] at h
    have h2 : ausgangRip (ByteAusgang.weiter s') = some s'.rip := rfl
    rw [h2] at h
    cases h
  | .verweigert => rfl

/-! ## 6. Joint witness: checked store run plus planted refusals. -/

/-- JOINT WITNESS for `ComposePermCheck_verbindung`: all premises hold
    jointly on one non-degenerate store state (executable code apart from
    readable/writable data): the success direction with the pinned store
    footprint (eight bytes at 8192, observably changed zero to 7), the
    refusal direction through the closing on the write-denied twin, and
    the execute-denied refusal. -/
theorem ComposePermCheck_verbindung_zeuge :
    (∃ d rest s', fetchDekodiert permStoreErlaubt = some (d, rest) ∧
      ausfuehrbarN permStoreErlaubt.speicher permStoreErlaubt.rip d.laenge =
        true ∧
      (zugriff d permStoreErlaubt).schreiben = Fuss (BitVec.ofNat 64 8192) ∧
      (∀ x, x ∈ (zugriff d permStoreErlaubt).lesen →
        permStoreErlaubt.speicher.lesbar x = true) ∧
      (∀ x, x ∈ (zugriff d permStoreErlaubt).schreiben →
        permStoreErlaubt.speicher.schreibbar x = true) ∧
      schritt d permStoreErlaubt = some s' ∧
      s'.speicher.bytes (BitVec.ofNat 64 8192) = natByte 7) ∧
    permStoreErlaubt.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 ∧
    (∃ d rest, fetchDekodiert permSchreibVerweigertStart = some (d, rest) ∧
      ((∃ x, x ∈ (zugriff d permSchreibVerweigertStart).lesen ∧
          permSchreibVerweigertStart.speicher.lesbar x = false) ∨
       (∃ x, x ∈ (zugriff d permSchreibVerweigertStart).schreiben ∧
          permSchreibVerweigertStart.speicher.schreibbar x = false)) ∧
      byteschritt permSchreibVerweigertStart = .verweigert) ∧
    byteschritt ohneExecStart = .verweigert := by
  have hsucc : ∃ s', byteschritt permStoreErlaubt = .weiter s' := by
    match hb : byteschritt permStoreErlaubt with
    | .weiter s' => exact ⟨s', rfl⟩
    | .verweigert =>
      have h := perm_schreib_erlaubt_schreitet
      rw [hb] at h
      simp [ausgangByte] at h
  obtain ⟨s', hs'⟩ := hsucc
  obtain ⟨d, rest, hf, hexe, hles, hschr, hstep⟩ :=
    (ComposePermCheck_verbindung permStoreErlaubt).1 s' hs'
  have hpin : permStoreDec = d := by
    have heq := perm_fetch_store.symm.trans hf
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    exact heq.1
  subst hpin
  have hfuss : (zugriff permStoreDec permStoreErlaubt).schreiben =
      Fuss (BitVec.ofNat 64 8192) := by
    decide
  have hbyte : s'.speicher.bytes (BitVec.ofNat 64 8192) = natByte 7 := by
    have h := perm_schreib_erlaubt_schreitet
    rw [hs'] at h
    simpa [ausgangByte] using h.1
  have hperm : (∃ x, x ∈ (zugriff permStoreDec permSchreibVerweigertStart).lesen ∧
        permSchreibVerweigertStart.speicher.lesbar x = false) ∨
      (∃ x, x ∈ (zugriff permStoreDec permSchreibVerweigertStart).schreiben ∧
        permSchreibVerweigertStart.speicher.schreibbar x = false) := by
    right
    have hschr : (zugriff permStoreDec permSchreibVerweigertStart).schreiben =
        Fuss (BitVec.ofNat 64 8192) := by
      decide
    refine ⟨BitVec.ofNat 64 8192, ?_, rfl⟩
    rw [hschr, fuss_mem]
    exact ⟨0, by omega, addrOff_null _⟩
  have href := (ComposePermCheck_verbindung permSchreibVerweigertStart).2
    permStoreDec permStoreRest perm_fetch_store_verweigert hperm
  have hOhne : byteschritt ohneExecStart = .verweigert := by
    match hb : byteschritt ohneExecStart with
    | .weiter s' =>
      have h := ohne_exec_verweigert
      rw [hb] at h
      have h2 : ausgangRip (ByteAusgang.weiter s') = some s'.rip := rfl
      rw [h2] at h
      cases h.1
    | .verweigert => rfl
  exact ⟨⟨permStoreDec, rest, s', hf, hexe, hfuss, hles, hschr, hstep, hbyte⟩,
    perm_schreib_erlaubt_schreitet.2,
    ⟨permStoreDec, permStoreRest, perm_fetch_store_verweigert, hperm, href⟩,
    hOhne⟩

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second loader/decoder/executor/ISA): the checked
    bundle `PermGeprueft` (consumed fetch prefix executable plus every
    footprint byte permission-checked); the byte bridge (`lesbar8_gibt_byte`,
    `schreibbar8_gibt_byte` and their contrapositives,
    `read64_aus_lesbar_falsch` mirroring the accepted `write64_verweigert`);
    the success direction over all 14 pilot forms
    (`zugriff_perm_aus_schritt`: realised reads went through `read64`,
    realised writes through `write64`, pure forms touch no byte); the
    refusal direction (`schritt_versagt_ohne_perm`: one denied footprint
    byte admits no transition); the closing through the existing
    `byteschritt` (`ComposePermCheck_verbindung`, both directions); and
    the joint non-degenerate witness with a reached memory-changing store
    run plus planted data and execute refusals
    (`ComposePermCheck_verbindung_zeuge`).
    NOT proved here, and not claimed:
    - No extended-ISA closing: narrow, multiply/divide, shift, SETcc/CMOVcc,
      scalar FP, packed-integer, LOCK/RMW/fence forms have no `zugriff`
      extraction; their per-access permission legs stay with their owners
      (extension codec lanes, lane 568 follow-ups).
    - No TSO/W/GX bridge: footprints stay byte sets; per-access
      linearisation, visibility and tearing stay OPEN.
    - No source correspondence, no image coverage beyond the fetched window,
      no entry/ABI/relocation/cost claim; `verweigert` is the absence of a
      transition, never a termination claim.
-/

#print axioms PermGeprueft
#print axioms lesbar8_gibt_byte
#print axioms schreibbar8_gibt_byte
#print axioms lesbar8_aus_byte_falsch
#print axioms schreibbar8_aus_byte_falsch
#print axioms read64_aus_lesbar_falsch
#print axioms zugriff_perm_aus_schritt
#print axioms schritt_versagt_ohne_perm
#print axioms ComposePermCheck_verbindung
#print axioms ComposePermCheck_verbindung_zeuge
#print axioms perm_fetch_store
#print axioms perm_fetch_store_verweigert
#print axioms perm_schreib_erlaubt_schreitet
#print axioms perm_schreib_verweigert_rip
#print axioms perm_schreib_verweigert

end Gabbro.Grammatik.X86
