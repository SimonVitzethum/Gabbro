/-
  File:      Grammatik/X86/Zugriffe.lean
  Subject:   Single owner for single-instruction target access footprints.

  Lane 317 (wave A, Lean-first): ONE generic reusable extraction from the
  actual canonical `Befehl` plus the pre-state, reusing `effAddr`, the stack
  addresses, `ripNach` and the byte footprints (`Fuss`) of `Speicher.lean`.
  Covers all 14 pilot constructors of `Ausfuehrung.lean` with read/write
  distinctions and stored words (CALL pushes the actual next RIP; PUSH reads
  the old RSP; POP/RET read the old stack address). No new ISA, no alternate
  evaluator, no fetch footprint (lane 319), no source rule.

  The extraction is a CHECKED POTENTIAL footprint: it is computed from the
  pre-state alone, without checking permissions or the decode length. It
  becomes a REALISED SUCCESSFUL footprint exactly when `schritt d s`
  succeeds; bad length or failed permission gives `schritt d s = none`,
  never a claimed successful trace. The eight addresses of a `Fuss` are a
  byte set, not one atomic multi-byte event and not a hardware
  interleaving trace; byte order inside a word, TSO visibility, grouping
  and any W/GX simulation stay OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- Single-instruction memory access: read footprint, write footprint and
    the stored word (present exactly for the three writing forms). -/
structure Zugriff where
  lesen : List Adresse
  schreiben : List Adresse
  speicherWert : Option Wort
  deriving DecidableEq, Repr

/-- Stack address a push or call writes: eight bytes below the old top. -/
def stapelOben (s : Zustand) : Adresse :=
  s.register Register.rsp - BitVec.ofNat 64 8

/-- THE single extraction: potential read/write footprints plus the stored
    word, from the canonical instruction and the pre-state. -/
def zugriff (d : Decodiert) (s : Zustand) : Zugriff :=
  match d.befehl with
  | .movImm64 _ _ => ⟨[], [], none⟩
  | .movReg64 _ _ => ⟨[], [], none⟩
  | .addReg64 _ _ => ⟨[], [], none⟩
  | .subReg64 _ _ => ⟨[], [], none⟩
  | .xorReg64 _ _ => ⟨[], [], none⟩
  | .cmpReg64 _ _ => ⟨[], [], none⟩
  | .load64 _ base disp => ⟨Fuss (effAddr s base disp), [], none⟩
  | .store64 base src disp =>
    ⟨[], Fuss (effAddr s base disp), some (s.register src)⟩
  | .jump32 _ => ⟨[], [], none⟩
  | .jumpIf32 _ _ => ⟨[], [], none⟩
  | .push64 src => ⟨[], Fuss (stapelOben s), some (s.register src)⟩
  | .pop64 _ => ⟨Fuss (s.register Register.rsp), [], none⟩
  | .call32 _ => ⟨[], Fuss (stapelOben s), some (ripNach s.rip d.laenge)⟩
  | .ret => ⟨Fuss (s.register Register.rsp), [], none⟩

/-! ## 1. Per-constructor footprint equations (all 14 pilot forms). -/

/-- Pure forms expose no memory footprint. -/
theorem zugriff_movImm64 (d : Decodiert) (s : Zustand) (dst : Register)
    (v : Wort) (h : d.befehl = .movImm64 dst v) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- Register move exposes no memory footprint. -/
theorem zugriff_movReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (h : d.befehl = .movReg64 dst src) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- Integer ALU forms expose no memory footprint. -/
theorem zugriff_addReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (h : d.befehl = .addReg64 dst src) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `sub` exposes no memory footprint. -/
theorem zugriff_subReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (h : d.befehl = .subReg64 dst src) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `xor` exposes no memory footprint. -/
theorem zugriff_xorReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (h : d.befehl = .xorReg64 dst src) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `cmp` exposes no memory footprint. -/
theorem zugriff_cmpReg64 (d : Decodiert) (s : Zustand) (lhs rhs : Register)
    (h : d.befehl = .cmpReg64 lhs rhs) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `load` reads the eight bytes at base plus displacement, writes none. -/
theorem zugriff_load64 (d : Decodiert) (s : Zustand) (dst base : Register)
    (disp : BitVec 32) (h : d.befehl = .load64 dst base disp) :
    zugriff d s = ⟨Fuss (effAddr s base disp), [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `store` writes the eight bytes at base plus displacement, reads none;
    the stored word is the source register. -/
theorem zugriff_store64 (d : Decodiert) (s : Zustand)
    (base src : Register) (disp : BitVec 32)
    (h : d.befehl = .store64 base src disp) :
    zugriff d s = ⟨[], Fuss (effAddr s base disp), some (s.register src)⟩ := by
  unfold zugriff
  rw [h]

/-- Unconditional jump exposes no memory footprint. -/
theorem zugriff_jump32 (d : Decodiert) (s : Zustand) (disp : BitVec 32)
    (h : d.befehl = .jump32 disp) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- Conditional jump exposes no memory footprint. -/
theorem zugriff_jumpIf32 (d : Decodiert) (s : Zustand) (cond : Bedingung)
    (disp : BitVec 32) (h : d.befehl = .jumpIf32 cond disp) :
    zugriff d s = ⟨[], [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `push` writes eight bytes below the OLD top; the stored word is the
    source register read before the move. -/
theorem zugriff_push64 (d : Decodiert) (s : Zustand) (src : Register)
    (h : d.befehl = .push64 src) :
    zugriff d s = ⟨[], Fuss (stapelOben s), some (s.register src)⟩ := by
  unfold zugriff
  rw [h]

/-- `pop` reads the eight bytes at the OLD stack address, writes none. -/
theorem zugriff_pop64 (d : Decodiert) (s : Zustand) (dst : Register)
    (h : d.befehl = .pop64 dst) :
    zugriff d s = ⟨Fuss (s.register Register.rsp), [], none⟩ := by
  unfold zugriff
  rw [h]

/-- `call` writes eight bytes below the OLD top; the stored word is the
    ACTUAL next RIP (post-decode address of this instruction). -/
theorem zugriff_call32 (d : Decodiert) (s : Zustand) (disp : BitVec 32)
    (h : d.befehl = .call32 disp) :
    zugriff d s =
      ⟨[], Fuss (stapelOben s), some (ripNach s.rip d.laenge)⟩ := by
  unfold zugriff
  rw [h]

/-- `ret` reads the eight bytes at the OLD stack address, writes none. -/
theorem zugriff_ret (d : Decodiert) (s : Zustand)
    (h : d.befehl = .ret) :
    zugriff d s = ⟨Fuss (s.register Register.rsp), [], none⟩ := by
  unfold zugriff
  rw [h]

/-! ## 2. Footprint membership as an explicit byte set. -/

/-- Membership in an eight-byte footprint is an explicit byte condition. -/
theorem fuss_mem (a x : Adresse) :
    x ∈ Fuss a ↔ ∃ k, k < 8 ∧ addrOff a k = x := by
  rw [← leseEreignisse_acht]
  exact leseEreignisse_mem a x 8

/-! ## 3. Pure forms: successful steps mutate no memory, footprint empty. -/

/-- `mov` immediate success writes no byte; the footprint is empty. -/
theorem erfolg_movImm64_ohne_speicher (s s' : Zustand)
    (dst : Register) (v : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .movImm64 dst v)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_movImm64_speicher dd s s' dst v hok h hstep,
    zugriff_movImm64 dd s dst v h⟩

/-- Register `mov` success writes no byte; the footprint is empty. -/
theorem erfolg_movReg64_ohne_speicher (s s' : Zustand)
    (dst src : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .movReg64 dst src)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_movReg64_speicher dd s s' dst src hok h hstep,
    zugriff_movReg64 dd s dst src h⟩

/-- `add` success writes no byte; the footprint is empty. -/
theorem erfolg_addReg64_ohne_speicher (s s' : Zustand)
    (dst src : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .addReg64 dst src)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_addReg64_speicher dd s s' dst src hok h hstep,
    zugriff_addReg64 dd s dst src h⟩

/-- `sub` success writes no byte; the footprint is empty. -/
theorem erfolg_subReg64_ohne_speicher (s s' : Zustand)
    (dst src : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .subReg64 dst src)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_subReg64_speicher dd s s' dst src hok h hstep,
    zugriff_subReg64 dd s dst src h⟩

/-- `xor` success writes no byte; the footprint is empty. -/
theorem erfolg_xorReg64_ohne_speicher (s s' : Zustand)
    (dst src : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .xorReg64 dst src)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_xorReg64_speicher dd s s' dst src hok h hstep,
    zugriff_xorReg64 dd s dst src h⟩

/-- `cmp` success writes no byte; the footprint is empty. -/
theorem erfolg_cmpReg64_ohne_speicher (s s' : Zustand)
    (lhs rhs : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .cmpReg64 lhs rhs)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_cmpReg64_speicher dd s s' lhs rhs hok h hstep,
    zugriff_cmpReg64 dd s lhs rhs h⟩

/-- Unconditional-jump success writes no byte; the footprint is empty. -/
theorem erfolg_jump32_ohne_speicher (s s' : Zustand)
    (disp : BitVec 32) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .jump32 disp)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_jump32_speicher dd s s' disp hok h hstep,
    zugriff_jump32 dd s disp h⟩

/-! ## 4. Read forms: successful steps mutate no memory. -/

/-- Taken conditional-jump success writes no byte; footprint empty. -/
theorem erfolg_jumpIfGenommen_ohne_speicher (s s' : Zustand)
    (cond : Bedingung) (disp : BitVec 32) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = true)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_jumpIf32_genommen_speicher dd s s' cond disp hok h hbed hstep,
    zugriff_jumpIf32 dd s cond disp h⟩

/-- Untaken conditional-jump success writes no byte; footprint empty. -/
theorem erfolg_jumpIfNicht_ohne_speicher (s s' : Zustand)
    (cond : Bedingung) (disp : BitVec 32) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = false)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧ zugriff dd s = ⟨[], [], none⟩ := by
  exact ⟨schritt_jumpIf32_nicht_speicher dd s s' cond disp hok h hbed hstep,
    zugriff_jumpIf32 dd s cond disp h⟩

/-- `load` success writes no byte; the read footprint names the address. -/
theorem erfolg_load64_ohne_speicher (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32) (v : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = some v)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧
      zugriff dd s = ⟨Fuss (effAddr s base disp), [], none⟩ := by
  exact ⟨schritt_load64_speicher dd s s' dst base disp v hok h hrd hstep,
    zugriff_load64 dd s dst base disp h⟩

/-- `pop` success writes no byte; the read footprint is the old top. -/
theorem erfolg_pop64_ohne_speicher (s s' : Zustand)
    (dst : Register) (v : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .pop64 dst)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧
      zugriff dd s = ⟨Fuss (s.register Register.rsp), [], none⟩ := by
  exact ⟨schritt_pop64_speicher dd s s' dst v hok h hrd hstep,
    zugriff_pop64 dd s dst h⟩

/-- `ret` success writes no byte; the read footprint is the old top. -/
theorem erfolg_ret_ohne_speicher (s s' : Zustand)
    (ziel : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : schritt dd s = some s') :
    s'.speicher = s.speicher ∧
      zugriff dd s = ⟨Fuss (s.register Register.rsp), [], none⟩ := by
  exact ⟨schritt_ret_speicher dd s s' ziel hok h hrd hstep,
    zugriff_ret dd s h⟩

/-! ## 5. Read linkage: extracted addresses meet the actual `read64`. -/

/-- A successful `load` read exactly the extracted footprint base, and the
    destination holds the value that read returned. -/
theorem zugriff_load64_liest (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32) (v : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = some v)
    (hstep : schritt dd s = some s') :
    read64 s.speicher ((zugriff dd s).lesen.getD 0 0) = some v ∧
      s'.register dst = v := by
  rw [zugriff_load64 dd s dst base disp h]
  simp only
  have hFuss : (Fuss (effAddr s base disp)).getD 0 0 =
      effAddr s base disp := by
    simp [Fuss, addrOff_null]
  rw [hFuss, hrd]
  refine ⟨rfl, ?_⟩
  rw [schritt_load64_erfolg dd s dst base disp v hok h hrd] at hstep
  cases hstep
  simp [schrittRegister, regSet]

/-- A successful `pop` read exactly the old stack address named by the
    extracted footprint, and the non-`rsp` destination holds that value. -/
theorem zugriff_pop64_liest (s s' : Zustand)
    (dst : Register) (v : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v)
    (hstep : schritt dd s = some s') :
    read64 s.speicher ((zugriff dd s).lesen.getD 0 0) = some v ∧
      s'.register dst = v := by
  rw [zugriff_pop64 dd s dst h]
  simp only
  have hFuss : (Fuss (s.register Register.rsp)).getD 0 0 =
      s.register Register.rsp := by
    simp [Fuss, addrOff_null]
  rw [hFuss, hrd]
  refine ⟨rfl, ?_⟩
  rw [schritt_pop64_reg dd s dst v hok h hdst hrd] at hstep
  cases hstep
  simp [schrittPopReg, regSet]

/-- A successful `ret` read exactly the old stack address named by the
    extracted footprint, and control reaches the value that read returned. -/
theorem zugriff_ret_liest (s s' : Zustand)
    (ziel : Wort) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : schritt dd s = some s') :
    read64 s.speicher ((zugriff dd s).lesen.getD 0 0) = some ziel ∧
      s'.rip = ziel := by
  rw [zugriff_ret dd s h]
  simp only
  have hFuss : (Fuss (s.register Register.rsp)).getD 0 0 =
      s.register Register.rsp := by
    simp [Fuss, addrOff_null]
  rw [hFuss, hrd]
  refine ⟨rfl, ?_⟩
  rw [schritt_ret_erfolg dd s ziel hok h hrd] at hstep
  cases hstep
  rfl

/-! ## 6. Write forms: changed bytes lie in the extracted footprint. -/

/-- `store` success: every changed byte lies in the extracted write
    footprint, permissions are preserved, and the stored word is the
    source register named by the extraction. -/
theorem erfolg_store64_im_fuss (s s' : Zustand)
    (base src : Register) (disp : BitVec 32) (m : Speicher)
    (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m)
    (hstep : schritt dd s = some s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    s'.speicher.lesbar = s.speicher.lesbar ∧
    s'.speicher.schreibbar = s.speicher.schreibbar ∧
    (zugriff dd s).speicherWert = some (s.register src) := by
  rw [zugriff_store64 dd s base src disp h]
  simp only
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro x hx
    by_cases hm : x ∈ Fuss (effAddr s base disp)
    · exact hm
    · rw [fuss_mem] at hm
      have haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (effAddr s base disp) k :=
        fun k hk heq => hm ⟨k, hk, heq.symm⟩
      have hframe := schritt_store64_rahmen dd s s' base src disp m x
        hok h hwr hstep haussen
      exact absurd hframe hx
  · exact (schritt_store64_berechtigungen dd s s' base src disp m
      hok h hwr hstep).1
  · exact (schritt_store64_berechtigungen dd s s' base src disp m
      hok h hwr hstep).2.1

/-- `push` success: every changed byte lies in the extracted write
    footprint below the old top, permissions are preserved, and the
    stored word is the source register read before the move. -/
theorem erfolg_push64_im_fuss (s s' : Zustand)
    (src : Register) (m : Speicher) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m)
    (hstep : schritt dd s = some s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    s'.speicher.lesbar = s.speicher.lesbar ∧
    s'.speicher.schreibbar = s.speicher.schreibbar ∧
    (zugriff dd s).speicherWert = some (s.register src) := by
  rw [zugriff_push64 dd s src h]
  simp only
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro x hx
    by_cases hm : x ∈ Fuss (stapelOben s)
    · exact hm
    · rw [fuss_mem] at hm
      unfold stapelOben at hm
      have haussen : ∀ k : Nat, k < 8 →
          x ≠ addrOff (s.register Register.rsp - BitVec.ofNat 64 8) k :=
        fun k hk heq => hm ⟨k, hk, heq.symm⟩
      have hframe := schritt_push64_rahmen dd s s' src m x
        hok h hwr hstep haussen
      exact absurd hframe hx
  · exact (schritt_push64_berechtigungen dd s s' src m
      hok h hwr hstep).1
  · exact (schritt_push64_berechtigungen dd s s' src m
      hok h hwr hstep).2.1

/-- `call` success: every changed byte lies in the extracted write
    footprint below the old top, permissions are preserved, and the
    stored word is the ACTUAL next RIP named by the extraction. -/
theorem erfolg_call32_im_fuss (s s' : Zustand)
    (disp : BitVec 32) (m : Speicher) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dd.laenge) = some m)
    (hstep : schritt dd s = some s') :
    (∀ x, s'.speicher.bytes x ≠ s.speicher.bytes x →
      x ∈ (zugriff dd s).schreiben) ∧
    s'.speicher.lesbar = s.speicher.lesbar ∧
    s'.speicher.schreibbar = s.speicher.schreibbar ∧
    (zugriff dd s).speicherWert = some (ripNach s.rip dd.laenge) := by
  rw [zugriff_call32 dd s disp h]
  simp only
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro x hx
    by_cases hm : x ∈ Fuss (stapelOben s)
    · exact hm
    · rw [fuss_mem] at hm
      unfold stapelOben at hm
      have haussen : ∀ k : Nat, k < 8 →
          x ≠ addrOff (s.register Register.rsp - BitVec.ofNat 64 8) k :=
        fun k hk heq => hm ⟨k, hk, heq.symm⟩
      have hframe := schritt_call32_rahmen dd s s' disp m x
        hok h hwr hstep haussen
      exact absurd hframe hx
  · exact (schritt_call32_berechtigungen dd s s' disp m
      hok h hwr hstep).1
  · exact (schritt_call32_berechtigungen dd s s' disp m
      hok h hwr hstep).2.1

/-! ## 7. Refusal: bad length or failed permission is never a trace. -/

/-- A bad decode length admits no successful step for any footprint. -/
theorem zugriff_laenge_versagt_kein_erfolg (s s' : Zustand) (dd : Decodiert)
    (h : laengeOk dd.laenge = false)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_laenge_verweigert dd s h] at hstep
  cases hstep

/-- A failed `load` read admits no successful step. -/
theorem zugriff_load64_versagt_kein_erfolg (s s' : Zustand)
    (dst base : Register) (disp : BitVec 32) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = none)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_load64_verweigert dd s dst base disp hok h hrd] at hstep
  cases hstep

/-- A failed `store` write admits no successful step. -/
theorem zugriff_store64_versagt_kein_erfolg (s s' : Zustand)
    (base src : Register) (disp : BitVec 32) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = none)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_store64_verweigert dd s base src disp hok h hwr] at hstep
  cases hstep

/-- A failed `push` write admits no successful step. -/
theorem zugriff_push64_versagt_kein_erfolg (s s' : Zustand)
    (src : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = none)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_push64_verweigert dd s src hok h hwr] at hstep
  cases hstep

/-- A failed `pop` read admits no successful step. -/
theorem zugriff_pop64_versagt_kein_erfolg (s s' : Zustand)
    (dst : Register) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .pop64 dst)
    (hrd : read64 s.speicher (s.register Register.rsp) = none)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_pop64_verweigert dd s dst hok h hrd] at hstep
  cases hstep

/-- A failed `call` write admits no successful step. -/
theorem zugriff_call32_versagt_kein_erfolg (s s' : Zustand)
    (disp : BitVec 32) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip dd.laenge) = none)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_call32_verweigert dd s disp hok h hwr] at hstep
  cases hstep

/-- A failed `ret` read admits no successful step. -/
theorem zugriff_ret_versagt_kein_erfolg (s s' : Zustand) (dd : Decodiert)
    (hok : laengeOk dd.laenge = true) (h : dd.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = none)
    (hstep : schritt dd s = some s') : False := by
  rw [schritt_ret_verweigert dd s hok h hrd] at hstep
  cases hstep

/-! ## 8. No atomicity, no interleaving trace.

    The eight addresses of a `Fuss` are a byte set shared with
    `Speicher.lean`'s per-byte events, not one atomic multi-byte event and
    not a completed hardware interleaving trace. Both stronger readings
    have no constructor below, so no extraction is one. Byte order inside
    a word, TSO visibility, grouping and any W/GX simulation stay OPEN. -/

/-- No extraction is one atomic multi-byte event: the type is empty. -/
inductive AtomarZugriff : Zugriff → Prop

/-- No extraction is one atomic multi-byte event. -/
theorem kein_atomarer_zugriff (z : Zugriff) : ¬ AtomarZugriff z := by
  intro h
  cases h

/-- No access list is a completed hardware interleaving trace. -/
inductive AblaufSpur : List Zugriff → Prop

/-- No access list is a completed hardware interleaving trace. -/
theorem keine_ablauf_spur (l : List Zugriff) : ¬ AblaufSpur l := by
  intro h
  cases h

/-- A `store` footprint is eight byte addresses, not one event. -/
theorem zugriff_store64_acht (s : Zustand)
    (base src : Register) (disp : BitVec 32) (dd : Decodiert)
    (h : dd.befehl = .store64 base src disp) :
    (zugriff dd s).schreiben.length = 8 := by
  rw [zugriff_store64 dd s base src disp h]
  simp [Fuss]

/-- A `push` footprint is eight byte addresses, not one event. -/
theorem zugriff_push64_acht (s : Zustand) (src : Register) (dd : Decodiert)
    (h : dd.befehl = .push64 src) :
    (zugriff dd s).schreiben.length = 8 := by
  rw [zugriff_push64 dd s src h]
  simp [Fuss]

/-- A `call` footprint is eight byte addresses, not one event. -/
theorem zugriff_call32_acht (s : Zustand) (disp : BitVec 32) (dd : Decodiert)
    (h : dd.befehl = .call32 disp) :
    (zugriff dd s).schreiben.length = 8 := by
  rw [zugriff_call32 dd s disp h]
  simp [Fuss]

/-- A `load` footprint is eight byte addresses, not one event. -/
theorem zugriff_load64_acht (s : Zustand)
    (dst base : Register) (disp : BitVec 32) (dd : Decodiert)
    (h : dd.befehl = .load64 dst base disp) :
    (zugriff dd s).lesen.length = 8 := by
  rw [zugriff_load64 dd s dst base disp h]
  simp [Fuss]

/-! ## 9. Reached store-changing witness and address probes. -/

/-- Witness program: set rax to 42, then store it through the stack pointer. -/
def zugriffZeugeProg : List Decodiert :=
  [{ befehl := Befehl.movImm64 Register.rax 42, laenge := 3 },
   { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 4 }]

/-- REACHED STORE-CHANGING WITNESS: the two-step run reaches a state whose
    byte at 8192 observably changed from zero to 42. -/
theorem zugriff_lauf_zeuge :
    ((lauf zugriffZeugeProg zeugeZustand).map
      (fun s' => s'.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (BitVec.ofNat 8 42)) ∧
    (zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0) := by
  decide

/-- The witness store's changed byte lies in the extracted footprint of
    that same store step, taken in its actual pre-state. -/
theorem zugriff_zeuge_im_fuss :
    (BitVec.ofNat 64 8192) ∈
      (zugriff { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 4 } { zeugeZustand with register := regSet zeugeReg Register.rax 42 }).schreiben := by
  decide

/-- PUSH probe: the extracted write base below the old top is 8184. -/
theorem probe_zugriff_schub :
    (zugriff { befehl := Befehl.push64 Register.rax, laenge := 1 }
      zeugeZustand).schreiben.getD 0 0 = BitVec.ofNat 64 8184 := by
  decide

/-- PUSH probe: the extracted stored word is the source register value. -/
theorem probe_zugriff_schub_wert :
    (zugriff { befehl := Befehl.push64 Register.rax, laenge := 1 } { zeugeZustand with register := regSet zeugeReg Register.rax 7 }).speicherWert =
      some (BitVec.ofNat 64 7) := by
  decide

/-- CALL probe: the extracted stored word is the ACTUAL next RIP 4101. -/
theorem probe_zugriff_ruf_wert :
    (zugriff { befehl := Befehl.call32 (BitVec.ofNat 32 32), laenge := 5 }
      zeugeZustand).speicherWert = some (BitVec.ofNat 64 4101) := by
  decide

/-- CALL probe: the extracted write base below the old top is 8184. -/
theorem probe_zugriff_ruf :
    (zugriff { befehl := Befehl.call32 (BitVec.ofNat 32 32), laenge := 5 }
      zeugeZustand).schreiben.getD 0 0 = BitVec.ofNat 64 8184 := by
  decide

/-- POP probe: the extracted read base is the OLD stack address 8192. -/
theorem probe_zugriff_nimm :
    (zugriff { befehl := Befehl.pop64 Register.rax, laenge := 1 }
      zeugeZustand).lesen.getD 0 0 = BitVec.ofNat 64 8192 := by
  decide

/- CUTS:
    - The extraction is a CHECKED POTENTIAL footprint from the pre-state
      (no permission or length check inside `zugriff`); it is a REALISED
      SUCCESSFUL footprint exactly when `schritt d s` succeeds (§3-§7).
    - No atomicity: `AtomarZugriff` is empty (`kein_atomarer_zugriff`); the
      eight `Fuss` addresses reuse the per-byte events of `Speicher.lean`
      and claim no single-copy-atomic multi-byte occurrence, no byte order
      beyond little-endian `wortByte`, no TSO visibility and no grouping.
    - No interleaving: `AblaufSpur` is empty (`keine_ablauf_spur`); `lauf`
      is the sequential fold of `Ausfuehrung.lean`, not a concurrent trace.
    - No RMW/LOCK/fence/narrow forms: `Befehl` has none, and none is
      admitted here; aligned-word observability and tearing stay OPEN.
    - No W/GX simulation, no per-access linearisation, no source, cost,
      contract, progress, timing, ABI/loader or whole-image claim.
    - No instruction-fetch footprint: owned by lane 319, not duplicated.
-/

#print axioms fuss_mem
#print axioms zugriff_movImm64
#print axioms zugriff_load64
#print axioms zugriff_store64
#print axioms zugriff_push64
#print axioms zugriff_pop64
#print axioms zugriff_call32
#print axioms zugriff_ret
#print axioms erfolg_movImm64_ohne_speicher
#print axioms erfolg_addReg64_ohne_speicher
#print axioms erfolg_cmpReg64_ohne_speicher
#print axioms erfolg_jump32_ohne_speicher
#print axioms erfolg_jumpIfGenommen_ohne_speicher
#print axioms erfolg_load64_ohne_speicher
#print axioms erfolg_pop64_ohne_speicher
#print axioms erfolg_ret_ohne_speicher
#print axioms zugriff_load64_liest
#print axioms zugriff_pop64_liest
#print axioms zugriff_ret_liest
#print axioms erfolg_store64_im_fuss
#print axioms erfolg_push64_im_fuss
#print axioms erfolg_call32_im_fuss
#print axioms zugriff_laenge_versagt_kein_erfolg
#print axioms zugriff_load64_versagt_kein_erfolg
#print axioms zugriff_store64_versagt_kein_erfolg
#print axioms zugriff_push64_versagt_kein_erfolg
#print axioms zugriff_pop64_versagt_kein_erfolg
#print axioms zugriff_call32_versagt_kein_erfolg
#print axioms zugriff_ret_versagt_kein_erfolg
#print axioms kein_atomarer_zugriff
#print axioms keine_ablauf_spur
#print axioms zugriff_store64_acht
#print axioms zugriff_push64_acht
#print axioms zugriff_call32_acht
#print axioms zugriff_load64_acht
#print axioms zugriff_lauf_zeuge
#print axioms zugriff_zeuge_im_fuss
#print axioms probe_zugriff_schub
#print axioms probe_zugriff_schub_wert
#print axioms probe_zugriff_ruf_wert
#print axioms probe_zugriff_ruf
#print axioms probe_zugriff_nimm

end Gabbro.Grammatik.X86
