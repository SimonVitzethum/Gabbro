/-
  Fetched call/return to stack-frame proofs (lane 569).

  Connects actual `Byteschritt` fetch/decode of canonical CALL/PUSH/POP/RET
  bytes to the accepted `Stapel` frame obligations, `CodeImmutability`
  fetch preservation and `StackUnwind` restoration/refusal results. No new
  transition, decoder, memory model or source claim is created here; every
  execution fact reuses the accepted `schritt`/`byteschritt` vocabulary.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.Stapel
import Grammatik.X86.CodeImmutability
import Grammatik.X86.StackUnwind

namespace Gabbro.Grammatik.X86

/-- The fetched window at `rip` is the canonical encoding of stack
    operation `b` followed by `suffix` bytes of actual executable memory. -/
def StapelGeholt (s : Zustand) (b : Befehl) (suffix : List Byte) : Prop :=
  geholt s = encode b ++ suffix

/-- FETCH FROM ACTUAL BYTES: a fetched window holding the canonical
    encoding of `b` decodes to `b` with its consumed length, through the
    round-trip instances. Both premises pin one runtime check. -/
theorem stapelGeholt_fetch (s : Zustand) (b : Befehl) (suffix : List Byte)
    (hwin : StapelGeholt s b suffix)
    (hexe : ausfuehrbarN s.speicher s.rip (encode b).length = true) :
    fetchDekodiert s = some (⟨b, (encode b).length⟩, suffix) :=
  (kanonisch_schritt_ueberein b s suffix hwin hexe).1

/-- FETCHED CALL: from actual call bytes, the byte step stores the correct
    next-RIP return word below the pre-state top and transfers control.
    The stored word is `ripNach` of the pre-state `rip`, never a
    hand-built address; the stack slot is the pre-state `rsp` minus 8. -/
theorem byteschritt_geholt_call (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte) (m : Speicher)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length) = some m) :
    byteschritt s = .weiter (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)) := by
  have hlen : laengeOk (encode (.call32 disp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hkan := kanonisch_schritt_ueberein (.call32 disp) s suffix hwin hexe
  obtain ⟨_, hbs⟩ := hkan
  have hs : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s =
      some (schrittCall s Register.rsp m
        (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length + dispWort disp)) :=
    schritt_call32_erfolg _ _ _ _ hlen rfl hwr
  rw [hs] at hbs
  exact hbs

/-- FETCHED PUSH: from actual push bytes, the byte step stores the
    pre-state source value below the pre-state top. -/
theorem byteschritt_geholt_push (s : Zustand) (src : Register)
    (suffix : List Byte) (m : Speicher)
    (hwin : StapelGeholt s (.push64 src) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.push64 src)).length = true)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m) :
    byteschritt s = .weiter (schrittPush s Register.rsp
      (ripNach s.rip (encode (.push64 src)).length)
      (s.register Register.rsp - BitVec.ofNat 64 8) m) := by
  have hlen : laengeOk (encode (.push64 src)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hkan := kanonisch_schritt_ueberein (.push64 src) s suffix hwin hexe
  obtain ⟨_, hbs⟩ := hkan
  have hs : schritt ⟨.push64 src, (encode (.push64 src)).length⟩ s =
      some (schrittPush s Register.rsp
        (ripNach s.rip (encode (.push64 src)).length)
        (s.register Register.rsp - BitVec.ofNat 64 8) m) :=
    schritt_push64_erfolg _ _ _ _ hlen rfl hwr
  rw [hs] at hbs
  exact hbs

/-- FETCHED POP: from actual pop bytes into a non-`rsp` register, the byte
    step advances past the word and delivers it. The `rsp` destination
    keeps its accepted `schrittPopTop` shape and is not covered here. -/
theorem byteschritt_geholt_pop (s : Zustand) (dst : Register)
    (suffix : List Byte) (v : Wort)
    (hwin : StapelGeholt s (.pop64 dst) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.pop64 dst)).length = true)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v)
    (hdst : dst ≠ Register.rsp) :
    byteschritt s = .weiter (schrittPopReg s Register.rsp dst
      (ripNach s.rip (encode (.pop64 dst)).length)
      (s.register Register.rsp + BitVec.ofNat 64 8) v) := by
  have hlen : laengeOk (encode (.pop64 dst)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hkan := kanonisch_schritt_ueberein (.pop64 dst) s suffix hwin hexe
  obtain ⟨_, hbs⟩ := hkan
  have hs : schritt ⟨.pop64 dst, (encode (.pop64 dst)).length⟩ s =
      some (schrittPopReg s Register.rsp dst
        (ripNach s.rip (encode (.pop64 dst)).length)
        (s.register Register.rsp + BitVec.ofNat 64 8) v) :=
    schritt_pop64_reg _ _ _ _ hlen rfl hdst hrd
  rw [hs] at hbs
  exact hbs

/-- FETCHED RET: from an actual return byte, the byte step moves control
    to the popped word and advances past it. -/
theorem byteschritt_geholt_ret (s : Zustand)
    (suffix : List Byte) (ziel : Wort)
    (hwin : StapelGeholt s .ret suffix)
    (hexe : ausfuehrbarN s.speicher s.rip (encode .ret).length = true)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel) :
    byteschritt s = .weiter (schrittRet s Register.rsp
      (s.register Register.rsp + BitVec.ofNat 64 8) ziel) := by
  have hlen : laengeOk (encode .ret).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hkan := kanonisch_schritt_ueberein .ret s suffix hwin hexe
  obtain ⟨_, hbs⟩ := hkan
  have hs : schritt ⟨.ret, (encode .ret).length⟩ s =
      some (schrittRet s Register.rsp
        (s.register Register.rsp + BitVec.ofNat 64 8) ziel) :=
    schritt_ret_erfolg _ _ _ hlen rfl hrd
  rw [hs] at hbs
  exact hbs

/-- FETCHED CALL ONTO A GUARD REFUSED: actual call bytes decode, but
    the return-address store below the top fails on a write-protected
    guard, so the byte step loudly refuses. -/
theorem byteschritt_geholt_call_wache (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    byteschritt s = .verweigert := by
  have hlen : laengeOk (encode (.call32 disp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hf := stapelGeholt_fetch s (.call32 disp) suffix hwin hexe
  have hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length) = none :=
    write64_verweigert _ _ _ hguard
  have hs : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s = none :=
    schritt_call32_verweigert _ _ _ hlen rfl hwr
  have hs : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s = none :=
    schritt_call32_verweigert _ _ _ hlen rfl hwr
  exact byteschritt_verweigert_ohne_schritt s _ _ hf hs

/-- FETCHED PUSH ONTO A GUARD REFUSED: actual push bytes decode, but the
    word store below the top fails on a write-protected guard. -/
theorem byteschritt_geholt_push_wache (s : Zustand) (src : Register)
    (suffix : List Byte)
    (hwin : StapelGeholt s (.push64 src) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.push64 src)).length = true)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    byteschritt s = .verweigert := by
  have hlen : laengeOk (encode (.push64 src)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hf := stapelGeholt_fetch s (.push64 src) suffix hwin hexe
  have hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = none :=
    write64_verweigert _ _ _ hguard
  have hs : schritt ⟨.push64 src, (encode (.push64 src)).length⟩ s = none :=
    schritt_push64_verweigert _ _ _ hlen rfl hwr
  have hfs : fetchDekodiert s =
      some (⟨.push64 src, (encode (.push64 src)).length⟩, suffix) := hf
  exact byteschritt_verweigert_ohne_schritt s _ _ hfs hs

/-- FETCHED RETURN INTO NON-EXECUTABLE REFUSED: an actual return byte
    steps to the popped target, but the target carries no execute
    permission, so the following byte step loudly refuses. Guard regions
    carry `ausfuehrbar = false`, so returns into a guard refuse here too. -/
theorem byteschritt_geholt_ret_nicht_ausfuehrbar (s s' : Zustand)
    (suffix : List Byte) (ziel : Wort)
    (hwin : StapelGeholt s .ret suffix)
    (hexe : ausfuehrbarN s.speicher s.rip (encode .ret).length = true)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : byteschritt s = .weiter s')
    (hxe : s.speicher.ausfuehrbar ziel = false) :
    byteschritt s' = .verweigert := by
  have hlen : laengeOk (encode .ret).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hb := byteschritt_geholt_ret s suffix ziel hwin hexe hrd
  rw [hstep] at hb
  have es : s' = schrittRet s Register.rsp
      (s.register Register.rsp + BitVec.ofNat 64 8) ziel := by
    injection hb
  have hret : schritt ⟨.ret, (encode .ret).length⟩ s = some s' := by
    rw [es]
    exact schritt_ret_erfolg _ _ _ hlen rfl hrd
  exact ret_ins_nicht_ausfuehrbar_verweigert s s' ziel _ hlen rfl hrd hret hxe

/-- NO STORE IS FOREIGN TO ITS OWN CODE WINDOW: a store at `rip` itself
    is never `CodeFremd`, so fetch preservation never covers a code-store
    overlap. The overlapping case falls outside loudly, by construction. -/
theorem codefremd_nie_selbst (s : Zustand) : ¬ CodeFremd s s.rip := by
  intro h
  exact h 0 (by decide) 0 (by decide) rfl

/-! ## Concrete nested-call witness: actual bytes, two code windows. -/

/-- Call displacement of the witness: 99 bytes forward. -/
def nestDisp : BitVec 32 := BitVec.ofNat 32 99

/-- Witness code bytes: `call +99` (5 bytes) at 4096, then `push rax`
    (80), `pop rbx` (91), `ret` (195) at 4200; zero elsewhere. The call
    target is 4101 + 99 = 4200, the first byte after the call. -/
def nestBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 232
  else if a.toNat = 4097 then natByte 99
  else if a.toNat = 4098 then natByte 0
  else if a.toNat = 4099 then natByte 0
  else if a.toNat = 4100 then natByte 0
  else if a.toNat = 4200 then natByte 80
  else if a.toNat = 4201 then natByte 91
  else if a.toNat = 4202 then natByte 195
  else BitVec.ofNat 8 0

/-- Witness code windows: 15 bytes at each site, covering every fetch. -/
def nestExec (a : Adresse) : Bool :=
  decide ((4096 ≤ a.toNat ∧ a.toNat < 4111) ∨
    (4200 ≤ a.toNat ∧ a.toNat < 4215))

/-- Witness stack extent: 8176..8192, readable and writable. -/
def nestDaten (a : Adresse) : Bool :=
  decide (8176 ≤ a.toNat ∧ a.toNat < 8192)

/-- Witness memory: two code windows plus the stack cell. Code is
    deliberately NOT data-readable: fetch needs execute, never read. -/
def nestSpeicher : Speicher :=
  { bytes := nestBytes
    lesbar := nestDaten
    schreibbar := nestDaten
    ausfuehrbar := nestExec }

/-- Witness registers: stack top at 8192, `rax` holding 42. -/
def nestReg : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 8192
  else if q = Register.rax then BitVec.ofNat 64 42
  else BitVec.ofNat 64 0

/-- Witness start state: `call` at 4096, stack top at 8192. -/
def nestS0 : Zustand :=
  { register := nestReg, flags := zeugFlags,
    rip := BitVec.ofNat 64 4096, speicher := nestSpeicher }

/-- Outer stack slot: one word below the pre-state top. -/
def nestOben0 : Adresse := BitVec.ofNat 64 8184

/-- Memory after the call stores the post-decode address 4101. -/
def nestM1 : Speicher := { nestSpeicher with
  bytes := writeBytes nestSpeicher nestOben0 (ripNach nestS0.rip 5) }

/-- State after the fetched `call +99` (length 5): control at 4200. -/
def nestS1 : Zustand := schrittCall nestS0 Register.rsp nestM1 nestOben0
  (ripNach nestS0.rip 5 + dispWort nestDisp)

/-- Inner stack slot: one word below the post-call top. -/
def nestObenP : Adresse := BitVec.ofNat 64 8176

/-- Memory after the inner push stores the caller's `rax` word. -/
def nestMp : Speicher := { nestM1 with
  bytes := writeBytes nestM1 nestObenP (nestS1.register Register.rax) }

/-- State after the fetched `push rax` (length 1). -/
def nestS2 : Zustand := schrittPush nestS1 Register.rsp
  (ripNach nestS1.rip 1) nestObenP nestMp

/-- State after the fetched `pop rbx` (length 1). -/
def nestS3 : Zustand := schrittPopReg nestS2 Register.rsp Register.rbx
  (ripNach nestS2.rip 1)
  (nestS2.register Register.rsp + BitVec.ofNat 64 8) 42

/-- State after the fetched `ret` (length 1): control back at 4101. -/
def nestS4 : Zustand := schrittRet nestS3 Register.rsp
  (nestS3.register Register.rsp + BitVec.ofNat 64 8)
  (ripNach nestS0.rip 5)

/-- CALL SITE FETCH: the actual 15 bytes at 4096 are the canonical
    `call +99` encoding followed by ten zero bytes. -/
theorem nest_call_geholt : StapelGeholt nestS0 (.call32 nestDisp)
    (List.replicate 10 (BitVec.ofNat 8 0)) := by
  unfold StapelGeholt
  decide

/-- The consumed call prefix is executable. -/
theorem nest_call_exe : ausfuehrbarN nestS0.speicher nestS0.rip
    (encode (.call32 nestDisp)).length = true := by
  decide

/-- PUSH SITE FETCH: the actual bytes at 4200 are the canonical
    `push rax` byte followed by `pop`/`ret` and twelve zero bytes. -/
theorem nest_push_geholt : StapelGeholt nestS1 (.push64 .rax)
    ([natByte 91, natByte 195] ++
      List.replicate 12 (BitVec.ofNat 8 0)) := by
  unfold StapelGeholt
  decide

/-- The consumed push prefix is executable. -/
theorem nest_push_exe : ausfuehrbarN nestS1.speicher nestS1.rip
    (encode (.push64 .rax)).length = true := by
  decide

/-- POP SITE FETCH: the actual bytes at 4201 are the canonical
    `pop rbx` byte followed by `ret` and thirteen zero bytes. -/
theorem nest_pop_geholt : StapelGeholt nestS2 (.pop64 .rbx)
    ([natByte 195] ++ List.replicate 12 (BitVec.ofNat 8 0)) := by
  unfold StapelGeholt
  decide

/-- The consumed pop prefix is executable. -/
theorem nest_pop_exe : ausfuehrbarN nestS2.speicher nestS2.rip
    (encode (.pop64 .rbx)).length = true := by
  decide

/-- RET SITE FETCH: the actual bytes at 4202 are the canonical `ret`
    byte followed by fourteen zero bytes. -/
theorem nest_ret_geholt : StapelGeholt nestS3 .ret
    (List.replicate 12 (BitVec.ofNat 8 0)) := by
  unfold StapelGeholt
  decide

/-- The consumed return prefix is executable. -/
theorem nest_ret_exe : ausfuehrbarN nestS3.speicher nestS3.rip
    (encode .ret).length = true := by
  decide

/-- The pre-state top minus 8 is the outer slot. -/
theorem nest_rsp0 : nestS0.register Register.rsp - BitVec.ofNat 64 8 =
    nestOben0 := by
  decide

/-- The outer slot is writable for eight bytes. -/
theorem nest_oben0_schreibbar :
    schreibbar8 nestSpeicher nestOben0 = true := by
  decide

/-- The outer slot is readable for eight bytes. -/
theorem nest_oben0_lesbar :
    lesbar8 nestSpeicher nestOben0 = true := by
  decide

/-- The call installs the post-decode address 4101 below the old top. -/
theorem nest_call_schreibt : write64 nestSpeicher nestOben0
    (ripNach nestS0.rip (encode (.call32 nestDisp)).length) =
    some nestM1 := by
  have hlen : (encode (.call32 nestDisp)).length = 5 := rfl
  rw [hlen]
  unfold write64 nestM1
  rw [if_pos nest_oben0_schreibbar]

/-- The post-call top minus 8 is the inner slot. -/
theorem nest_rsp1 : nestS1.register Register.rsp - BitVec.ofNat 64 8 =
    nestObenP := by
  decide

/-- The inner slot is writable for eight bytes. -/
theorem nest_obenp_schreibbar :
    schreibbar8 nestM1 nestObenP = true := by
  decide

/-- The inner slot is readable for eight bytes. -/
theorem nest_obenp_lesbar :
    lesbar8 nestM1 nestObenP = true := by
  decide

/-- The inner push installs the caller's `rax` word below the call top. -/
theorem nest_push_schreibt : write64 nestM1 nestObenP
    (nestS1.register Register.rax) = some nestMp := by
  unfold write64 nestMp
  rw [if_pos nest_obenp_schreibbar]

/-- The pushed word reads back at the inner slot. -/
theorem nest_push_liest : read64 nestS2.speicher
    (nestS2.register Register.rsp) = some 42 := by
  decide

/-- The stored return address reads back at the outer slot. -/
theorem nest_ret_liest : read64 nestS3.speicher
    (nestS3.register Register.rsp) = some (ripNach nestS0.rip 5) := by
  decide

/-- The call lands at 4200: post-decode 4101 plus displacement 99. -/
theorem nest_ziel_4200 : ripNach nestS0.rip 5 + dispWort nestDisp =
    BitVec.ofNat 64 4200 := by
  decide

/-! ## Fetched nested-call restoration over actual bytes. -/

/-- FETCHED NESTED RESTORATION: when the actual fetched bytes at four
    successive states are the canonical call/push/pop/ret encodings with
    executable prefixes, and the stack guards pass with disjoint slots,
    the byte-step chain restores the pre-state stack pointer, lands on
    the correct next-RIP return word, delivers the inner value and
    preserves every permission map. The `Decodiert` values in the step
    premises are forced to match the fetched bytes: `stapelGeholt_fetch`
    yields exactly those outcomes, so no forged decoded value can enter.
    Restoration itself reuses the accepted `StackUnwind` proof. -/
theorem geholt_verschachtelt_wiederhergestellt
    (s s1 s2 s3 s4 : Zustand)
    (disp : BitVec 32) (src dst : Register)
    (sc sp sq sr : List Byte)
    (mc mp : Speicher) (vp vr : Wort)
    (hwinc : StapelGeholt s (.call32 disp) sc)
    (hexec : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hwrc : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip (encode (.call32 disp)).length) = some mc)
    (hlesc : lesbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepc : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s =
      some s1)
    (hwinp : StapelGeholt s1 (.push64 src) sp)
    (hexep : ausfuehrbarN s1.speicher s1.rip
      (encode (.push64 src)).length = true)
    (hwrp : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (s1.register src) = some mp)
    (hlesp : lesbar8 s1.speicher
      (s1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepp : schritt ⟨.push64 src, (encode (.push64 src)).length⟩ s1 =
      some s2)
    (hrdp : read64 s2.speicher (s2.register Register.rsp) = some vp)
    (hstepq : schritt ⟨.pop64 dst, (encode (.pop64 dst)).length⟩ s2 =
      some s3)
    (hdst : dst ≠ Register.rsp)
    (hwinq : StapelGeholt s2 (.pop64 dst) sq)
    (hexeq : ausfuehrbarN s2.speicher s2.rip
      (encode (.pop64 dst)).length = true)
    (hrdr : read64 s3.speicher (s3.register Register.rsp) = some vr)
    (hstepr : schritt ⟨.ret, (encode .ret).length⟩ s3 = some s4)
    (hwinr : StapelGeholt s3 .ret sr)
    (hexer : ausfuehrbarN s3.speicher s3.rip
      (encode .ret).length = true)
    (hdis : Disjunkt (s.register Register.rsp - BitVec.ofNat 64 8)
      (s1.register Register.rsp - BitVec.ofNat 64 8)) :
    byteschritt s = .weiter s1 ∧ byteschritt s1 = .weiter s2 ∧
      byteschritt s2 = .weiter s3 ∧ byteschritt s3 = .weiter s4 ∧
      s4.register Register.rsp = s.register Register.rsp ∧
      s4.rip = ripNach s.rip (encode (.call32 disp)).length ∧
      s4.register dst = s1.register src ∧
      s4.speicher.ausfuehrbar = s.speicher.ausfuehrbar ∧
      s4.speicher.lesbar = s.speicher.lesbar ∧
      s4.speicher.schreibbar = s.speicher.schreibbar := by
  have hlen_c : laengeOk (encode (.call32 disp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlen_p : laengeOk (encode (.push64 src)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlen_q : laengeOk (encode (.pop64 dst)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlen_r : laengeOk (encode .ret).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hf1 := stapelGeholt_fetch s (.call32 disp) sc hwinc hexec
  have hf2 := stapelGeholt_fetch s1 (.push64 src) sp hwinp hexep
  have hf3 := stapelGeholt_fetch s2 (.pop64 dst) sq hwinq hexeq
  have hf4 := stapelGeholt_fetch s3 .ret sr hwinr hexer
  have hb1 : byteschritt s = .weiter s1 :=
    byteschritt_weiter s s1 _ _ hf1 hstepc
  have hb2 : byteschritt s1 = .weiter s2 :=
    byteschritt_weiter s1 s2 _ _ hf2 hstepp
  have hb3 : byteschritt s2 = .weiter s3 :=
    byteschritt_weiter s2 s3 _ _ hf3 hstepq
  have hb4 : byteschritt s3 = .weiter s4 :=
    byteschritt_weiter s3 s4 _ _ hf4 hstepr
  have hrest := verschachtelt_wiederhergestellt s s1 s2 s3 s4 disp src dst
    (⟨.call32 disp, (encode (.call32 disp)).length⟩)
    (⟨.push64 src, (encode (.push64 src)).length⟩)
    (⟨.pop64 dst, (encode (.pop64 dst)).length⟩)
    (⟨.ret, (encode .ret).length⟩)
    mc mp vp vr hlen_c rfl hwrc hlesc hstepc hwrp hlesp hstepp
    hlen_p rfl hrdp hstepq hlen_q rfl hdst hrdr hstepr hlen_r rfl hdis
  obtain ⟨hrsp, hrip, hval, hexeP, hlesP, hschrP⟩ := hrest
  exact ⟨hb1, hb2, hb3, hb4, hrsp, hrip, hval, hexeP, hlesP, hschrP⟩

/-! ## Stack stores preserve the fetch: the Stapel/CodeImmutability link. -/

/-- The outer stack slot is foreign to the call-site code window: the
    whole 15-byte fetch range at 4096 stays far below 8184. -/
theorem nest_aussen_fremd : CodeFremd nestS0 nestOben0 := by
  apply codeFremd_von_intervallen
  · decide
  · decide
  · exact Or.inl (by decide)

/-- The inner stack slot is foreign to the callee-site code window: the
    whole 15-byte fetch range at 4200 stays below 8176. -/
theorem nest_innen_fremd : CodeFremd nestS1 nestObenP := by
  apply codeFremd_von_intervallen
  · decide
  · decide
  · exact Or.inl (by decide)

/-- STACK WRITES KEEP THE FETCH: both word stores of the nested run are
    foreign to their code windows, so neither changes the fetched window
    or the decode outcome. Uses the accepted preservation lemmas. -/
theorem nest_schreiben_haelt_fetch :
    geholt { nestS0 with speicher := nestM1 } = geholt nestS0 ∧
      geholt { nestS1 with speicher := nestMp } = geholt nestS1 := by
  have hwr0 : write64 nestS0.speicher nestOben0
      (ripNach nestS0.rip (encode (.call32 nestDisp)).length) =
      some nestM1 :=
    nest_call_schreibt
  have hwr1 : write64 nestS1.speicher nestObenP
      (nestS1.register Register.rax) = some nestMp :=
    nest_push_schreibt
  exact ⟨geholt_nach_fremd_schreiben nestS0 nestM1 nestOben0 _ hwr0
      nest_aussen_fremd,
    geholt_nach_fremd_schreiben nestS1 nestMp nestObenP _ hwr1
      nest_innen_fremd⟩

/-! ## Frame sonde: the witness slots are checked Stapel slots. -/

/-- Witness frame: base 8160, four word slots up to 8192. -/
def nestRahmen : Rahmen := { basis := 8160, tiefe := 32 }

/-- The witness frame is checked. -/
theorem nest_rahmen_ok : rahmenOk nestRahmen = true := by
  decide

/-- The inner slot is frame slot 2. -/
theorem nest_slot_innen : nestRahmen.schlitzAddr 2 = nestObenP := by
  decide

/-- The outer slot is frame slot 3. -/
theorem nest_slot_aussen : nestRahmen.schlitzAddr 3 = nestOben0 := by
  decide

/-- FRAME SONDE: the checked frame carries both stack slots, the stack
    top counts as inside at every stage, and the frame top is the
    16-aligned call boundary. Pre-state `rsp` semantics is preserved:
    every stage top stays inside this one frame. -/
theorem nest_rahmen_sonde :
    rahmenOk nestRahmen = true ∧
      nestRahmen.schlitzAddr 2 = nestObenP ∧
      nestRahmen.schlitzAddr 3 = nestOben0 ∧
      rspImRahmen nestS0 nestRahmen = true ∧
      rspImRahmen nestS1 nestRahmen = true ∧
      rspImRahmen nestS4 nestRahmen = true ∧
      ausgerichtet16 nestRahmen.spitzeWort = true := by
  refine ⟨nest_rahmen_ok, nest_slot_innen, nest_slot_aussen, by decide,
    by decide, by decide, by decide⟩

/-! ## Joint witness: every premise holds on the actual-byte run. -/

/-- The two stack slots are disjoint words. -/
theorem nest_slots_disjunkt :
    Disjunkt (nestS0.register Register.rsp - BitVec.ofNat 64 8)
      (nestS1.register Register.rsp - BitVec.ofNat 64 8) := by
  rw [nest_rsp0, nest_rsp1]
  show Disjunkt (BitVec.ofNat 64 8184) (BitVec.ofNat 64 8176)
  exact disjunkt_von_intervallen _ _
    (by unfold OhneUmbruch; decide) (by unfold OhneUmbruch; decide)
    (Or.inr (by decide))

/-- JOINT WITNESS (fetched nested call): every premise of fetched nested
    restoration holds jointly on a non-degenerate run from actual
    executable-memory bytes — the call observably changes memory (zero
    becomes the return address below the old top), the four byte steps
    chain, the stack pointer is restored and control lands on the
    correct next-RIP word 4101. -/
theorem geholt_verschachtelt_wiederhergestellt_zeuge :
    ∃ (s s1 s2 s3 s4 : Zustand) (disp : BitVec 32) (src dst : Register)
      (sc sp sq sr : List Byte) (mc mp : Speicher) (vp vr : Wort),
      StapelGeholt s (.call32 disp) sc ∧
      (ausfuehrbarN s.speicher s.rip (encode (.call32 disp)).length = true) ∧
      (write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        (ripNach s.rip (encode (.call32 disp)).length) = some mc) ∧
      (lesbar8 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s = some s1) ∧
      StapelGeholt s1 (.push64 src) sp ∧
      (ausfuehrbarN s1.speicher s1.rip (encode (.push64 src)).length
        = true) ∧
      (write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
        (s1.register src) = some mp) ∧
      (lesbar8 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
        = true) ∧
      (schritt ⟨.push64 src, (encode (.push64 src)).length⟩ s1 = some s2) ∧
      (read64 s2.speicher (s2.register Register.rsp) = some vp) ∧
      (schritt ⟨.pop64 dst, (encode (.pop64 dst)).length⟩ s2 = some s3) ∧
      (dst ≠ Register.rsp) ∧
      StapelGeholt s2 (.pop64 dst) sq ∧
      (ausfuehrbarN s2.speicher s2.rip (encode (.pop64 dst)).length
        = true) ∧
      (read64 s3.speicher (s3.register Register.rsp) = some vr) ∧
      (schritt ⟨.ret, (encode .ret).length⟩ s3 = some s4) ∧
      StapelGeholt s3 .ret sr ∧
      (ausfuehrbarN s3.speicher s3.rip (encode .ret).length = true) ∧
      (Disjunkt (s.register Register.rsp - BitVec.ofNat 64 8)
        (s1.register Register.rsp - BitVec.ofNat 64 8)) ∧
      (s.speicher.bytes (s.register Register.rsp - BitVec.ofNat 64 8) ≠
        mc.bytes (s.register Register.rsp - BitVec.ofNat 64 8)) ∧
      (laufBytes 4 s = .weiter s4) ∧
      (s4.register Register.rsp = s.register Register.rsp) ∧
      (s4.rip = ripNach s.rip (encode (.call32 disp)).length) := by
  have hlen_c : laengeOk (encode (.call32 nestDisp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlen_p : laengeOk (encode (.push64 .rax)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlen_q : laengeOk (encode (.pop64 .rbx)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlen_r : laengeOk (encode .ret).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hwrc0 : write64 nestS0.speicher
      (nestS0.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach nestS0.rip (encode (.call32 nestDisp)).length) =
      some nestM1 := by
    rw [nest_rsp0]
    exact nest_call_schreibt
  have hlesc0 : lesbar8 nestS0.speicher
      (nestS0.register Register.rsp - BitVec.ofNat 64 8) = true := by
    rw [nest_rsp0]
    exact nest_oben0_lesbar
  have hstepc0 : schritt
      (⟨.call32 nestDisp, (encode (.call32 nestDisp)).length⟩ : Decodiert)
      nestS0 = some nestS1 :=
    schritt_call32_erfolg _ _ _ _ hlen_c rfl hwrc0
  have hwrp0 : write64 nestS1.speicher
      (nestS1.register Register.rsp - BitVec.ofNat 64 8)
      (nestS1.register Register.rax) = some nestMp := by
    rw [nest_rsp1]
    exact nest_push_schreibt
  have hlesp0 : lesbar8 nestS1.speicher
      (nestS1.register Register.rsp - BitVec.ofNat 64 8) = true := by
    rw [nest_rsp1]
    exact nest_obenp_lesbar
  have hstepp0 : schritt
      (⟨.push64 .rax, (encode (.push64 .rax)).length⟩ : Decodiert)
      nestS1 = some nestS2 :=
    schritt_push64_erfolg _ _ _ _ hlen_p rfl hwrp0
  have hstepq0 : schritt
      (⟨.pop64 .rbx, (encode (.pop64 .rbx)).length⟩ : Decodiert)
      nestS2 = some nestS3 :=
    schritt_pop64_reg _ _ _ _ hlen_q rfl (by decide) nest_push_liest
  have hstepr0 : schritt
      (⟨.ret, (encode .ret).length⟩ : Decodiert)
      nestS3 = some nestS4 :=
    schritt_ret_erfolg _ _ _ hlen_r rfl nest_ret_liest
  have hg := geholt_verschachtelt_wiederhergestellt nestS0 nestS1 nestS2
    nestS3 nestS4 nestDisp .rax .rbx _ _ _ _ nestM1 nestMp 42
    (ripNach nestS0.rip 5) nest_call_geholt nest_call_exe hwrc0 hlesc0
    hstepc0 nest_push_geholt nest_push_exe hwrp0 hlesp0 hstepp0
    nest_push_liest hstepq0 (by decide) nest_pop_geholt nest_pop_exe
    nest_ret_liest hstepr0 nest_ret_geholt nest_ret_exe
    nest_slots_disjunkt
  obtain ⟨hb1, hb2, hb3, hb4, hrsp, hrip, _, _, _, _⟩ := hg
  have hlauf : laufBytes 4 nestS0 = .weiter nestS4 := by
    simp only [laufBytes, hb1, hb2, hb3, hb4]
  have hmem : nestS0.speicher.bytes
      (nestS0.register Register.rsp - BitVec.ofNat 64 8) ≠
      nestM1.bytes
        (nestS0.register Register.rsp - BitVec.ofNat 64 8) := by
    rw [nest_rsp0]
    have hhit := writeBytesN_hit nestSpeicher nestOben0
      (ripNach nestS0.rip 5) 8 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠
      writeBytes nestSpeicher nestOben0 (ripNach nestS0.rip 5) nestOben0
    unfold writeBytes
    rw [hhit]
    decide
  exact ⟨nestS0, nestS1, nestS2, nestS3, nestS4, nestDisp, .rax, .rbx,
    _, _, _, _, nestM1, nestMp, 42, (ripNach nestS0.rip 5),
    nest_call_geholt, nest_call_exe, hwrc0, hlesc0, hstepc0,
    nest_push_geholt, nest_push_exe, hwrp0, hlesp0, hstepp0,
    nest_push_liest, hstepq0, (by decide), nest_pop_geholt, nest_pop_exe,
    nest_ret_liest, hstepr0, nest_ret_geholt, nest_ret_exe,
    nest_slots_disjunkt, hmem, hlauf, hrsp, hrip⟩

/-! ## Planted refusals: joint witnesses from actual bytes. -/

/-- Guard witness memory: same code bytes as the nested run, but the
    stack slot below the top is write-protected. -/
def wacheNestSpeicher : Speicher :=
  { nestSpeicher with schreibbar := fun _ => false }

/-- Guard witness start: `call` at 4096, stack top at 8192. -/
def wacheNestS : Zustand :=
  { nestS0 with speicher := wacheNestSpeicher }

/-- GUARD FETCH: the guard keeps code bytes and execute rights, so the
    actual call bytes still fetch. -/
theorem wacheNest_geholt : StapelGeholt wacheNestS (.call32 nestDisp)
    (List.replicate 10 (BitVec.ofNat 8 0)) := by
  unfold StapelGeholt
  decide

/-- The consumed call prefix stays executable under the guard. -/
theorem wacheNest_exe : ausfuehrbarN wacheNestS.speicher wacheNestS.rip
    (encode (.call32 nestDisp)).length = true := by
  decide

/-- The stack slot below the top is guard-protected. -/
theorem wacheNest_guard : schreibbar8 wacheNestS.speicher
    (wacheNestS.register Register.rsp - BitVec.ofNat 64 8) = false := by
  decide

/-- NEGATIVE WITNESS (guard store): every premise of fetched call-guard
    refusal holds jointly — actual call bytes fetch, but the
    return-address store below the top hits the guard, so the byte step
    loudly refuses. -/
theorem byteschritt_geholt_call_wache_zeuge :
    ∃ (s : Zustand) (disp : BitVec 32) (suffix : List Byte),
      StapelGeholt s (.call32 disp) suffix ∧
      (ausfuehrbarN s.speicher s.rip (encode (.call32 disp)).length
        = true) ∧
      (schreibbar8 s.speicher
        (s.register Register.rsp - BitVec.ofNat 64 8) = false) ∧
      (byteschritt s = .verweigert) := by
  exact ⟨wacheNestS, nestDisp, _, wacheNest_geholt, wacheNest_exe,
    wacheNest_guard,
    byteschritt_geholt_call_wache _ _ _ wacheNest_geholt wacheNest_exe
      wacheNest_guard⟩

/-- Return-refusal witness memory: a `ret` byte at 4096 (executable),
    the stack word 12288 at 8192, and no execute permission at 12288. -/
def retNestSpeicher : Speicher :=
  { bytes := fun a =>
      if a.toNat = 4096 then natByte 195
      else if a.toNat = 8192 then BitVec.ofNat 8 0
      else if a.toNat = 8193 then BitVec.ofNat 8 48
      else BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun a => decide (a.toNat = 4096) }

/-- Return-refusal witness start: `ret` at 4096, stack top at 8192. -/
def retNestS : Zustand :=
  { register := fun q =>
      if q = Register.rsp then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0
    flags := zeugFlags
    rip := BitVec.ofNat 64 4096
    speicher := retNestSpeicher }

/-- RET FETCH: the actual byte at 4096 is the canonical `ret`. -/
theorem retNest_geholt : StapelGeholt retNestS .ret [] := by
  unfold StapelGeholt
  decide

/-- The consumed return prefix is executable. -/
theorem retNest_exe : ausfuehrbarN retNestS.speicher retNestS.rip
    (encode .ret).length = true := by
  decide

/-- The stack word reads back as the non-executable target 12288. -/
theorem retNest_liest : read64 retNestS.speicher
    (retNestS.register Register.rsp) = some (BitVec.ofNat 64 12288) := by
  decide

/-- The popped target carries no execute permission. -/
theorem retNest_kein_exec : retNestS.speicher.ausfuehrbar
    (BitVec.ofNat 64 12288) = false := by
  decide

/-- NEGATIVE WITNESS (non-executable return): every premise of fetched
    return refusal holds jointly — an actual return byte steps to the
    popped target, but the target is not executable, so the following
    byte step loudly refuses. -/
theorem byteschritt_geholt_ret_nicht_ausfuehrbar_zeuge :
    ∃ (s s' : Zustand) (suffix : List Byte) (ziel : Wort),
      StapelGeholt s .ret suffix ∧
      (ausfuehrbarN s.speicher s.rip (encode .ret).length = true) ∧
      (read64 s.speicher (s.register Register.rsp) = some ziel) ∧
      (byteschritt s = .weiter s') ∧
      (s.speicher.ausfuehrbar ziel = false) ∧
      (byteschritt s' = .verweigert) := by
  have hstep : byteschritt retNestS =
      .weiter (schrittRet retNestS Register.rsp
        (retNestS.register Register.rsp + BitVec.ofNat 64 8)
        (BitVec.ofNat 64 12288)) :=
    byteschritt_geholt_ret _ _ _ retNest_geholt retNest_exe retNest_liest
  refine ⟨retNestS, _, [], (BitVec.ofNat 64 12288), retNest_geholt,
    retNest_exe, retNest_liest, hstep, retNest_kein_exec, ?_⟩
  exact byteschritt_geholt_ret_nicht_ausfuehrbar _ _ _ _
    retNest_geholt retNest_exe retNest_liest hstep retNest_kein_exec

/- CUTS:
     Proved here: fetched-window decoding of canonical stack bytes
     (`stapelGeholt_fetch` via `kanonisch_schritt_ueberein`); fetched
     CALL/PUSH/POP/RET byte steps storing the correct next-RIP return
     word below the pre-state top (`byteschritt_geholt_call/push/pop/ret`,
     no hand-built decoded values enter); fetched nested-call restoration
     over actual bytes — byte-step chain, pre-state `rsp` restoration,
     correct next-RIP return word, inner-value delivery and permission
     preservation (`geholt_verschachtelt_wiederhergestellt`, reusing the
     accepted `StackUnwind` proof); stack stores preserve the fetch
     (`nest_schreiben_haelt_fetch` via accepted `CodeFremd` preservation,
     with `nest_aussen_fremd`/`nest_innen_fremd` through the interval
     bridge); witness slots as checked `Stapel` frame slots
     (`nest_rahmen_sonde`); guard refusal of fetched call/push
     (`byteschritt_geholt_call_wache/push_wache` via `StackUnwind`
     guards); fetched return into non-executable memory refuses the next
     byte step (`byteschritt_geholt_ret_nicht_ausfuehrbar`, guards
     included since guards carry `ausfuehrbar = false`); no store is
     foreign to its own code window (`codefremd_nie_selbst`), so
     code-store overlap never claims fetch preservation — the accepted
     overlap counterexample (`ueberlapp_geaendert_zeuge`) is the negative
     side; joint non-degenerate witnesses with real reached
     memory-changing execution (`geholt_verschachtelt_wiederhergestellt_zeuge`
     with `laufBytes 4`, observable zero-to-return-address change) and
     planted refusals (`byteschritt_geholt_call_wache_zeuge`,
     `byteschritt_geholt_ret_nicht_ausfuehrbar_zeuge`).
     NOT proved here, and not claimed:
     - No ABI callee-save/entry contracts and no source-call linkage:
       which registers survive a call and what a source call compiles to
       stay OPEN (cuts by task order).
     - No TSO bridge: every fact is sequential over one canonical
       `Speicher`; store buffers, forwarding and GX refinement stay with
       the TSO-bridge work.
     - No whole-source self-modifying-code refusal and no loader, entry,
       relocation, cost or final-image claim.
     - No new hardware or software assumptions: the only gates are the
       accepted execute/read/write permissions of the consumed prefixes
       and stack slots.
-/

#print axioms StapelGeholt
#print axioms stapelGeholt_fetch
#print axioms byteschritt_geholt_call
#print axioms byteschritt_geholt_push
#print axioms byteschritt_geholt_pop
#print axioms byteschritt_geholt_ret
#print axioms byteschritt_geholt_call_wache
#print axioms byteschritt_geholt_push_wache
#print axioms byteschritt_geholt_ret_nicht_ausfuehrbar
#print axioms codefremd_nie_selbst
#print axioms nest_call_geholt
#print axioms nest_call_exe
#print axioms nest_push_geholt
#print axioms nest_push_exe
#print axioms nest_pop_geholt
#print axioms nest_pop_exe
#print axioms nest_ret_geholt
#print axioms nest_ret_exe
#print axioms nest_rsp0
#print axioms nest_oben0_schreibbar
#print axioms nest_oben0_lesbar
#print axioms nest_call_schreibt
#print axioms nest_rsp1
#print axioms nest_obenp_schreibbar
#print axioms nest_obenp_lesbar
#print axioms nest_push_schreibt
#print axioms nest_push_liest
#print axioms nest_ret_liest
#print axioms nest_ziel_4200
#print axioms geholt_verschachtelt_wiederhergestellt
#print axioms nest_aussen_fremd
#print axioms nest_innen_fremd
#print axioms nest_schreiben_haelt_fetch
#print axioms nest_rahmen_ok
#print axioms nest_slot_innen
#print axioms nest_slot_aussen
#print axioms nest_rahmen_sonde
#print axioms nest_slots_disjunkt
#print axioms geholt_verschachtelt_wiederhergestellt_zeuge
#print axioms wacheNest_geholt
#print axioms wacheNest_exe
#print axioms wacheNest_guard
#print axioms byteschritt_geholt_call_wache_zeuge
#print axioms retNest_geholt
#print axioms retNest_exe
#print axioms retNest_liest
#print axioms retNest_kein_exec
#print axioms byteschritt_geholt_ret_nicht_ausfuehrbar_zeuge

end Gabbro.Grammatik.X86
