/-
  File:      Grammatik/X86/TsoGxEntryBytes.lean
  Subject:   Byte-level entry/call linkage for the start-anchored bridged run.

  Follow-up of lane 1253 (`TsoGxStart.lean`): the prefix there is
  source-level (`RufSchrittG` from `RufStartG`), while
  `PipelineEntry.prolog_lauf` and
  `StackExecution.geholt_verschachtelt_wiederhergestellt` live on the byte
  machine (`Zustand`, `laufBytes`). This module proves the linkage on the
  byte side and names the admission it stands on: the entry sequence
  (`prolog_lauf`: `AbiArgs` to `EnvRepr`) followed by one fetched
  call/push/pop/ret nest (return word below the old top, inner value
  delivered, stack pointer restored) reaches the fragment-head byte state
  with the entry `WorldRep`/`EnvRepr` transported across the two stack
  writes (both slots foreign to every placed slot). The source-level
  prefix (`fragmentKopf_erreichbar`, `startFragment_zeuge`) is reused by
  reference; the joint witness shows both sides reach their head, with the
  call frame written and restored through memory. What is NOT covered is
  refused (guard slot, non-executable return, clobbering prolog) or listed
  in CUTS. No new machine, no new decoder, no silicon claim.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.StackExecution
import Grammatik.X86.TsoGxStart

namespace Gabbro.Grammatik.X86.TsoGxEntryBytes

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineEntry

/-- Both stack slots are foreign to every placed slot: the admission that
    lets the entry representation survive the call frame writes. -/
def StapelLayoutFremd {D : Deklaration} (L : Layout D) (aussen innen : Adresse) : Prop :=
  ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
    L.loc t k f = some a0 → Disjunkt aussen (natAdresse a0) ∧ Disjunkt innen (natAdresse a0)

/-- WORLD SURVIVAL OF ONE FOREIGN WORD STORE: a successful `write64`
    at an address foreign to every placed slot keeps the representation of
    the same world: permissions are unchanged, and every placed slot reads
    through the frame (`read64_rahmen`). -/
theorem worldRep_schreiben_fremd {D : Deklaration} (L : Layout D) (m m' : Speicher)
    (σ : World D) (a : Adresse) (v : Wort)
    (hW : WorldRep L m σ) (hwr : write64 m a v = some m')
    (hf : ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
      L.loc t k f = some a0 → Disjunkt a (natAdresse a0)) :
    WorldRep L m' σ := by
  intro t2 k2 f2 a2 hloc2
  obtain ⟨hok2, hrd2, hwr2, hrep2⟩ := hW t2 k2 f2 a2 hloc2
  refine ⟨hok2, by rw [lesbar8_nach_schreiben m m' _ _ _ hwr]; exact hrd2,
    by rw [schreibbar8_nach_schreiben m m' _ _ _ hwr]; exact hwr2, ?_⟩
  intro lo2 hi2 hT2
  have hrep := hrep2 lo2 hi2 hT2
  unfold RepSlot at hrep ⊢
  rw [read64_rahmen m m' _ _ _ hwr (hf t2 k2 f2 a2 hloc2)]
  exact hrep

/-- THE BYTE ENTRY/CALL PREFIX RUNS: an entry run of `proLen` fetched
    steps (the `prolog_lauf` outcome: memory and stack top kept) followed
    by one fetched call/push/pop/ret nest reaches the fragment-head byte
    state: the stack pointer is restored to the entry top, control is on
    the next-`rip` return word, the inner value is delivered, and every
    permission map is preserved. Every premise is consumed by the accepted
    nested-restoration theorem. -/
theorem eintrittCallPrefix_lauf
    (s0 s1 b1 b2 b3 b4 : Zustand)
    (proLen : Nat) (disp : BitVec 32) (src dst : Register)
    (sc sp sq sr : List Byte)
    (mc mp : Speicher) (vp vr : Wort)
    (hpro : laufBytes proLen s0 = .weiter s1)
    (hrsp0 : s1.register Register.rsp = s0.register Register.rsp)
    (hwinc : StapelGeholt s1 (.call32 disp) sc)
    (hexec : ausfuehrbarN s1.speicher s1.rip
      (encode (.call32 disp)).length = true)
    (hwrc : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s1.rip (encode (.call32 disp)).length) = some mc)
    (hlesc : lesbar8 s1.speicher
      (s1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepc : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s1 =
      some b1)
    (hwinp : StapelGeholt b1 (.push64 src) sp)
    (hexep : ausfuehrbarN b1.speicher b1.rip
      (encode (.push64 src)).length = true)
    (hwrp : write64 b1.speicher (b1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register src) = some mp)
    (hlesp : lesbar8 b1.speicher
      (b1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepp : schritt ⟨.push64 src, (encode (.push64 src)).length⟩ b1 =
      some b2)
    (hrdp : read64 b2.speicher (b2.register Register.rsp) = some vp)
    (hstepq : schritt ⟨.pop64 dst, (encode (.pop64 dst)).length⟩ b2 =
      some b3)
    (hdst : dst ≠ Register.rsp)
    (hsrc : src ≠ Register.rsp)
    (hwinq : StapelGeholt b2 (.pop64 dst) sq)
    (hexeq : ausfuehrbarN b2.speicher b2.rip
      (encode (.pop64 dst)).length = true)
    (hrdr : read64 b3.speicher (b3.register Register.rsp) = some vr)
    (hstepr : schritt ⟨.ret, (encode .ret).length⟩ b3 = some b4)
    (hwinr : StapelGeholt b3 .ret sr)
    (hexer : ausfuehrbarN b3.speicher b3.rip
      (encode .ret).length = true)
    (hdis : Disjunkt (s1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register Register.rsp - BitVec.ofNat 64 8)) :
    laufBytes (proLen + 4) s0 = .weiter b4 ∧
      b4.register Register.rsp = s0.register Register.rsp ∧
      b4.rip = ripNach s1.rip (encode (.call32 disp)).length ∧
      b4.register dst = s1.register src ∧
      b4.speicher.ausfuehrbar = s1.speicher.ausfuehrbar ∧
      b4.speicher.lesbar = s1.speicher.lesbar ∧
      b4.speicher.schreibbar = s1.speicher.schreibbar := by
  obtain ⟨hb1, hb2, hb3, hb4, hrsp, hrip, hval, hexeP, hlesP, hschrP⟩ :=
    geholt_verschachtelt_wiederhergestellt s1 b1 b2 b3 b4 disp src dst sc sp sq sr
      mc mp vp vr hwinc hexec hwrc hlesc hstepc hwinp hexep hwrp hlesp hstepp
      hrdp hstepq hdst hwinq hexeq hrdr hstepr hwinr hexer hdis
  have hrun : laufBytes (proLen + 4) s0 = .weiter b4 := by
    rw [laufBytes_add proLen 4 s0 s1 hpro]
    simp only [laufBytes, hb1, hb2, hb3, hb4]
  have hlenC : laengeOk (encode (.call32 disp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have eC := schritt_call32_erfolg ⟨.call32 disp, (encode (.call32 disp)).length⟩
    s1 disp mc hlenC rfl hwrc
  rw [hstepc] at eC
  have hsrc1 : b1.register src = s1.register src := by
    cases eC
    simp [schrittCall, regSet, hsrc]
  exact ⟨hrun, by rw [hrsp, hrsp0], hrip, by rw [hval, hsrc1], hexeP, hlesP, hschrP⟩

open Gabbro.Grammatik.X86.PipelineImage

/-- THE LINKAGE: ENTRY REPRESENTATION REACHES THE FRAGMENT HEAD. From an
    admitted entry (`prologImageOk`, the caller's `AbiArgs` duty) followed
    by one fetched call/push/pop/ret nest whose two stack slots are foreign
    to every placed slot (`StapelLayoutFremd`) and whose clobbered
    registers (`rsp`, `dst`) hold no variable, the byte run reaches the
    fragment-head state with the entry world still represented and every
    variable still in its pipeline register. `EnvRepr` is ESTABLISHED by
    the fetched entry sequence (`prolog_lauf`), not assumed; `WorldRep`
    crosses the two frame writes by the foreign-store frame, and the
    pop/ret memory passthrough is derived from the accepted success
    lemmas. -/
theorem byteKopf_antwortErhalten {D : Deklaration} {Γ : Ctx}
    (L : Layout D) (c : PipeCfg) (bild : Bild) (abi : List Register)
    (ρ : Env D Γ) (σE : World D)
    (s0 s1 b1 b2 b3 b4 : Zustand)
    (disp : BitVec 32) (src dst : Register)
    (sc sp sq sr : List Byte)
    (mc mp : Speicher) (vp vr : Wort)
    (hproImg : prologImageOk bild c abi Γ.length = true)
    (hs : s0.speicher = ladung bild)
    (hrip : s0.rip = natAdresse (c.codeBase - (encodeAll (prolog c abi Γ.length)).length))
    (hargs : AbiArgs abi ρ s0.register)
    (hpro : laufBytes (prolog c abi Γ.length).length s0 = .weiter s1)
    (hW0 : WorldRep L s0.speicher σE)
    (hfremd : StapelLayoutFremd L (s1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register Register.rsp - BitVec.ofNat 64 8))
    (hvar : ∀ (τ : Ty) (x : Var Γ τ), abbOf c τ x ≠ Register.rsp ∧ abbOf c τ x ≠ dst)
    (hwinc : StapelGeholt s1 (.call32 disp) sc)
    (hexec : ausfuehrbarN s1.speicher s1.rip
      (encode (.call32 disp)).length = true)
    (hwrc : write64 s1.speicher (s1.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s1.rip (encode (.call32 disp)).length) = some mc)
    (hlesc : lesbar8 s1.speicher
      (s1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepc : schritt ⟨.call32 disp, (encode (.call32 disp)).length⟩ s1 =
      some b1)
    (hwinp : StapelGeholt b1 (.push64 src) sp)
    (hexep : ausfuehrbarN b1.speicher b1.rip
      (encode (.push64 src)).length = true)
    (hwrp : write64 b1.speicher (b1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register src) = some mp)
    (hlesp : lesbar8 b1.speicher
      (b1.register Register.rsp - BitVec.ofNat 64 8) = true)
    (hstepp : schritt ⟨.push64 src, (encode (.push64 src)).length⟩ b1 =
      some b2)
    (hrdp : read64 b2.speicher (b2.register Register.rsp) = some vp)
    (hstepq : schritt ⟨.pop64 dst, (encode (.pop64 dst)).length⟩ b2 =
      some b3)
    (hdst : dst ≠ Register.rsp)
    (hsrc : src ≠ Register.rsp)
    (hwinq : StapelGeholt b2 (.pop64 dst) sq)
    (hexeq : ausfuehrbarN b2.speicher b2.rip
      (encode (.pop64 dst)).length = true)
    (hrdr : read64 b3.speicher (b3.register Register.rsp) = some vr)
    (hstepr : schritt ⟨.ret, (encode .ret).length⟩ b3 = some b4)
    (hwinr : StapelGeholt b3 .ret sr)
    (hexer : ausfuehrbarN b3.speicher b3.rip
      (encode .ret).length = true)
    (hdis : Disjunkt (s1.register Register.rsp - BitVec.ofNat 64 8)
      (b1.register Register.rsp - BitVec.ofNat 64 8)) :
    ∃ b4', laufBytes ((prolog c abi Γ.length).length + 4) s0 = .weiter b4' ∧
      WorldRep L b4'.speicher σE ∧ EnvRepr ρ b4'.register (abbOf c) ∧
      b4'.register Register.rsp = s0.register Register.rsp := by
  obtain ⟨s1', hrunP', -, hmemP, hrspP, hE1⟩ :=
    prolog_lauf bild c abi ρ hproImg s0 hs hrip hargs
  have hpro2 := hpro
  rw [hrunP'] at hpro2
  cases hpro2
  have hW1 : WorldRep L s1.speicher σE := by
    rw [hmemP, ← hs]
    exact hW0
  have hlenC : laengeOk (encode (.call32 disp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlenP : laengeOk (encode (.push64 src)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlenQ : laengeOk (encode (.pop64 dst)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hlenR : laengeOk (encode .ret).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have eC := schritt_call32_erfolg ⟨.call32 disp, (encode (.call32 disp)).length⟩
    s1 disp mc hlenC rfl hwrc
  rw [hstepc] at eC
  have eCeq := Option.some.inj eC
  have eP := schritt_push64_erfolg ⟨.push64 src, (encode (.push64 src)).length⟩
    b1 src mp hlenP rfl hwrp
  rw [hstepp] at eP
  have ePeq := Option.some.inj eP
  have eQ := schritt_pop64_reg ⟨.pop64 dst, (encode (.pop64 dst)).length⟩
    b2 dst vp hlenQ rfl hdst hrdp
  rw [hstepq] at eQ
  have eQeq := Option.some.inj eQ
  have eR := schritt_ret_erfolg ⟨.ret, (encode .ret).length⟩ b3 vr hlenR rfl hrdr
  rw [hstepr] at eR
  have eReq := Option.some.inj eR
  have hm1 : b1.speicher = mc := by rw [eCeq]; rfl
  have hm2 : b2.speicher = mp := by rw [ePeq]; rfl
  have hm3 : b3.speicher = b2.speicher := by rw [eQeq]; rfl
  have hm4 : b4.speicher = b3.speicher := by rw [eReq]; rfl
  have hfC : ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
      L.loc t k f = some a0 →
        Disjunkt (s1.register Register.rsp - BitVec.ofNat 64 8) (natAdresse a0) :=
    fun t k f a0 h => (hfremd t k f a0 h).1
  have hfP : ∀ (t : D.Tab) (k : Int) (f : D.Feld t) (a0 : Nat),
      L.loc t k f = some a0 →
        Disjunkt (b1.register Register.rsp - BitVec.ofNat 64 8) (natAdresse a0) :=
    fun t k f a0 h => (hfremd t k f a0 h).2
  have hWb1 : WorldRep L b1.speicher σE := by
    rw [hm1]
    exact worldRep_schreiben_fremd L s1.speicher mc σE _ _ hW1 hwrc hfC
  have hWb2 : WorldRep L b2.speicher σE := by
    rw [hm2]
    exact worldRep_schreiben_fremd L b1.speicher mp σE _ _ hWb1 hwrp hfP
  have hWb4 : WorldRep L b4.speicher σE := by
    rw [hm4, hm3]
    exact hWb2
  have k1 : ∀ q : Register, q ≠ Register.rsp → b1.register q = s1.register q := by
    intro q hq
    rw [eCeq]
    show regSet s1.register Register.rsp _ q = s1.register q
    unfold regSet
    rw [if_neg hq]
  have k2 : ∀ q : Register, q ≠ Register.rsp → b2.register q = b1.register q := by
    intro q hq
    rw [ePeq]
    show regSet b1.register Register.rsp _ q = b1.register q
    unfold regSet
    rw [if_neg hq]
  have k3 : ∀ q : Register, q ≠ Register.rsp → q ≠ dst →
      b3.register q = b2.register q := by
    intro q hq1 hq2
    rw [eQeq]
    show regSet (regSet b2.register Register.rsp _) dst _ q = b2.register q
    unfold regSet
    rw [if_neg hq2, if_neg hq1]
  have k4 : ∀ q : Register, q ≠ Register.rsp → b4.register q = b3.register q := by
    intro q hq
    rw [eReq]
    show regSet b3.register Register.rsp _ q = b3.register q
    unfold regSet
    rw [if_neg hq]
  have hkeep : ∀ q : Register, q ≠ Register.rsp → q ≠ dst →
      b4.register q = s1.register q := by
    intro q hq1 hq2
    rw [k4 q hq1, k3 q hq1 hq2, k2 q hq1, k1 q hq1]
  have hEnv4 : EnvRepr ρ b4.register (abbOf c) :=
    envRepr_fremd _ _ _ _ hE1 (fun τ x => hkeep _ (hvar τ x).1 (hvar τ x).2)
  obtain ⟨hrun, hrspB, -, -, -, -, -⟩ := eintrittCallPrefix_lauf s0 s1 b1 b2 b3 b4
    (prolog c abi Γ.length).length disp src dst sc sp sq sr mc mp vp vr
    hpro hrspP hwinc hexec hwrc hlesc hstepc hwinp hexep hwrp hlesp hstepp
    hrdp hstepq hdst hsrc hwinq hexeq hrdr hstepr hwinr hexer hdis
  exact ⟨b4, hrun, hWb4, hEnv4, hrspB⟩
/-- REFUSAL (guard slot): actual call bytes fetch, but the
    return-address store below the top hits a write-protected guard, so the
    byte step loudly refuses. Every premise is consumed by the accepted
    guard-refusal theorem. -/
theorem eintrittCall_verweigert_wache (s : Zustand) (disp : BitVec 32)
    (suffix : List Byte)
    (hwin : StapelGeholt s (.call32 disp) suffix)
    (hexe : ausfuehrbarN s.speicher s.rip
      (encode (.call32 disp)).length = true)
    (hguard : schreibbar8 s.speicher
      (s.register Register.rsp - BitVec.ofNat 64 8) = false) :
    byteschritt s = .verweigert :=
  byteschritt_geholt_call_wache s disp suffix hwin hexe hguard

/-- REFUSAL (non-executable return): an actual return byte steps to the
    popped target, but the target carries no execute permission, so the
    following byte step loudly refuses. -/
theorem eintrittCall_verweigert_ret_nicht_ausfuehrbar (s s' : Zustand)
    (suffix : List Byte) (ziel : Wort)
    (hwin : StapelGeholt s .ret suffix)
    (hexe : ausfuehrbarN s.speicher s.rip (encode .ret).length = true)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : byteschritt s = .weiter s')
    (hxe : s.speicher.ausfuehrbar ziel = false) :
    byteschritt s' = .verweigert :=
  byteschritt_geholt_ret_nicht_ausfuehrbar s s' suffix ziel hwin hexe hrd hstep hxe

/-- REFUSAL (clobbering entry): two entry copies that interfere (the
    earlier destination is a later source or destination) fail the decided
    entry check, so no `EnvRepr` is established from this ABI. -/
theorem eintrittProlog_verweigert_ohne_frisch (c : PipeCfg) (abi : List Register)
    (n : Nat) (h : ¬ (prologPaare c abi n).Pairwise ZugOk) :
    prologOk c abi n = false := by
  cases hok : prologOk c abi n
  · rfl
  · exact absurd (prologOk_teile c abi n hok).1 h

/-- POISON (guard slot): the guard witness fetches actual call bytes and
    loudly refuses the return-address store. -/
theorem gift_wache_verweigert : byteschritt wacheNestS = .verweigert :=
  byteschritt_geholt_call_wache _ _ _ wacheNest_geholt wacheNest_exe wacheNest_guard

/-- POISON (non-executable return): the return witness steps to a popped
    target without execute permission, and the next byte step refuses. -/
theorem gift_ret_verweigert :
    ∃ (s s' : Zustand), byteschritt s = .weiter s' ∧ byteschritt s' = .verweigert := by
  have hstep := byteschritt_geholt_ret _ _ _ retNest_geholt retNest_exe retNest_liest
  exact ⟨retNestS, _, hstep,
    byteschritt_geholt_ret_nicht_ausfuehrbar _ _ _ _ retNest_geholt retNest_exe
      retNest_liest hstep retNest_kein_exec⟩

/-- POISON (clobbering entry): two parameters aimed at one pipeline
    register fail the decided entry check. -/
def giftPrologCfg : PipeCfg :=
  { regs := [.rbx, .rbx], dst := .rax, tmp := .rcx, adr := .rdx,
    codeBase := 4096, exitBase := 12288 }

theorem gift_prolog_clobber_grund :
    ¬ (prologPaare giftPrologCfg [.rax, .rcx] 2).Pairwise ZugOk := by
  decide

theorem gift_prolog_clobber : prologOk giftPrologCfg [.rax, .rcx] 2 = false :=
  eintrittProlog_verweigert_ohne_frisch _ _ _ gift_prolog_clobber_grund

/-- JOINT WITNESS (start-anchored entry/call linkage): the source-level
    prefix from the start anchor reaches its fragment head on the accepted
    witness program (a table `setze` writes, start world `konto[0] = 0`,
    logged entry world `konto[0] = 5`), AND the byte-level entry/call
    prefix runs four fetched steps whose call frame is written and restored
    through memory (return word below the old top reads back, the same byte
    differs from the pre-state, the stack pointer is restored). The
    identity of the two heads (a lowering certificate `eP` to bytes) stays
    OPEN in CUTS; proved here is joint reachability with an observably
    changed, restored frame. -/
theorem eintrittCallPrefix_zeuge :
    (∃ M : RufMaschineG eD,
      RufErreichbarG eP eO 0 startAnker M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ∃ (rho : Env eD (eD.params ePruefe)) (ws : World eD),
        RufEreignisF.eintritt ePruefe rho ws ∈ (M.faeden 0).log ∧
        (ws.slots () 0 ()).n = 5) ∧
    (∃ (s0 s4 : Zustand),
      laufBytes 4 s0 = .weiter s4 ∧
      s4.register Register.rsp = s0.register Register.rsp ∧
      s4.rip = ripNach s0.rip (encode (.call32 nestDisp)).length ∧
      read64 s4.speicher (s0.register Register.rsp - BitVec.ofNat 64 8) =
        some (ripNach s0.rip (encode (.call32 nestDisp)).length) ∧
      s0.speicher.bytes (s0.register Register.rsp - BitVec.ofNat 64 8) ≠
        s4.speicher.bytes (s0.register Register.rsp - BitVec.ofNat 64 8)) := by
  obtain ⟨M, hr, h0, hwr, rho, ws, hm, -, h5⟩ := startFragment_zeuge
  have hrA : RufErreichbarG eP eO 0 startAnker M := by
    rw [startAnker_gleich]
    exact hr
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
  have hlenC0 : laengeOk (encode (.call32 nestDisp)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hstepc0 : schritt
      (⟨.call32 nestDisp, (encode (.call32 nestDisp)).length⟩ : Decodiert)
      nestS0 = some nestS1 :=
    schritt_call32_erfolg _ _ _ _ hlenC0 rfl hwrc0
  have hwrp0 : write64 nestS1.speicher
      (nestS1.register Register.rsp - BitVec.ofNat 64 8)
      (nestS1.register Register.rax) = some nestMp := by
    rw [nest_rsp1]
    exact nest_push_schreibt
  have hlesp0 : lesbar8 nestS1.speicher
      (nestS1.register Register.rsp - BitVec.ofNat 64 8) = true := by
    rw [nest_rsp1]
    exact nest_obenp_lesbar
  have hlenP0 : laengeOk (encode (.push64 .rax)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hstepp0 : schritt
      (⟨.push64 .rax, (encode (.push64 .rax)).length⟩ : Decodiert)
      nestS1 = some nestS2 :=
    schritt_push64_erfolg _ _ _ _ hlenP0 rfl hwrp0
  have hlenQ0 : laengeOk (encode (.pop64 .rbx)).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hstepq0 : schritt
      (⟨.pop64 .rbx, (encode (.pop64 .rbx)).length⟩ : Decodiert)
      nestS2 = some nestS3 :=
    schritt_pop64_reg _ _ _ _ hlenQ0 rfl (by decide) nest_push_liest
  have hlenR0 : laengeOk (encode .ret).length = true := by
    unfold laengeOk
    simp only [decide_eq_true_eq]
    exact encode_len _
  have hstepr0 : schritt
      (⟨.ret, (encode .ret).length⟩ : Decodiert)
      nestS3 = some nestS4 :=
    schritt_ret_erfolg _ _ _ hlenR0 rfl nest_ret_liest
  obtain ⟨hrun, hrsp, hrip, -, -, -, -⟩ := eintrittCallPrefix_lauf
    nestS0 nestS0 nestS1 nestS2 nestS3 nestS4 0 nestDisp .rax .rbx _ _ _ _
    nestM1 nestMp 42 (ripNach nestS0.rip 5) rfl rfl
    nest_call_geholt nest_call_exe hwrc0 hlesc0 hstepc0
    nest_push_geholt nest_push_exe hwrp0 hlesp0 hstepp0
    nest_push_liest hstepq0 (by decide) (by decide)
    nest_pop_geholt nest_pop_exe nest_ret_liest hstepr0
    nest_ret_geholt nest_ret_exe nest_slots_disjunkt
  have hrun4 : laufBytes 4 nestS0 = .weiter nestS4 := hrun
  have hdisPN : Disjunkt nestObenP nestOben0 := by
    have h := nest_slots_disjunkt
    rw [nest_rsp0, nest_rsp1] at h
    intro i j hi hj
    exact Ne.symm (h j i hj hi)
  have hmem4 : nestS4.speicher = nestMp := rfl
  have hread : read64 nestS4.speicher
      (nestS0.register Register.rsp - BitVec.ofNat 64 8) =
      some (ripNach nestS0.rip (encode (.call32 nestDisp)).length) := by
    rw [nest_rsp0, hmem4,
      read64_rahmen nestM1 nestMp nestObenP nestOben0 _ nest_push_schreibt hdisPN]
    exact read64_nach_write64 _ _ _ _ nest_call_schreibt nest_oben0_lesbar
  have hframe : nestMp.bytes nestOben0 = nestM1.bytes nestOben0 := by
    apply write64_rahmen nestM1 nestMp nestObenP nestOben0 _ nest_push_schreibt
    intro k hk
    have hne := hdisPN k 0 hk (by decide)
    rw [addrOff_null] at hne
    exact Ne.symm hne
  have hmem : nestS0.speicher.bytes
      (nestS0.register Register.rsp - BitVec.ofNat 64 8) ≠
      nestS4.speicher.bytes
        (nestS0.register Register.rsp - BitVec.ofNat 64 8) := by
    rw [nest_rsp0, hmem4, hframe]
    have hhit := writeBytesN_hit nestSpeicher nestOben0 (ripNach nestS0.rip 5) 8 0
      (by decide) (by decide)
    rw [addrOff_null] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes nestSpeicher nestOben0 (ripNach nestS0.rip 5) nestOben0
    unfold writeBytes
    rw [hhit]
    decide
  exact ⟨⟨M, hrA, h0, hwr, rho, ws, hm, h5⟩,
    nestS0, nestS4, hrun4, hrsp, hrip, hread, hmem⟩

/- CUTS (exactly what is NOT proved here):
   Proved here:
   - `StapelLayoutFremd`: the admission predicate (both stack slots foreign
     to every placed slot).
   - `worldRep_schreiben_fremd`: one foreign word store keeps `WorldRep`.
   - `eintrittCallPrefix_lauf`: entry run plus one fetched call/push/pop/ret
     nest reaches the fragment-head byte state (stack pointer restored,
     next-`rip` return word, inner value delivered, permissions kept).
   - `byteKopf_antwortErhalten`: from an admitted entry the head state keeps
     the entry world represented and every variable in its register.
   - `eintrittCall_verweigert_wache/_ret_nicht_ausfuehrbar`: guard slot and
     non-executable return refuse loudly.
   - `eintrittProlog_verweigert_ohne_frisch`: interfering entry copies fail
     the decided check.
   - Poison probes `gift_wache_verweigert`, `gift_ret_verweigert`,
     `gift_prolog_clobber` (with `giftPrologCfg`,
     `gift_prolog_clobber_grund`).
   - `eintrittCallPrefix_zeuge`: joint source-head and byte-head reachability
     with a call frame written and restored through memory.
   NOT proved here, and not claimed:
   - No lowering certificate from the source program `eP` to bytes: the
     identity of the source fragment head with the byte head is OPEN with
     the pipeline owners. Proved here is co-reachability plus transport.
   - No TSO/GX bridge: every fact is sequential over one canonical
     `Speicher`; store buffers, forwarding and GX refinement stay with the
     TSO work (`TsoGxRefine` is reused by reference only through
     `TsoGxStart`).
   - One call nest only (call/push/pop/ret, `dst ≠ rsp`, `src ≠ rsp`,
     disjoint slots); deeper nesting, callee-saved registers, stack-passed
     or float/pointer/aggregate parameters, and interrupts or guard-page
     behaviour beyond the two planted refusals are refused or open.
   - Pilot ISA, one core, model memory, no time (cuts of the reused modules).
-/

#print axioms StapelLayoutFremd
#print axioms worldRep_schreiben_fremd
#print axioms eintrittCallPrefix_lauf
#print axioms byteKopf_antwortErhalten
#print axioms eintrittCall_verweigert_wache
#print axioms eintrittCall_verweigert_ret_nicht_ausfuehrbar
#print axioms eintrittProlog_verweigert_ohne_frisch
#print axioms gift_wache_verweigert
#print axioms gift_ret_verweigert
#print axioms giftPrologCfg
#print axioms gift_prolog_clobber_grund
#print axioms gift_prolog_clobber
#print axioms eintrittCallPrefix_zeuge

end Gabbro.Grammatik.X86.TsoGxEntryBytes
