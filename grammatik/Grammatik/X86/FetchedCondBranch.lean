/-
  File:      Grammatik/X86/FetchedCondBranch.lean
  Subject:   Fetched conditional byte-step flag dependency simulation.

  Lane 656 (connection): lifts `FlagDependencies.jccSchritt_stabil` and the
  per-condition read sets (`liestFlag` / `stimmtUebberein`) to the actual
  `Byteschritt.fetchDekodiert` / `byteschritt` path. Fetch/decode identity
  is DERIVED from equal actual code bytes, execute map and RIP (never
  assumed); agreement on exactly the consumed flags then suffices for the
  same branch outcome and next RIP. One `ConditionalMove.cmovLowerOk`
  lowering admission and the `InstructionSelection.wahlOk` refusal are
  connected to this byte-level rule; the `BranchLayout` carried length is
  tied to the fetched length. CMOVcc/SETcc stay on their real
  `ControlCodec` byte helpers (no `fetchDekodiert` path exists for them).
  No new executor, no new source condition language, no new decoder.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Codec
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.FlagDependencies
import Grammatik.X86.ControlCodec
import Grammatik.X86.ConditionalMove
import Grammatik.X86.BranchLayout
import Grammatik.X86.InstructionSelection
import Grammatik.X86.SourceCodeFrame

namespace Gabbro.Grammatik.X86

/-- Witness displacement of the fetched conditional jump (`je +16`). -/
def fjDisp : BitVec 32 := BitVec.ofNat 32 16

/-- Witness code bytes: the canonical `je +16` encoding at 4096, zero
    elsewhere. Actual `encode` output, never a hand-written byte. -/
def fjBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else (encode (.jumpIf32 .e fjDisp)).getD (a.toNat - 4096) (BitVec.ofNat 8 0)

/-! ## 2. Fetch identity from equal actual code, map and RIP.

    `geholt` reads only `speicher.bytes`, `speicher.ausfuehrbar` and
    `rip`; `fetchDekodiert` adds only `decode`, `laengeOk` and
    `ausfuehrbarN` over the same data. Equal code/map/RIP therefore
    gives equal fetch and equal decode outcome: no second execution is
    assumed identical, the identity is derived. -/

/-- Fetch-window identity: equal code bytes and execute map at equal
    RIP fetch the same window. Every premise is used. -/
theorem holeFetchAux_gleich (mF mG : Speicher) (aF aG : Adresse)
    (off n : Nat)
    (hrip : aF = aG)
    (hbytes : ∀ a, mF.bytes a = mG.bytes a)
    (hexe : ∀ a, mF.ausfuehrbar a = mG.ausfuehrbar a) :
    holeFetchAux mF aF off n = holeFetchAux mG aG off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have haddr : addrOff aF off = addrOff aG off := by rw [hrip]
    have he : mF.ausfuehrbar (addrOff aF off) =
        mG.ausfuehrbar (addrOff aG off) := by
      rw [haddr]
      exact hexe _
    have hb : mF.bytes (addrOff aF off) =
        mG.bytes (addrOff aG off) := by
      rw [haddr]
      exact hbytes _
    simp only [holeFetchAux, he, hb, ih]

/-- State-window identity from equal code, map and RIP. -/
theorem geholt_gleich (sF sG : Zustand)
    (hrip : sF.rip = sG.rip)
    (hbytes : ∀ a, sF.speicher.bytes a = sG.speicher.bytes a)
    (hexe : ∀ a, sF.speicher.ausfuehrbar a = sG.speicher.ausfuehrbar a) :
    geholt sF = geholt sG := by
  unfold geholt
  exact holeFetchAux_gleich sF.speicher sG.speicher sF.rip sG.rip
    0 fetchCap hrip hbytes hexe

/-- Fetch-and-decode identity: equal code, map and RIP decode the same
    way. The `decode` scrutinee is rewritten by `geholt_gleich` and
    the consumed-prefix check by `ausfuehrbarN_gleich`; both
    `fetchDekodiert` copies then agree. Every premise is used. -/
theorem fetchDekodiert_gleich (sF sG : Zustand)
    (hrip : sF.rip = sG.rip)
    (hbytes : ∀ a, sF.speicher.bytes a = sG.speicher.bytes a)
    (hexe : ∀ a, sF.speicher.ausfuehrbar a = sG.speicher.ausfuehrbar a) :
    fetchDekodiert sF = fetchDekodiert sG := by
  have hg : geholt sF = geholt sG :=
    geholt_gleich sF sG hrip hbytes hexe
  have hperm : sF.speicher.ausfuehrbar = sG.speicher.ausfuehrbar :=
    funext hexe
  have hex : ∀ n, ausfuehrbarN sF.speicher sF.rip n =
      ausfuehrbarN sG.speicher sG.rip n := by
    intro n
    rw [hrip]
    exact ausfuehrbarN_gleich sG.speicher sF.speicher hperm _ n
  unfold fetchDekodiert
  rw [hg]
  cases hdec : decode (geholt sG) with
  | none => rfl
  | some pr =>
    obtain ⟨d, rest⟩ := pr
    simp only [hex]

/-! ## 3. Fetched conditional-jump stability on consumed flags only.

    The main consumer theorem: where `fetchDekodiert` produces a
    conditional jump from ACTUAL fetched bytes, two states with equal
    code, map and RIP that agree on exactly the flags the decoded
    condition reads take the same `byteschritt` successor RIP. Neither
    execution is assumed identical: the second fetch is derived by
    `fetchDekodiert_gleich`, the decoded length by
    `decodeJumpIf_laenge` through the accepted coverage shape, and the
    successor agreement by the accepted `jccSchritt_stabil`. -/

/-- Agreement on the flags read by a FETCHED conditional jump implies
    the same executed successor RIP, the same branch outcome, the same
    derived fetch on the second state, and the same `byteschritt`
    outcomes. Every premise is used: `hFfetch` supplies the actual
    decode and the first byte step, `hbef` fixes the decoded shape,
    `hrip`/`hbytes`/`hexe` derive the second fetch, `hfl` aligns the
    conditions, `hF`/`hG` are the two accepted steps. -/
theorem fetchedJcc_stabil (sF sG sF' sG' : Zustand) (d : Decodiert)
    (rest : List Byte) (c : Bedingung) (disp : BitVec 32)
    (hFfetch : fetchDekodiert sF = some (d, rest))
    (hbef : d.befehl = .jumpIf32 c disp)
    (hrip : sF.rip = sG.rip)
    (hbytes : ∀ a, sF.speicher.bytes a = sG.speicher.bytes a)
    (hexe : ∀ a, sF.speicher.ausfuehrbar a = sG.speicher.ausfuehrbar a)
    (hfl : stimmtUebberein c sF.flags sG.flags)
    (hF : schritt d sF = some sF')
    (hG : schritt d sG = some sG') :
    sF'.rip = sG'.rip ∧ bedingung c sF.flags = bedingung c sG.flags ∧
      fetchDekodiert sG = some (d, rest) ∧
      byteschritt sF = .weiter sF' ∧ byteschritt sG = .weiter sG' := by
  have heq := fetchDekodiert_gleich sF sG hrip hbytes hexe
  have hGfetch : fetchDekodiert sG = some (d, rest) := heq ▸ hFfetch
  obtain ⟨hdecF, _, _, _⟩ := fetchDekodiert_entspricht sF d rest hFfetch
  obtain ⟨b, len⟩ := d
  dsimp only at hbef
  subst hbef
  have hbed : bedingung c sF.flags = bedingung c sG.flags :=
    bedingung_stabil c sF.flags sG.flags hfl
  have hrips : sF'.rip = sG'.rip :=
    jccSchritt_stabil (geholt sF) rest c disp len sF sG sF' sG'
      hdecF hrip hfl hF hG
  have hbsF : byteschritt sF = .weiter sF' :=
    byteschritt_weiter sF sF' _ rest hFfetch hF
  have hbsG : byteschritt sG = .weiter sG' :=
    byteschritt_weiter sG sG' _ rest hGfetch hG
  exact ⟨hrips, hbed, hGfetch, hbsF, hbsG⟩

/-- The fetched conditional-jump length is the carried layout length:
    `decodeJumpIf_laenge` fixes six actual bytes and
    `BranchLayout.zweigLaenge_codec_jumpIf32` carries the same six, so
    a `ZweigBeleg` with `len = zweigLaenge true .weit` checks the
    actual fetched bytes. Every premise is used. -/
theorem fetchedJcc_len_layout (sF : Zustand) (d : Decodiert)
    (rest : List Byte) (c : Bedingung) (disp : BitVec 32)
    (hfetch : fetchDekodiert sF = some (d, rest))
    (hbef : d.befehl = .jumpIf32 c disp) :
    d.laenge = zweigLaenge true .weit := by
  obtain ⟨hdecF, _, _, _⟩ := fetchDekodiert_entspricht sF d rest hfetch
  obtain ⟨b, len⟩ := d
  dsimp only at hbef
  subst hbef
  have hlen : len = 6 :=
    decodeJumpIf_laenge c disp len (geholt sF) rest hdecF
  have h6 : zweigLaenge true .weit = 6 := rfl
  rw [hlen, h6]

/-! ## 4. Lowering connections at byte level.

    One `ConditionalMove.cmovLowerOk` admission implies the byte-step
    select stability (the admission carries checked length and flag
    identity, hence read-set agreement for every condition); the
    `InstructionSelection.wahlOk` refusal of a clobbering `xor` under
    live flags is load-bearing because the two choices take different
    fetched branch successors (`zweig_weicht_ab` lifted to `schritt`
    RIPs). CMOVcc/SETcc stay on their real `ControlCodec` byte
    helpers: for condition `.e` only ZF is consumed, so same ZF plus
    same registers give the same selected value with every other flag
    free; length 0 refuses both steps. -/

/-- An admitted `cmovLowerOk` lowering selects the same destination
    word at byte level: the admission guarantees checked length and
    flag identity, and identity implies read-set agreement for every
    condition. Every premise is used. -/
theorem cmovLower_fetched_stabil (d : Decodiert) (len : Nat)
    (sF sG sF' sG' : Zustand) (dst src : Register) (c : Bedingung)
    (hlen : d.laenge = len)
    (hadmin : cmovLowerOk d sF.flags sG.flags = true)
    (hregs : ∀ q, sF.register q = sG.register q)
    (hF : cmovSchrittBytes len sF dst src c = some sF')
    (hG : cmovSchrittBytes len sG dst src c = some sG') :
    sF'.register dst = sG'.register dst := by
  obtain ⟨hokD, heq⟩ := cmovLowerOk_garantiert d sF.flags sG.flags hadmin
  have hok : laengeOk len = true := hlen ▸ hokD
  have hfl : stimmtUebberein c sF.flags sG.flags := by
    intro n _
    rw [heq]
  exact cmovBytes_stabil len sF sG sF' sG' dst src c hok hfl hregs hF hG

/-- The `wahlOk` refusal is load-bearing at step level: with a clear
    zero flag the preserving choice falls through while the
    clobbering `xor` (whose flags the selector would expose) takes
    the same fetched `je`, so the fetched successors differ. Reuses
    `Anweisungswahl.zweig_weicht_ab` for the condition values and the
    accepted `schritt` equations for the RIPs. Every premise is used. -/
theorem wahlOk_fetched_notwendig (s : Zustand) (dst : Register)
    (hdead : s.flags.zf = false)
    (hok : laengeOk 6 = true) :
    (schritt (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert) s).map
        (fun t => t.rip) = some (ripNach s.rip 6) ∧
      (schritt (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert)
          { s with flags := (xor64 (s.register dst)
            (s.register dst)).2 }).map (fun t => t.rip) =
        some (ripNach s.rip 6 + dispWort (BitVec.ofNat 32 16)) := by
  obtain ⟨hfall, htake⟩ :=
    Anweisungswahl.zweig_weicht_ab s dst hdead
  have hF := schritt_jumpIf32_nicht
    (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert) s .e _ hok
    rfl hfall
  have hG := schritt_jumpIf32_genommen
    (⟨.jumpIf32 .e (BitVec.ofNat 32 16), 6⟩ : Decodiert)
    { s with flags := (xor64 (s.register dst) (s.register dst)).2 }
    .e _ hok rfl htake
  rw [hF, hG]
  exact ⟨rfl, rfl⟩

/-- CMOVcc under `.e` reads only ZF: same zero flag and same
    registers give the same selected word; every other flag
    (CF/PF/AF/SF/OF) may differ arbitrarily. Every premise is used. -/
theorem cmov_e_unverbraucht_stabil (sF sG sF' sG' : Zustand)
    (dst src : Register)
    (hzf : sF.flags.zf = sG.flags.zf)
    (hregs : ∀ q, sF.register q = sG.register q)
    (hok : laengeOk 4 = true)
    (hF : cmovSchrittBytes 4 sF dst src .e = some sF')
    (hG : cmovSchrittBytes 4 sG dst src .e = some sG') :
    sF'.register dst = sG'.register dst := by
  have hfl : stimmtUebberein .e sF.flags sG.flags := by
    intro n hn
    cases n with
    | cf => exact absurd hn (by decide)
    | pf => exact absurd hn (by decide)
    | zf => exact hzf
    | sf => exact absurd hn (by decide)
    | of_ => exact absurd hn (by decide)
  exact cmovBytes_stabil 4 sF sG sF' sG' dst src .e hok hfl hregs hF hG

/-- SETcc under `.e` reads only ZF: same zero flag and same
    destination word give the same selected low byte. -/
theorem setcc_e_unverbraucht_stabil (sF sG sF' sG' : Zustand)
    (dst : Register)
    (hzf : sF.flags.zf = sG.flags.zf)
    (hregs : sF.register dst = sG.register dst)
    (hok : laengeOk 4 = true)
    (hF : setccSchrittBytes 4 sF dst .e = some sF')
    (hG : setccSchrittBytes 4 sG dst .e = some sG') :
    sF'.register dst = sG'.register dst := by
  have hfl : stimmtUebberein .e sF.flags sG.flags := by
    intro n hn
    cases n with
    | cf => exact absurd hn (by decide)
    | pf => exact absurd hn (by decide)
    | zf => exact hzf
    | sf => exact absurd hn (by decide)
    | of_ => exact absurd hn (by decide)
  exact setccBytes_stabil 4 sF sG sF' sG' dst .e hok hfl hregs hF hG

/-- Length refusal for both conditional-select byte steps: length 0
    is no valid decoding, so neither step runs. -/
theorem cmov_setcc_len0_verweigert (s : Zustand) (dst src : Register)
    (c : Bedingung) :
    cmovSchrittBytes 0 s dst src c = none ∧
      setccSchrittBytes 0 s dst c = none := by
  have h0 : laengeOk 0 = false := by decide
  have hc : cmovSchrittBytes 0 s dst src c = none := by
    unfold cmovSchrittBytes
    rw [h0]
  have hs : setccSchrittBytes 0 s dst c = none := by
    unfold setccSchrittBytes
    rw [h0]
  exact ⟨hc, hs⟩

/-! ## 5. Witness states: one fetched `je` over actual bytes.

    Six executable bytes hold the canonical `je +16` at 4096; the
    data cell at 8192 is readable and writable. `fjTaken` has ZF set,
    `fjAnder` agrees on ZF with every other flag flipped (CF/SF/OF
    set, PF clear, AF undefined), `fjAf` differs in AF alone,
    `fjFall` has ZF clear. Truncated, execute-denied and forged
    variants refuse. -/

/-- Code window executable: exactly the six `je` bytes at 4096. -/
def fjExec6 (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4102)

/-- Data cell readable and writable: 8192..8200. -/
def fjDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8200)

/-- Witness memory: the fetched `je` at 4096, the data cell at 8192. -/
def fjSpeicher : Speicher :=
  { bytes := fjBytes
    lesbar := fjDaten
    schreibbar := fjDaten
    ausfuehrbar := fjExec6 }

/-- Witness registers: `rax` holds 42, the stack top sits at 8192. -/
def fjReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 42
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Taken state: zero flag set over the fetched `je`. -/
def fjTaken : Zustand :=
  { register := fjReg, flags := zeugeFlagsGleich,
    rip := BitVec.ofNat 64 4096, speicher := fjSpeicher }

/-- Same consumed flag (ZF set), every other flag flipped. -/
def fjAnder : Zustand :=
  { register := fjReg, flags := ⟨true, false, none, true, true, true⟩,
    rip := BitVec.ofNat 64 4096, speicher := fjSpeicher }

/-- AF alone differs (undefined instead of `some false`). -/
def fjAf : Zustand :=
  { fjTaken with flags := { zeugeFlagsGleich with af := none } }

/-- Consumed-flag mutation: zero flag clear. -/
def fjFall : Zustand :=
  { register := fjReg, flags := zeugeFlags,
    rip := BitVec.ofNat 64 4096, speicher := fjSpeicher }

/-- Truncated variant: only five of the six `je` bytes executable. -/
def fjStumpf : Zustand :=
  { fjTaken with speicher := { fjSpeicher with
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4101) } }

/-- Execute-denied variant: the `je` bytes are not executable. -/
def fjOhneExec : Zustand :=
  { fjTaken with speicher := { fjSpeicher with
    ausfuehrbar := fun _ => false } }

/-- Forged variant: the second `je` byte reads `0x90` (outside the
    `0x80..0x8F` conditional-jump range), so no pilot form decodes. -/
def fjFalschBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 15
  else if a.toNat = 4097 then natByte 144
  else if a.toNat < 4102 then BitVec.ofNat 8 0
  else BitVec.ofNat 8 0

/-- Forged state: same map shape, one mutated opcode byte. -/
def fjFalsch : Zustand :=
  { fjTaken with speicher := { fjSpeicher with bytes := fjFalschBytes } }

/-! ## 6. Concrete pins: taken edge, unused-flag stability, mutation,
    refusals.

    Every pin below is a concrete fetched-byte fact (`decide`): the
    taken edge lands at 4118, flipping every unconsumed flag
    (including AF alone) keeps it there, clearing the consumed ZF
    falls through to 4102, and truncated, execute-denied and forged
    bytes refuse with no transition. -/

/-- TAKEN: the fetched `je +16` steps from 4096 to 4118. -/
theorem fj_kante_genommen :
    ausgangRip (byteschritt fjTaken) = some (BitVec.ofNat 64 4118) := by
  decide

/-- UNUSED FLAGS STABLE: flipping CF/PF/AF/SF/OF around a set ZF
    keeps the fetched successor at 4118. -/
theorem fj_kante_ander_stabil :
    ausgangRip (byteschritt fjAnder) = some (BitVec.ofNat 64 4118) := by
  decide

/-- AF ALONE STABLE: leaving AF undefined keeps the edge at 4118. -/
theorem fj_kante_af_stabil :
    ausgangRip (byteschritt fjAf) = some (BitVec.ofNat 64 4118) := by
  decide

/-- CONSUMED-FLAG MUTATION: clearing ZF falls through to 4102, so
    the planted mutation observably changes the branch. -/
theorem fj_mutation_faellt_durch :
    ausgangRip (byteschritt fjFall) = some (BitVec.ofNat 64 4102) := by
  decide

/-- TRUNCATED REFUSAL: five of six bytes admit no transition. -/
theorem fj_stumpf_verweigert :
    ausgangRip (byteschritt fjStumpf) = none := by
  decide

/-- EXECUTE-DENIED REFUSAL: no execute permission, no transition. -/
theorem fj_ohneExec_verweigert :
    ausgangRip (byteschritt fjOhneExec) = none := by
  decide

/-- FORGED-OPCODE REFUSAL: the mutated second byte decodes to
    nothing, so the step refuses. -/
theorem fj_falsch_verweigert :
    ausgangRip (byteschritt fjFalsch) = none := by
  decide

/-! ## 7. Joint witnesses.

    `fetchDekodiert_gleich_zeuge` exhibits ALL premises of the fetch
    identity jointly on the two flag variants. `fetchedJcc_stabil_zeuge`
    exhibits ALL premises of the main theorem jointly (one actual
    fetch, both accepted steps, code/map/RIP identity, read-set
    agreement) and pairs the shared successor with a memory-changing
    store after the taken edge plus the planted truncation refusal.
    `cmovLower_fetched_stabil_zeuge` exhibits the lowering admission
    with its byte-step value and a memory-changing run. -/

/-- JOINT premise witness for `fetchDekodiert_gleich`: both flag
    variants fetch and decode identically over equal code, map
    and RIP. -/
theorem fetchDekodiert_gleich_zeuge :
    ∃ (d : Decodiert) (rest : List Byte),
      fetchDekodiert fjTaken = some (d, rest) ∧
      fetchDekodiert fjAnder = some (d, rest) ∧
      fjTaken.rip = fjAnder.rip ∧
      (∀ a, fjTaken.speicher.bytes a = fjAnder.speicher.bytes a) ∧
      (∀ a, fjTaken.speicher.ausfuehrbar a =
        fjAnder.speicher.ausfuehrbar a) := by
  refine ⟨⟨.jumpIf32 .e fjDisp, 6⟩, [], by decide, by decide, rfl,
    fun _ => rfl, fun _ => rfl⟩

/-- JOINT witness for `fetchedJcc_stabil`: one actual fetch of
    `je +16`, both accepted steps from the two flag variants, the
    shared successor at 4118, a store after the taken edge that
    observably changes the data byte from zero to 42, and the
    planted truncation refusal. -/
theorem fetchedJcc_stabil_zeuge :
    ∃ (sF' sG' : Zustand),
      fetchDekodiert fjTaken =
        some ((⟨.jumpIf32 .e fjDisp, 6⟩ : Decodiert), []) ∧
      schritt (⟨.jumpIf32 .e fjDisp, 6⟩ : Decodiert) fjTaken =
        some sF' ∧
      schritt (⟨.jumpIf32 .e fjDisp, 6⟩ : Decodiert) fjAnder =
        some sG' ∧
      sF'.rip = sG'.rip ∧
      sF'.rip = BitVec.ofNat 64 4118 ∧
      (schritt (⟨.store64 .rsp .rax (BitVec.ofNat 32 0), 8⟩ : Decodiert)
        sF').map
        (fun t => t.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42) ∧
      fjTaken.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 ∧
      ausgangRip (byteschritt fjStumpf) = none := by
  have hok : laengeOk 6 = true := by decide
  have hbedT : bedingung .e fjTaken.flags = true := by decide
  have hbedA : bedingung .e fjAnder.flags = true := by decide
  have hdecT : fetchDekodiert fjTaken =
      some ((⟨.jumpIf32 .e fjDisp, 6⟩ : Decodiert), []) := by decide
  have hFT := schritt_jumpIf32_genommen
    (⟨.jumpIf32 .e fjDisp, 6⟩ : Decodiert) fjTaken .e fjDisp hok rfl
    hbedT
  have hGT := schritt_jumpIf32_genommen
    (⟨.jumpIf32 .e fjDisp, 6⟩ : Decodiert) fjAnder .e fjDisp hok rfl
    hbedA
  have hfl : stimmtUebberein .e fjTaken.flags fjAnder.flags := by
    intro n hn
    cases n with
    | cf => exact absurd hn (by decide)
    | pf => exact absurd hn (by decide)
    | zf => rfl
    | sf => exact absurd hn (by decide)
    | of_ => exact absurd hn (by decide)
  have hrips := (fetchedJcc_stabil fjTaken fjAnder _ _ _ [] .e fjDisp
    hdecT rfl rfl (fun _ => rfl) (fun _ => rfl) hfl hFT hGT).1
  refine ⟨_, _, hdecT, hFT, hGT, hrips, by decide, by decide, by decide,
    fj_stumpf_verweigert⟩

/-- JOINT witness for `cmovLower_fetched_stabil`: the admitted
    lowering, its byte-step value (the source word 20), and the
    memory-changing run that reads it back, plus the flag-clobber
    refusal. -/
theorem cmovLower_fetched_stabil_zeuge :
    ∃ (sF' : Zustand) (m : Speicher),
      cmovLowerOk (⟨.movReg64 .rax .rbx, 4⟩ : Decodiert) witTrue.flags
          witTrue.flags = true ∧
      cmovSchrittBytes 4 witTrue .rax .rbx .e = some sF' ∧
      sF'.register .rax = witTrue.register .rbx ∧
      write64 witSpeicher (BitVec.ofNat 64 8192) (sF'.register .rax) =
        some m ∧
      read64 m (BitVec.ofNat 64 8192) = some 20 ∧
      m.bytes (BitVec.ofNat 64 8192) ≠
        witSpeicher.bytes (BitVec.ofNat 64 8192) ∧
      cmovLowerOk (⟨.movReg64 .rax .rbx, 4⟩ : Decodiert) witTrue.flags
          witFalse.flags = false := by
  have hadmin : cmovLowerOk (⟨.movReg64 .rax .rbx, 4⟩ : Decodiert)
      witTrue.flags witTrue.flags = true := by decide
  have hstep : cmovSchrittBytes 4 witTrue .rax .rbx .e =
      some ({ cmovAnwenden witTrue .rax .rbx .e with
        rip := ripNach witTrue.rip 4 }) := by
    unfold cmovSchrittBytes
    rw [show laengeOk 4 = true from by decide]
  have hval := cmovLower_fetched_stabil
    (⟨.movReg64 .rax .rbx, 4⟩ : Decodiert) 4 witTrue witTrue _ _ .rax
    .rbx .e rfl hadmin (fun _ => rfl) hstep hstep
  have hsel : ({ cmovAnwenden witTrue .rax .rbx .e with
      rip := ripNach witTrue.rip 4 } : Zustand).register .rax = 20 :=
    cmov_witness_unterscheidet.1
  obtain ⟨m, hwr, hread, hdiff⟩ := cmov_speicher_zeuge
  have hsel2 : (cmovAnwenden witTrue .rax .rbx .e).register .rax = 20 :=
    cmov_witness_unterscheidet.1
  rw [hsel2] at hwr
  have hrefuse : cmovLowerOk (⟨.movReg64 .rax .rbx, 4⟩ : Decodiert)
      witTrue.flags witFalse.flags = false := by decide
  refine ⟨_, m, hadmin, hstep, hval, ?_, hread, hdiff, hrefuse⟩
  rw [← hsel] at hwr
  exact hwr

/- CUTS:
    Proved here (all over the REUSED canonical `Flags`/`bedingung`,
    `Codec.decode`, accepted `Ausfuehrung.schritt` equations, accepted
    `Byteschritt` fetch/step correspondence, accepted ControlCodec
    byte steps and accepted
    ConditionalMove/InstructionSelection/BranchLayout facts -- no new
    machine, decoder, executor, or source condition language):
    - fetch identity from equal actual code, map and RIP
      (`holeFetchAux_gleich`, `geholt_gleich`,
      `fetchDekodiert_gleich`, reusing the accepted
      `SourceCodeFrame.ausfuehrbarN_gleich` for the consumed-prefix
      check): no execution is assumed identical;
    - `fetchedJcc_stabil`: agreement on exactly the flags the FETCHED
      conditional jump reads gives the same successor RIP, the same
      branch outcome, the derived second fetch and the same
      `byteschritt` outcomes (taken and untaken, via the accepted
      `jccSchritt_stabil` on actual fetched bytes);
    - `fetchedJcc_len_layout`: the fetched length is the carried
      `BranchLayout` length (`zweigLaenge true .weit`);
    - `cmovLower_fetched_stabil`: an admitted `cmovLowerOk` lowering
      (checked length plus flag identity) selects the same
      destination word at byte level, for every condition;
    - `wahlOk_fetched_notwendig`: the `wahlOk` refusal of a
      clobbering `xor` under live flags is load-bearing -- the two
      choices take different fetched `je` successors;
    - `cmov_e_unverbraucht_stabil` / `setcc_e_unverbraucht_stabil`:
      under `.e` only ZF is consumed (same ZF plus same registers
      give the same selected value; CF/PF/AF/SF/OF free);
    - `cmov_setcc_len0_verweigert`: length 0 refuses both
      conditional-select byte steps;
    - concrete fetched-byte pins (`decide`): taken edge 4096 -> 4118,
      unused-flag stability (all-others-flipped and AF-alone),
      consumed-flag mutation falls through to 4102, truncated,
      execute-denied and forged-opcode refusals;
    - joint witnesses (`fetchDekodiert_gleich_zeuge`,
      `fetchedJcc_stabil_zeuge` with a memory-changing store after
      the taken edge, `cmovLower_fetched_stabil_zeuge` with a
      memory-changing run).
    NOT proved here, and not claimed:
    - No hardware correspondence: flag read sets follow the Intel
      manual as modelled in `Wort.lean`, checked only as
      self-consistency, not silicon.
    - No `fetchDekodiert` path for CMOVcc/SETcc: they have no `Befehl`
      constructor and no pilot decoder arm, so their byte steps run
      through `ControlCodec`/`dispatch` only; the fetched-branch
      claim stays `jumpIf32`-only.
    - No liveness analysis and no optimiser decision procedure: read
      sets are per-condition facts; `cmovLowerOk` admission and the
      `wahlOk` refusal are consumed, never re-decided.
    - No TSO/GX, concurrency, cost, time, termination, source,
      checker, Spec or goal claim; every fact is sequential over one
      `Speicher`; absence of a transition is never a termination
      statement.
-/

#print axioms holeFetchAux_gleich
#print axioms geholt_gleich
#print axioms fetchDekodiert_gleich
#print axioms fetchedJcc_stabil
#print axioms fetchedJcc_len_layout
#print axioms cmovLower_fetched_stabil
#print axioms wahlOk_fetched_notwendig
#print axioms cmov_e_unverbraucht_stabil
#print axioms setcc_e_unverbraucht_stabil
#print axioms cmov_setcc_len0_verweigert
#print axioms fj_kante_genommen
#print axioms fj_kante_ander_stabil
#print axioms fj_kante_af_stabil
#print axioms fj_mutation_faellt_durch
#print axioms fj_stumpf_verweigert
#print axioms fj_ohneExec_verweigert
#print axioms fj_falsch_verweigert
#print axioms fetchDekodiert_gleich_zeuge
#print axioms fetchedJcc_stabil_zeuge
#print axioms cmovLower_fetched_stabil_zeuge

end Gabbro.Grammatik.X86
