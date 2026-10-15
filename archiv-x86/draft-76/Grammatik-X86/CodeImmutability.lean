/-
  Code-window preservation under disjoint stores (lane 429).

  Over the accepted byte fetch (`Byteschritt.lean`) and permission-checked
  byte memory (`Speicher.lean`): a successful `write64` whose 8-byte
  footprint is disjoint from the whole possible fetch window at `rip`
  preserves the fetched bytes (`geholt`), the decode outcome
  (`fetchDekodiert`) and every code byte. An overlapping store is shown to
  change the fetch (counterexample). Range/wrap side conditions come from
  explicit Nat-interval facts. Whole-source self-modifying-code refusal
  stays separate work.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.SpeicherKommutation
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- A store footprint at `a` is foreign to the code window: every address
    of the whole possible fetch range (`fetchCap` bytes at `rip`) differs
    from every byte of the 8-byte store footprint. Stated over the whole
    cap so the induction below needs no length bookkeeping. -/
def CodeFremd (s : Zustand) (a : Adresse) : Prop :=
  ∀ i : Nat, i < fetchCap → ∀ k : Nat, k < 8 →
    addrOff s.rip i ≠ addrOff a k

/-- Execute permission is byte data, never created by a store: a successful
    `write64` only replaces `bytes`, so every `ausfuehrbarN` check agrees
    before and after. -/
theorem ausfuehrbarN_nach_schreiben (m m' : Speicher) (a b : Adresse)
    (v : Wort) (n : Nat) (hwr : write64 m a v = some m') :
    ausfuehrbarN m' b n = ausfuehrbarN m b n := by
  have hperm := write64_erhaelt_berechtigungen m a v m' hwr
  induction n with
  | zero => rfl
  | succ n ih => simp only [ausfuehrbarN, ih, hperm.2.2]

/-- The executable-prefix fetch reads only its window: a store outside
    the whole `cap` range leaves `holeFetchAux` unchanged. Induction over
    the cap; permissions agree by the store frame, bytes agree outside
    the footprint. -/
theorem holeFetchAux_nach_fremd (m m' : Speicher) (a w : Adresse)
    (v : Wort) (off cap : Nat)
    (hwr : write64 m w v = some m')
    (hdis : ∀ i : Nat, i < cap → ∀ k : Nat, k < 8 →
      addrOff a (off + i) ≠ addrOff w k) :
    holeFetchAux m' a off cap = holeFetchAux m a off cap := by
  induction cap generalizing off with
  | zero => rfl
  | succ n ih =>
    have hperm := write64_erhaelt_berechtigungen m w v m' hwr
    have hexe : m'.ausfuehrbar (addrOff a off) =
        m.ausfuehrbar (addrOff a off) := by rw [hperm.2.2]
    simp only [holeFetchAux, hexe]
    by_cases hc : m.ausfuehrbar (addrOff a off) = true
    · rw [if_pos hc, if_pos hc]
      have hbyte : m'.bytes (addrOff a off) = m.bytes (addrOff a off) :=
        write64_rahmen m m' w _ v hwr (fun k hk => by
          have h0 := hdis 0 (by omega) k hk
          rwa [Nat.add_zero] at h0)
      rw [hbyte]
      congr 1
      apply ih
      intro i hi k hk
      have h := hdis (i + 1) (Nat.succ_lt_succ hi) k hk
      have he : off + 1 + i = off + (i + 1) := by omega
      rw [← he] at h
      exact h
    · rw [if_neg hc, if_neg hc]

/-- FETCH PRESERVED: the fetched window at `rip` survives a successful
    store foreign to the code window. -/
theorem geholt_nach_fremd_schreiben (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write64 s.speicher a v = some m') (hdis : CodeFremd s a) :
    geholt { s with speicher := m' } = geholt s := by
  unfold geholt CodeFremd at *
  apply holeFetchAux_nach_fremd s.speicher m' s.rip a v 0 fetchCap hwr
  intro i hi k hk
  have h := hdis i hi k hk
  have he : 0 + i = i := Nat.zero_add i
  rw [he]
  exact h

/-- DECODE PRESERVED: the fetch-and-decode outcome (the checked
    instruction the byte step runs) is unchanged by a store foreign to
    the code window. Needs the fetch fact and the execute-permission
    fact; the decoder itself is never re-trusted. -/
theorem fetchDekodiert_nach_fremd_schreiben (s : Zustand) (m' : Speicher)
    (a : Adresse) (v : Wort)
    (hwr : write64 s.speicher a v = some m') (hdis : CodeFremd s a) :
    fetchDekodiert { s with speicher := m' } = fetchDekodiert s := by
  have hg : geholt { s with speicher := m' } = geholt s :=
    geholt_nach_fremd_schreiben s m' a v hwr hdis
  have hexe : ∀ n, ausfuehrbarN m' s.rip n =
      ausfuehrbarN s.speicher s.rip n :=
    fun n => ausfuehrbarN_nach_schreiben s.speicher m' a s.rip v n hwr
  unfold fetchDekodiert
  rw [hg]
  dsimp only
  simp only [hexe]

/-- CODE BYTES STAY: every byte of the fetched window reads as before
    after a foreign store. Uses the store frame plus the fetch length
    cap to place the byte inside the foreign range. -/
theorem codeBytes_bleiben (s : Zustand) (m' : Speicher) (a : Adresse)
    (v : Wort) (i : Nat)
    (hwr : write64 s.speicher a v = some m') (hdis : CodeFremd s a)
    (hi : i < (geholt s).length) :
    m'.bytes (addrOff s.rip i) = s.speicher.bytes (addrOff s.rip i) := by
  have hcap := geholt_laenge_le s
  have hi' : i < fetchCap := by omega
  exact write64_rahmen s.speicher m' a _ v hwr
    (fun k hk => hdis i hi' k hk)

/-- RANGE TO FOREIGNNESS: Nat-interval disjointness plus explicit
    no-wrap on both sides gives `CodeFremd`. The wrap hypotheses are
    stated, never assumed away: without them modular address addition
    could alias distant naturals. -/
theorem codeFremd_von_intervallen (s : Zustand) (a : Adresse)
    (hrip : s.rip.toNat + fetchCap ≤ 2 ^ 64)
    (hA : a.toNat + 8 ≤ 2 ^ 64)
    (h : s.rip.toNat + fetchCap ≤ a.toNat ∨
      a.toNat + 8 ≤ s.rip.toNat) :
    CodeFremd s a := by
  have h15 : fetchCap = 15 := rfl
  rw [h15] at hrip h
  intro i hi k hk he
  rw [h15] at hi
  have hripNat := s.rip.isLt
  have haNat := a.isLt
  have e1 : (addrOff s.rip i).toNat = s.rip.toNat + i := by
    unfold addrOff
    have hi64 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hi64,
      Nat.mod_eq_of_lt (by omega : s.rip.toNat + i < 2 ^ 64)]
  have e2 : (addrOff a k).toNat = a.toNat + k := by
    unfold addrOff
    have hk64 : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hk64,
      Nat.mod_eq_of_lt (by omega : a.toNat + k < 2 ^ 64)]
  have he2 := congrArg BitVec.toNat he
  rw [e1, e2] at he2
  omega

/-- WRAP ALIASES: near the top of the address space modular addition
    wraps, so naturals far apart name the same byte. This is why
    `codeFremd_von_intervallen` demands explicit no-wrap hypotheses
    instead of reading disjointness off Nat order alone. -/
theorem umbruch_alias :
    addrOff (BitVec.ofNat 64 (2 ^ 64 - 2)) 2 =
      addrOff (BitVec.ofNat 64 0) 0 := by
  decide

/-! ## Concrete witnesses over the accepted chain-program memory. -/

/-- The chain program at 4096 is far below the data cell at 8192:
    the whole 15-byte fetch range stays disjoint from the 8-byte store
    footprint, through the interval bridge. -/
theorem wFremd : CodeFremd ketteStart (BitVec.ofNat 64 8192) := by
  apply codeFremd_von_intervallen
  · decide
  · decide
  · exact Or.inl (by decide)

/-- JOINT WITNESS (disjoint, memory-changing, fetch-preserving): a real
    nonzero store at the data cell reaches, is foreign to the code
    window, preserves both the fetched window and the decode outcome,
    and observably changes the data byte. -/
theorem fremd_schreiben_zeuge :
    ∃ (m' : Speicher),
      (42 : Wort) ≠ 0 ∧
      write64 ketteStart.speicher (BitVec.ofNat 64 8192) 42 = some m' ∧
      CodeFremd ketteStart (BitVec.ofNat 64 8192) ∧
      geholt { ketteStart with speicher := m' } = geholt ketteStart ∧
      fetchDekodiert { ketteStart with speicher := m' } =
        fetchDekodiert ketteStart ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠
        ketteStart.speicher.bytes (BitVec.ofNat 64 8192) := by
  have hsch : schreibbar8 ketteStart.speicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hwr : write64 ketteStart.speicher (BitVec.ofNat 64 8192) 42 =
      some { ketteStart.speicher with
        bytes := writeBytes ketteStart.speicher (BitVec.ofNat 64 8192) 42 } := by
    unfold write64
    rw [if_pos hsch]
  refine ⟨_, by decide, hwr, wFremd, ?_, ?_, ?_⟩
  · exact geholt_nach_fremd_schreiben ketteStart _ _ _ hwr wFremd
  · exact fetchDekodiert_nach_fremd_schreiben ketteStart _ _ _ hwr wFremd
  · have hhit := write64_trifft _ _ _ _ 0 (by decide) hwr
    rw [addrOff_null] at hhit
    have halt : ketteStart.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0 := by decide
    rw [halt, hhit]
    decide

/-- Overlapping store memory: a `ret` byte at 4096 that is executable
    AND writable (the model permits both; loaded images never do), so a
    real store can reach the code byte. -/
def wOverlappSpeicher : Speicher :=
  { bytes := fun a =>
      if a.toNat = 4096 then natByte 195 else BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4128) }

/-- Overlapping store start state: `rip` at the writable code byte. -/
def wOverlappStart : Zustand :=
  { register := ketteReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 4096
    speicher := wOverlappSpeicher }

/-- The overlapping footprint is NOT foreign: byte zero of the window
    is byte zero of the store. -/
theorem ueberlapp_nicht_fremd :
    ¬ CodeFremd wOverlappStart (BitVec.ofNat 64 4096) := by
  intro h
  have h0 := h 0 (by decide) 0 (by decide)
  have erip : wOverlappStart.rip = BitVec.ofNat 64 4096 := rfl
  have e : addrOff wOverlappStart.rip 0 =
      addrOff (BitVec.ofNat 64 4096) 0 := by
    rw [addrOff_null, addrOff_null, erip]
  exact h0 e

/-- OVERLAP COUNTEREXAMPLE (joint): a real store onto the code byte
    reaches, observably changes the code byte, and changes the fetched
    window. Foreignness is exactly what fails. -/
theorem ueberlapp_geaendert_zeuge :
    ∃ (m' : Speicher),
      write64 wOverlappStart.speicher (BitVec.ofNat 64 4096) 42 = some m' ∧
      m'.bytes (BitVec.ofNat 64 4096) ≠
        wOverlappStart.speicher.bytes (BitVec.ofNat 64 4096) ∧
      geholt { wOverlappStart with speicher := m' } ≠
        geholt wOverlappStart := by
  have hsch :
      schreibbar8 wOverlappStart.speicher (BitVec.ofNat 64 4096) = true := by
    decide
  have hwr : write64 wOverlappStart.speicher (BitVec.ofNat 64 4096) 42 =
      some { wOverlappStart.speicher with
        bytes := writeBytes wOverlappStart.speicher
          (BitVec.ofNat 64 4096) 42 } := by
    unfold write64
    rw [if_pos hsch]
  refine ⟨_, hwr, ?_, ?_⟩
  · have hhit := write64_trifft _ _ _ _ 0 (by decide) hwr
    rw [addrOff_null] at hhit
    have halt : wOverlappStart.speicher.bytes (BitVec.ofNat 64 4096) =
        natByte 195 := by decide
    rw [halt, hhit]
    decide
  · decide

/- CUTS:
    Proved here: a successful `write64` foreign to the whole 15-byte
    fetch window (`CodeFremd`) preserves the executable-prefix fetch
    (`geholt_nach_fremd_schreiben`, by induction over the cap), the
    checked fetch-and-decode outcome (`fetchDekodiert_nach_fremd_schreiben`,
    with execute permission preserved because a store only replaces
    `bytes`), and every fetched code byte (`codeBytes_bleiben`, via the
    accepted store frame); Nat-interval disjointness plus explicit
    no-wrap gives foreignness (`codeFremd_von_intervallen`); concrete
    joint witnesses: a memory-changing disjoint store preserving fetch
    and decode (`fremd_schreiben_zeuge` over the accepted chain memory),
    and an overlapping store that is provably not foreign and changes
    both the code byte and the fetch (`ueberlapp_nicht_fremd`,
    `ueberlapp_geaendert_zeuge`); wrap aliasing as the reason for the
    no-wrap side conditions (`umbruch_alias`).
    NOT proved here, and not claimed:
    - No whole-source self-modifying-code refusal: this file shows what
      a foreign store preserves and what an overlapping store breaks,
      but no source-level theorem refusing a program that writes its
      own code window. That refusal stays separate work.
    - No byte-step outcome preservation: `byteschritt` runs `schritt`,
      which may legitimately read data memory (loads, stack), so a
      disjoint data store can change the successor state even while the
      fetch is identical. Only fetch, decode and code bytes are claimed.
    - No concurrency, cache/TLB/store-buffer or hardware coherence
      claim: everything is sequential over one model `Speicher`;
      self-modifying-code coherence on silicon stays with the TSO bridge.
    - Only 64-bit `write64` stores are covered; the 1/2/4-byte forms have
      the same `writeBytesN` shape and would commute the same way, but
      their fetch-preservation instances are not stated.
    - No new hardware or software assumptions: the only facts used are
      the accepted permission frame (a store replaces `bytes` alone)
      and explicit Nat-interval arithmetic.
-/

#print axioms ausfuehrbarN_nach_schreiben
#print axioms holeFetchAux_nach_fremd
#print axioms geholt_nach_fremd_schreiben
#print axioms fetchDekodiert_nach_fremd_schreiben
#print axioms codeBytes_bleiben
#print axioms codeFremd_von_intervallen
#print axioms umbruch_alias
#print axioms wFremd
#print axioms fremd_schreiben_zeuge
#print axioms ueberlapp_nicht_fremd
#print axioms ueberlapp_geaendert_zeuge

end Gabbro.Grammatik.X86
