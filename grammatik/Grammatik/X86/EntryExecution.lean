/-
  Entry admission to executed first instruction (lane 571).

  Connects the accepted entry admission (`EntryState.eintrittOk` over the
  checked `Bild` mapping) and caller-gate admission (`GateStub`/`valTore`)
  to executed-memory consequences: the RIP is executable through the
  CHECKED loaded mapping (not just the state's permission function), the
  entry stack window is readable/writable, and the fetched first
  instruction actually steps (`Byteschritt.byteschritt`). Source
  start/binding duties (`ReqAmEintritt`, `AufruferPflicht`) are reused
  from their generic definitions; OS/binding contracts stay user logic.
  No new executor, no second decoder, no new hardware assumption.
-/
import Grammatik.X86.EntryState
import Grammatik.X86.GateStub
import Grammatik.X86.Byteschritt
import Grammatik.X86.ValidatorSkeleton
import Grammatik.VertragOrtB
import Grammatik.FremdRuf
import Grammatik.X86.ContractSites

namespace Gabbro.Grammatik.X86

/-- Joint x86 admission for one entry: checked image mapping AND entry
    state AND every listed caller gate. A `Bool`, never a fault claim;
    the source duties join in the joint witness below. -/
def eintrittZulassung (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl) : Bool :=
  wohlgeformt p bild && eintrittOk p bild bias art z && valTore tore

/-- Admission implies the checked image mapping. -/
theorem zulassung_wohlgeformt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : eintrittZulassung p bild bias art z tore = true) :
    wohlgeformt p bild = true := by
  unfold eintrittZulassung at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1

/-- Admission implies the entry predicate. -/
theorem zulassung_eintritt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : eintrittZulassung p bild bias art z tore = true) :
    eintrittOk p bild bias art z = true := by
  unfold eintrittZulassung at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.2

/-- Admission makes the RIP executable through the CHECKED loaded
    mapping: the actual shared `Speicher` built from the image answers
    `true` at the entry RIP. This is not the state's own permission
    function -- it is the loaded byte permission the validator checked. -/
theorem zulassung_rip_ausfuehrbar (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : eintrittZulassung p bild bias art z tore = true) :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true := by
  have he := zulassung_eintritt p bild bias art z tore h
  unfold eintrittOk at he
  simp only [Bool.and_eq_true_iff] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hl⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := he
  exact hl

/-- Admission makes the entry stack window below the top readable and
    writable in the entry state's own memory: one word below `rsp`. -/
theorem zulassung_stapel_rw (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (h : eintrittZulassung p bild bias art z tore = true) :
    lesbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true := by
  have he := zulassung_eintritt p bild bias art z tore h
  unfold eintrittOk at he
  simp only [Bool.and_eq_true_iff] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hrw⟩, _⟩, _⟩, _⟩ := he
  simpa [stapelRW, eintrittRsp] using hrw

/-- FIRST INSTRUCTION: from admission, the entry state's own fetched
    instruction runs as a real byte step, and the RIP is executable
    through the checked loaded mapping. Reuses `byteschritt_weiter`;
    no second fetch, no new executor. -/
theorem zulassung_erster_schritt (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (h : eintrittZulassung p bild bias art z tore = true)
    (hf : fetchDekodiert z.zustand = some (d, rest))
    (hs : schritt d z.zustand = some s') :
    (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      byteschritt z.zustand = .weiter s' := by
  refine ⟨zulassung_rip_ausfuehrbar p bild bias art z tore h, ?_⟩
  exact byteschritt_weiter z.zustand s' d rest hf hs

/-- Auxiliary: a pair the list search returns is a member with a true
    predicate. By induction on the table; no stdlib search lemma is
    invented or assumed. -/
theorem find?_tupel_mem (tab : List (Nat × Nat))
    (pred : (Nat × Nat) → Bool) (pr : Nat × Nat)
    (h : tab.find? pred = some pr) :
    pr ∈ tab ∧ pred pr = true := by
  induction tab with
  | nil => simp at h
  | cons hd tl ih =>
    cases hp : pred hd with
    | true =>
      simp only [List.find?, hp] at h
      cases h
      exact ⟨List.mem_cons_self, hp⟩
    | false =>
      simp only [List.find?, hp] at h
      obtain ⟨m1, m2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ m1, m2⟩

/-- CHANNEL LINK: a raw answer that decodes to a reason through an
    admitted gate's table names a reason inside the declared channel.
    Uses the admission (every table target is a declared case) and the
    actual decode (the reason came from a table row). The kernel-side
    meaning of the table stays user logic, never an assumption. -/
theorem tor_grund_im_kanal (t : TorDekl) (lo hi roh : Int) (g : Nat)
    (htor : torOkB t = true)
    (herr : torKlassifiziere t.errors lo hi roh = .grund g) :
    g < t.gruende := by
  have hfehler :
      t.errors.all (fun p => decide (p.2 < t.gruende)) = true := by
    unfold torOkB fehlerOkB at htor
    simp only [Bool.and_eq_true_iff] at htor
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hf⟩ := htor
    exact hf.1.2
  have hex : ∃ errno, (errno, g) ∈ t.errors := by
    unfold torKlassifiziere at herr
    by_cases hneg : roh < 0
    · rw [if_pos hneg] at herr
      by_cases hfence : 1 ≤ -roh ∧ -roh ≤ 4095
      · rw [dif_pos hfence] at herr
        cases hfind : t.errors.find?
            (fun p => decide (p.1 = (-roh).toNat)) with
        | none =>
          rw [hfind] at herr
          cases herr
        | some pr =>
          obtain ⟨e1, e2⟩ := pr
          have hmem : (e1, e2) ∈ t.errors :=
            (find?_tupel_mem _ _ _ hfind).1
          rw [hfind] at herr
          cases herr
          exact ⟨e1, hmem⟩
      · rw [dif_neg hfence] at herr
        cases herr
    · rw [if_neg hneg] at herr
      by_cases hok : lo ≤ roh ∧ roh ≤ hi
      · rw [if_pos hok] at herr
        cases herr
      · rw [if_neg hok] at herr
        cases herr
  obtain ⟨errno, hmem⟩ := hex
  have hall := (List.all_eq_true.mp hfehler) _ hmem
  exact of_decide_eq_true hall

/-- REFUSAL: an unlisted RIP admits no entry. Uses the missing listing. -/
theorem zulassung_verweigert_unlisted (p : Profil) (bild : Bild)
    (bias : Nat) (art : EintrittArt) (z : EintrittZustand)
    (tore : List TorDekl)
    (h : eintragGelisted bild z.zustand.rip.toNat = false) :
    eintrittZulassung p bild bias art z tore = false := by
  unfold eintrittZulassung
  rw [eintritt_verweigert_unlisted p bild bias art z h]
  simp

/-- A gate list containing a refused declaration is refused. Uses the
    member's refusal and the list's admission shape. -/
theorem valTore_verweigert_bei (tore : List TorDekl) (t : TorDekl)
    (hmem : t ∈ tore) (h : torOkB t = false) :
    valTore tore = false := by
  have hnot : ¬ (∀ x, x ∈ tore → torOkB x = true) := by
    intro hall
    have ht := hall t hmem
    rw [h] at ht
    cases ht
  rw [← List.all_eq_true] at hnot
  unfold valTore
  cases hall : tore.all torOkB with
  | true => exact absurd hall hnot
  | false => rfl

/-- REFUSAL: a gate list with a refused member admits no entry. Uses
    the member's refusal through the list's admission shape. -/
theorem zulassung_verweigert_tor (p : Profil) (bild : Bild) (bias : Nat)
    (art : EintrittArt) (z : EintrittZustand) (tore : List TorDekl)
    (t : TorDekl) (hmem : t ∈ tore) (h : torOkB t = false) :
    eintrittZulassung p bild bias art z tore = false := by
  unfold eintrittZulassung
  rw [valTore_verweigert_bei tore t hmem h]
  simp

/-! ## Witness: admitted entry whose first byte runs.

    The minimal accepted image (`valZeuge`: one `ret` byte) with a stack
    window that covers both the checked word below the top (entry
    discipline) and the word the `ret` pops (actual execution). Stack is
    never executable: `ausfuehrbar` comes from the checked image only. -/

/-- Witness memory: checked image bytes and permissions plus a
    readable/writable stack window `[0x7000, 0x8008)`. -/
def zulassungSpeicher : Speicher :=
  { bytes := fun a => ladenByte valZeuge 0 a.toNat
    lesbar := fun a =>
      decide (0x7000 ≤ a.toNat ∧ a.toNat < 0x8008) ||
        ladenLesbar valZeuge 0 a.toNat
    schreibbar := fun a =>
      decide (0x7000 ≤ a.toNat ∧ a.toNat < 0x8008) ||
        ladenSchreibbar valZeuge 0 a.toNat
    ausfuehrbar := fun a => ladenAusfuehrbar valZeuge 0 a.toNat }

/-- Witness entry state for hosted main on the minimal image: RIP at the
    listed entry, RSP at the aligned top, no XMM touched, IF set. -/
def zeugenEintrittAusf : EintrittZustand :=
  { zustand :=
    { register := fun r =>
        if r == Register.rsp then BitVec.ofNat 64 0x8000
        else BitVec.ofNat 64 0
      flags := { cf := false, pf := false, af := none, zf := false,
                 sf := false, of := false }
      rip := BitVec.ofNat 64 0x1000
      speicher := zulassungSpeicher }
    mxcsr := 0x1F80
    xmmBeruehrt := false
    mxcsrGesichert := false
    ifBit := true
    guardOk := true }

/-- ACCEPTANCE: the witness entry is admitted -- checked image, listed
    executable entry, aligned readable/writable stack, admitted gate. -/
theorem zulassung_zeuge_ok :
    eintrittZulassung .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [schreibTor] = true := by
  decide

/-- FETCH TIE: at the admitted entry, the byte step's fetch over actual
    executable memory sees exactly the validated `ret` with no
    remainder. The admitted bytes are what the machine fetches. -/
theorem zulassung_fetch_ret :
    fetchDekodiert zeugenEintrittAusf.zustand = some (⟨.ret, 1⟩, []) := by
  decide

/-- FIRST STEP RUNS: the fetched `ret` pops the zero word at the stack
    top, so the byte step moves to RIP zero. Stated through the
    decidable RIP projection. -/
theorem zulassung_schritt_ret :
    ausgangRip (byteschritt zeugenEintrittAusf.zustand) =
      some (BitVec.ofNat 64 0) := by
  decide

/-- PLANTED REFUSAL: the same entry moved to an unlisted RIP admits
    nothing, although image, stack and gate are unchanged. -/
theorem zulassung_fremd_verweigert :
    eintrittZulassung .p48 valZeuge 0 .hostedMain
      { zeugenEintrittAusf with zustand :=
        { zeugenEintrittAusf.zustand with
          rip := BitVec.ofNat 64 0x5000 } } [schreibTor] = false := by
  decide

/-- PLANTED REFUSAL: the admitted entry with a clobbered-out gate
    admits nothing, although image and entry state are unchanged. -/
theorem zulassung_abi_verweigert :
    eintrittZulassung .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
      [torAusClobber] = false := by
  decide

/-- JOINT WITNESS (channel): the witness gate is admitted, EBADF
    decodes to reason 0 through its table, and the reason lies inside
    the declared channel -- every premise jointly instantiated. -/
theorem tor_grund_im_kanal_zeuge :
    torOkB schreibTor = true ∧
      torKlassifiziere schreibTor.errors 0 8192 (-9) = .grund 0 ∧
      0 < schreibTor.gruende :=
  ⟨schreibTor_ok, torKlassifiziere_ebadf,
    tor_grund_im_kanal schreibTor 0 8192 (-9) 0 schreibTor_ok
      torKlassifiziere_ebadf⟩

/-- Caller-side binding duty at actual values: the caller's arguments
    meet the gate's precondition. This is the generic
    `AufruferPflicht`, reused rather than restated -- user logic, never
    a hardware assumption, and never discharged by a declaration alone.
    Consumer interface: whatever lowers a gate call must discharge this
    at the actual call site; see CUTS for the instantiation status. -/
def torRuferPflicht {D : Deklaration} (Pre : AxPre D) (a : D.Ax)
    (σ : World D) (ρ : Env D (D.aparams a)) : Prop :=
  AufruferPflicht Pre a σ ρ

/-- JOINT WITNESS (entry runs, source duties hold): the witness entry
    is admitted, its first instruction is fetched from the checked
    bytes and steps, and on a reached non-degenerate source run (a
    table-writing call with a `0 -> 5` memory change) the entry
    contract holds at its actual place -- plus a real eight-byte
    x86 memory change. Neither side is assumed from the other. -/
theorem eintrittAusf_zeuge :
    ∃ (M : RufMaschineG eD) (rhoP : Env eD (eD.params ePruefe))
      (wP : World eD),
      eintrittZulassung .p48 valZeuge 0 .hostedMain zeugenEintrittAusf
        [schreibTor] = true ∧
      fetchDekodiert zeugenEintrittAusf.zustand = some (⟨.ret, 1⟩, []) ∧
      ausgangRip (byteschritt zeugenEintrittAusf.zustand) =
        some (BitVec.ofNat 64 0) ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      ReqAmEintritt eP ePruefe wP rhoP ∧
      (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
        v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
          m.bytes a ≠ m'.bytes a) := by
  obtain ⟨M, hr, _, _, rhoP, wP, _, _, _, _, _, _, _, _, _, hreq, _⟩ :=
    vertragStandort_lauf_zeuge
  exact ⟨M, rhoP, wP, zulassung_zeuge_ok, zulassung_fetch_ret,
    zulassung_schritt_ret, hr, hreq, write_read_zeuge⟩

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Bild.wohlgeformt`
   /`geladen`, `EntryState.eintrittOk`, `GateStub.torOkB`/
   `torKlassifiziere`, `Byteschritt.fetchDekodiert`/`byteschritt`,
   `ValidatorSkeleton.valZeuge`/`valTore`, `VertragOrtB.ReqAmEintritt`,
   `FremdRuf.AufruferPflicht`, `ContractSites.vertragStandort_lauf_zeuge`,
   `Speicher.write_read_zeuge`): the joint admission predicate
   (`eintrittZulassung`: checked mapping AND entry state AND gates),
   its mapping/entry projections, RIP executability through the CHECKED
   loaded mapping (not the state's own permission function), the entry
   stack window facts, the fetched-first-instruction step
   (`zulassung_erster_schritt`), the gate channel link (a decoded
   reason lands inside the declared channel, with joint witness), the
   caller-duty interface (`torRuferPflicht`, the generic duty reused),
   generic unlisted-RIP and refused-gate refusals with planted
   `decide` witnesses, and the joint witness (admitted entry, fetched
   `ret`, executed step, reached non-degenerate source run with the
   entry contract at its place, real x86 memory change).
   OPEN, stated here as obligation and never as an assumed premise of
   any delivered theorem:
   - Source-to-entry lowering: no claim is made that the admitted bytes
     are the emitted form of any source program, or that any source
     start lowers to this entry. The shared IR (lane 287) and the
     QUELLBRUECKE bridge are the named open dependencies; no substitute
     IR or executor is invented here.
   - Asynchronous interrupt model: entry IF/guard discipline is checked
     admission at handoff only; what an interrupt does afterwards is
     OPEN (owner of the interrupt leg).
   - `torRuferPflicht` is stated, never jointly instantiated: the
     non-degenerate fixture declaration carries `Ax := Empty`, so no
     gate inhabitant exists to discharge a caller precondition on it.
     Whatever lowers a gate call must discharge it at the actual call
     site; a declaration alone admits nothing.
   - Single-step scope: the witness `ret` pops to RIP zero (unlisted);
     no multi-step control-flow, entry-legality-beyond-containment, or
     callee-side (obligation (c)) template claim is made here.
   - No hardware claim: refusal `Bool`s are validator admission, never
     a fault claim; silicon, caches, TLBs, store buffers, faults beyond
     the decoded refusal, and timing are untouched. Binding/kernel
     behaviour stays user logic.
   - No cost/time claim: no budget, cycle, or bound is transferred.
-/

#print axioms eintrittZulassung
#print axioms zulassung_wohlgeformt
#print axioms zulassung_eintritt
#print axioms zulassung_rip_ausfuehrbar
#print axioms zulassung_stapel_rw
#print axioms zulassung_erster_schritt
#print axioms find?_tupel_mem
#print axioms tor_grund_im_kanal
#print axioms zulassung_verweigert_unlisted
#print axioms valTore_verweigert_bei
#print axioms zulassung_verweigert_tor
#print axioms zulassung_zeuge_ok
#print axioms zulassung_fetch_ret
#print axioms zulassung_schritt_ret
#print axioms zulassung_fremd_verweigert
#print axioms zulassung_abi_verweigert
#print axioms tor_grund_im_kanal_zeuge
#print axioms eintrittAusf_zeuge

end Gabbro.Grammatik.X86
