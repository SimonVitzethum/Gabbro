/-
  File:      Grammatik/X86/OverlapRefusal.lean
  Subject:   Decided overlap refusal over target access footprints (O-align decidable half).

  Lane 342 (wave B2, Lean-first): a decided alignment/containment/non-overlap
  checker over the canonical `Zugriff` footprints of `Zugriffe.lean`, the
  `Region` extents of `Regionen.lean` and the `Abschnitt` layout of
  `Bild.lean`, plus the aligned-single-carrier bytes-value agreement lemma
  over the little-endian `Speicher.lean` mapping. Tearing correspondence
  (aligned multi-byte single-copy atomicity under concurrency) stays OPEN:
  the checker is validator/profile admission, never a hardware fault claim.
  Actual x86 hardware allows many unaligned ordinary accesses; this file
  imposes declared alignment only where the selected contract/profile
  requires it, with refusal as the loud outcome. No new ISA, no second
  evaluator, no source admission change.
-/
import Grammatik.X86.Speicher
import Grammatik.X86.Zugriffe
import Grammatik.X86.Regionen
import Grammatik.X86.Bild

namespace Gabbro.Grammatik.X86

/-! ## 1. Decided alignment and containment over footprints. -/

/-- Decided natural alignment of one address: nonzero width dividing `toNat`. -/
def addrAusgerichtet (a : Adresse) (ausr : Nat) : Bool :=
  decide (0 < ausr ∧ a.toNat % ausr = 0)

/-- Decided containment: every footprint byte lies in the region extent. -/
def fussEnthalten (f : List Adresse) (r : Region) : Bool :=
  f.all (fun a => inRegion r a.toNat)

/-- The access base: first written byte, else first read byte, else none
    (pure forms carry no footprint and are vacuously admitted). -/
def zugriffBasis (z : Zugriff) : Option Adresse :=
  match z.schreiben, z.lesen with
  | b :: _, _ => some b
  | [], b :: _ => some b
  | [], [] => none

/-- Single-access admission: the base is naturally aligned and the whole
    read/write footprint lies inside the one carrier extent. -/
def zugriffOk (z : Zugriff) (r : Region) (ausr : Nat) : Bool :=
  match zugriffBasis z with
  | none => true
  | some b => addrAusgerichtet b ausr && fussEnthalten (z.lesen ++ z.schreiben) r

/-! ## 1b. Single-access admission facts. -/

/-- A zero width refuses every address: no silent admission. -/
theorem addrAusgerichtet_null_verweigert (a : Adresse) :
    addrAusgerichtet a 0 = false := by
  simp [addrAusgerichtet]

/-- Probe: the stack top 8192 is naturally aligned for 8-byte carriers. -/
theorem probe_ausgerichtet_8192 :
    addrAusgerichtet (BitVec.ofNat 64 8192) 8 = true := by
  decide

/-- Probe: base 8196 (carrier base plus four) is NOT 8-aligned. -/
theorem probe_unversetzt_8196 :
    addrAusgerichtet (BitVec.ofNat 64 8196) 8 = false := by
  decide

/-- Empty footprints carry no base and are vacuously admitted. -/
theorem zugriffOk_ohne_fuss (z : Zugriff) (r : Region) (ausr : Nat)
    (hs : z.schreiben = []) (hl : z.lesen = []) :
    zugriffOk z r ausr = true := by
  simp [zugriffOk, zugriffBasis, hs, hl]

/-! ## 2. Decided non-overlap with a conservative three-state policy. -/

/-- Decided footprint disjointness: every byte address differs. -/
def fussDisjunktB (a b : List Adresse) : Bool :=
  a.all (fun x => b.all (fun y => x != y))

/-- Overlap answer: `disjunkt` is proved disjoint, `gleich` is the same
    footprint (shared bytes, needs another discipline), `unbekannt` is a
    partial overlap the checker cannot place. -/
inductive UeberlappAntwort where
  | disjunkt
  | gleich
  | unbekannt
  deriving DecidableEq, Repr

/-- Decided classifier over two footprints. -/
def klassifiziere (a b : List Adresse) : UeberlappAntwort :=
  if fussDisjunktB a b then .disjunkt
  else if a == b then .gleich else .unbekannt

/-- Conservative admission: only proved disjointness admits a shared access;
    `unknown-overlap => refuse`, and same-footprint sharing is refused here
    (it needs lock/atomic discipline, owned elsewhere). -/
def aliasZulassen : UeberlappAntwort → Bool
  | .disjunkt => true
  | .gleich => false
  | .unbekannt => false

/-- The empty footprint is disjoint from everything. -/
theorem fussDisjunktB_leer_links (b : List Adresse) :
    fussDisjunktB [] b = true := by
  rfl

/-- A positive disjointness answer classifies as `disjunkt`. -/
theorem klassifiziere_disjunkt (a b : List Adresse)
    (h : fussDisjunktB a b = true) :
    klassifiziere a b = .disjunkt := by
  simp [klassifiziere, h]

/-- The policy refuses the unknown case: this is `unknown-overlap => refuse`. -/
theorem klassifiziere_verweigert_unbekannt (a b : List Adresse)
    (h : klassifiziere a b = .unbekannt) :
    aliasZulassen (klassifiziere a b) = false := by
  simp [h, aliasZulassen]

/-- SOUNDNESS: a positive Bool answer means set disjointness: no byte of
    `a` lies in `b`. Every premise is used. -/
theorem fussDisjunktB_klingt (a b : List Adresse)
    (h : fussDisjunktB a b = true) (x : Adresse) (hx : x ∈ a) : x ∉ b := by
  unfold fussDisjunktB at h
  rw [List.all_eq_true] at h
  have hx2 := h x hx
  rw [List.all_eq_true] at hx2
  intro hy
  have heq := hx2 x hy
  simp at heq

/-! ## 3. Single word carrier and bytes-value agreement. -/

/-- One 8-byte word carrier: a readable/writable, never-executable extent
    of exactly one word at `basis`. -/
def wortTraeger (basis : Nat) : Region :=
  { basis := basis, len := 8, lesbar := true,
    schreibbar := true, ausfuehrbar := false }

/-- ALIGNED-SINGLE-CARRIER BYTES-VALUE AGREEMENT: an 8-byte access whose
    base names the carrier is admitted by the checker, reads back the
    stored value, and every footprint byte carries the value's
    little-endian byte. Every premise is used: `hbasis`/`hno` place the
    footprint inside the carrier, `hcel` aligns the base, `hwr`/`hrd`
    give the read-back and the byte facts. -/
theorem einzelTraeger_wertUeberein (m m' : Speicher) (a : Adresse) (v : Wort)
    (c : Nat) (hbasis : a.toNat = c) (hcel : c % 8 = 0)
    (hno : OhneUmbruch a) (hwr : write64 m a v = some m')
    (hrd : lesbar8 m a = true) :
    read64 m' a = some v ∧
      (∀ k, k < 8 → m'.bytes (addrOff a k) = wortByte v k) ∧
      fussEnthalten (Fuss a) (wortTraeger c) = true ∧
      addrAusgerichtet a 8 = true := by
  have hlese : read64 m' a = some v :=
    read64_nach_write64 m m' a v hwr hrd
  refine ⟨hlese, ?_, ?_, ?_⟩
  · unfold write64 at hwr
    by_cases hc : schreibbar8 m a = true
    · rw [if_pos hc] at hwr
      cases hwr
      intro k hk
      show writeBytes m a v (addrOff a k) = wortByte v k
      unfold writeBytes
      exact writeBytesN_hit m a v 8 k hk (Nat.le_refl 8)
    · rw [if_neg hc] at hwr
      cases hwr
  · unfold fussEnthalten
    rw [List.all_eq_true]
    intro x hx
    rw [fuss_mem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hadd : (addrOff a k).toNat = c + k := by
      rw [ohneUmbruch_addrs a hno k hk, hbasis]
    rw [hadd]
    show decide (c ≤ c + k ∧ c + k < c + 8) = true
    simp only [decide_eq_true_eq]
    omega
  · unfold addrAusgerichtet
    simp only [decide_eq_true_eq]
    refine ⟨by decide, ?_⟩
    rw [hbasis]
    exact hcel

/-! ## 4. Adjacent-carrier layout witness on one image. -/

/-- Lower carrier section: eight writable bytes at 8184. -/
def nachbarAbschnittA : Abschnitt :=
  { dateiOff := 0, dateiLen := 8, vaddr := 8184, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 8 }

/-- Upper carrier section: eight writable bytes at 8192, adjacent to A. -/
def nachbarAbschnittB : Abschnitt :=
  { dateiOff := 8, dateiLen := 8, vaddr := 8192, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 8 }

/-- Sixteen zero file bytes backing both carriers. -/
def nachbarDatei : List Byte :=
  List.replicate 16 (BitVec.ofNat 8 0)

/-- The adjacent-carrier image: two neighbouring word sections, fixed bias. -/
def nachbarBild : Bild :=
  { datei := nachbarDatei
    abschnitte := [nachbarAbschnittA, nachbarAbschnittB]
    reloks := []
    eintraege := []
    modus := .fest }

/-- The adjacent-carrier image is accepted under profile 48. -/
theorem nachbarBild_wohlgeformt :
    wohlgeformt .p48 nachbarBild = true := by
  decide

/-- Address 8184 resolves to the lower carrier section. -/
theorem nachbarFund_a :
    abteilFinden nachbarBild.abschnitte 0 8184 =
      some nachbarAbschnittA := by
  decide

/-- The boundary address 8192 resolves to the upper carrier section. -/
theorem nachbarFund_grenze :
    abteilFinden nachbarBild.abschnitte 0 8192 =
      some nachbarAbschnittB := by
  decide

/-- The two word carriers are disjoint regions. -/
theorem nachbarTraeger_disjunkt :
    regionDisjunkt (wortTraeger 8184) (wortTraeger 8192) = true := by
  decide

/-- ACCEPTED: the real `push` footprint below the witness stack top lies
    aligned inside the lower carrier. -/
theorem push_in_traeger_angenommen :
    zugriffOk
      (zugriff { befehl := Befehl.push64 Register.rax, laenge := 1 }
        zeugeZustand)
      (wortTraeger 8184) 8 = true := by
  decide

/-- ACCEPTED: the real `store` footprint at the witness stack top lies
    aligned inside the upper carrier. -/
theorem store_in_traeger_angenommen :
    zugriffOk
      (zugriff { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 4 } zeugeZustand)
      (wortTraeger 8192) 8 = true := by
  decide

/-- REFUSED: an 8-byte access at 8188 is unaligned, so the checker refuses
    it against the upper carrier. -/
theorem spanne_verweigert_unversetzt :
    zugriffOk ⟨[], Fuss (natAdresse 8188), some 42⟩
      (wortTraeger 8192) 8 = false := by
  decide

/-- REFUSED: the same spanning footprint is not contained in the lower
    carrier either: its upper bytes cross the carrier boundary. -/
theorem spanne_verweigert_aussen :
    fussEnthalten (Fuss (natAdresse 8188)) (wortTraeger 8184) = false := by
  decide

/-- The two accepted footprints are disjoint as byte sets. -/
theorem nachbarFuss_disjunkt :
    fussDisjunktB (Fuss (natAdresse 8184))
      (Fuss (natAdresse 8192)) = true := by
  decide

/-- The adjacent pair classifies as `disjunkt` through the generic lemma. -/
theorem nachbarKlasse_disjunkt :
    klassifiziere (Fuss (natAdresse 8184))
      (Fuss (natAdresse 8192)) = .disjunkt :=
  klassifiziere_disjunkt _ _ nachbarFuss_disjunkt

/-- The adjacent pair is admitted by the conservative policy. -/
theorem nachbarPaar_zugelassen :
    aliasZulassen (klassifiziere (Fuss (natAdresse 8184))
      (Fuss (natAdresse 8192))) = true := by
  rw [nachbarKlasse_disjunkt]
  rfl

/-- COUNTEREXAMPLE-C SHAPE (negative probe): an 8-byte access at the
    misaligned base 8196 overlaps two carriers (bytes 8196..8199 of the
    lower-adjacent word and 8200..8203 past it). It classifies as
    `unbekannt`: partial overlap the checker cannot place, so the
    conservative policy refuses it. Tearing correspondence stays OPEN. -/
theorem gegenbeispielC_unbekannt :
    klassifiziere (Fuss (natAdresse 8192))
      (Fuss (natAdresse 8196)) = .unbekannt := by
  decide

/-- The counterexample-C access is refused by the policy. -/
theorem gegenbeispielC_verweigert :
    aliasZulassen (klassifiziere (Fuss (natAdresse 8192))
      (Fuss (natAdresse 8196))) = false := by
  rw [gegenbeispielC_unbekannt]
  rfl

/-! ## 5. Joint witnesses: agreement plus checker verdicts plus a reached run. -/

/-- JOINT WITNESS for the agreement lemma: a real nonzero write at the
    aligned base 8192 reads back, observably changes the byte, carries
    the little-endian bytes, and is admitted by the checker; the
    instruction-level reached run changed the same byte. -/
theorem einzelTraeger_wertUeberein_zeuge :
    ∃ (m' : Speicher),
      write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 42 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠
        zeugeSpeicher.bytes (BitVec.ofNat 64 8192) ∧
      (∀ k, k < 8 →
        m'.bytes (addrOff (BitVec.ofNat 64 8192) k) = wortByte 42 k) ∧
      fussEnthalten (Fuss (BitVec.ofNat 64 8192))
        (wortTraeger 8192) = true ∧
      addrAusgerichtet (BitVec.ofNat 64 8192) 8 = true ∧
      ((lauf zeugeProg zeugeZustand).map
        (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
        some (BitVec.ofNat 8 42)) ∧
      (zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192) =
        BitVec.ofNat 8 0) := by
  have hbasis : (BitVec.ofNat 64 8192).toNat = 8192 := by decide
  have hcel : 8192 % 8 = 0 := by decide
  have hno : OhneUmbruch (BitVec.ofNat 64 8192) := by
    unfold OhneUmbruch
    decide
  have hsch : schreibbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hles : lesbar8 zeugeSpeicher (BitVec.ofNat 64 8192) = true := by
    decide
  have hwr : write64 zeugeSpeicher (BitVec.ofNat 64 8192) 42 =
      some { zeugeSpeicher with
        bytes := writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42 } := by
    unfold write64
    rw [if_pos hsch]
  obtain ⟨hrd, hbytes, henth, hausr⟩ :=
    einzelTraeger_wertUeberein _ _ _ _ _ hbasis hcel hno hwr hles
  refine ⟨_, hwr, hrd, ?_, hbytes, henth, hausr,
    zeuge_speicher_aendert_sich.2.1, zeuge_speicher_aendert_sich.2.2⟩
  have hhit := writeBytesN_hit zeugeSpeicher (BitVec.ofNat 64 8192) 42 8 0
    (by decide) (by decide)
  rw [addrOff_null] at hhit
  show writeBytes zeugeSpeicher (BitVec.ofNat 64 8192) 42
    (BitVec.ofNat 64 8192) ≠ BitVec.ofNat 8 0
  unfold writeBytes
  rw [hhit]
  decide

/-- JOINT CHECKER WITNESS: on the one adjacent-carrier layout the real
    push and store footprints are accepted, the carriers are disjoint,
    the spanning access and the counterexample-C pair are refused, and
    the reached run observably changed memory. -/
theorem zugriffOk_zeuge :
    zugriffOk (zugriff { befehl := Befehl.push64 Register.rax, laenge := 1 } zeugeZustand) (wortTraeger 8184) 8 = true ∧
    zugriffOk (zugriff { befehl := Befehl.store64 Register.rsp Register.rax (BitVec.ofNat 32 0), laenge := 4 } zeugeZustand) (wortTraeger 8192) 8 = true ∧
    regionDisjunkt (wortTraeger 8184) (wortTraeger 8192) = true ∧
    zugriffOk ⟨[], Fuss (natAdresse 8188), some 42⟩ (wortTraeger 8192) 8 = false ∧
    aliasZulassen (klassifiziere (Fuss (natAdresse 8192)) (Fuss (natAdresse 8196))) = false ∧
    ((lauf zeugeProg zeugeZustand).map (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) = some (BitVec.ofNat 8 42)) := by
  exact ⟨push_in_traeger_angenommen, store_in_traeger_angenommen,
    nachbarTraeger_disjunkt, spanne_verweigert_unversetzt,
    gegenbeispielC_verweigert, zeuge_speicher_aendert_sich.2.1⟩

/- CUTS:
    - Decided admission only: `zugriffOk`/`aliasZulassen` are
      validator/profile admission over footprints, never hardware fault
      claims. Actual x86 hardware allows many unaligned ordinary
      accesses; alignment is imposed only where the selected
      contract/profile declares it, with refusal as the loud outcome
      and a certified scalar fallback owned by the consumer.
    - No atomicity or tearing claim: the agreement lemma is sequential
      over one canonical `Speicher`; aligned multi-byte single-copy
      atomicity, LOCK RMW and any per-access TSO correspondence stay
      OPEN with the TSO bridge. The eight `Fuss` addresses are per-byte
      events, not one atomic occurrence.
    - Same-footprint sharing (`gleich`) is refused here; its admission
      needs lock/atomic discipline owned elsewhere, not a weaker check.
    - No source correspondence: nothing here lowers a Gabbro carrier,
      duty, contract or cost; no `Zielsatz/Spec` statement is touched.
    - No new ISA: only the 14 pilot `Befehl` forms through the canonical
      `zugriff` extraction; narrow 8/16/32-bit carriers and their
      extension helpers belong to future ISA work, not duplicated here.
    - Consumer interface: the future shared IR (lane 287, pending) may
      consume `zugriffOk`/`klassifiziere` verdicts; no substitute IR is
      invented here and the tearing proof stays OPEN until derived.
    - No cost, budget, progress, timing, ABI/loader or whole-image claim.
-/

#print axioms addrAusgerichtet
#print axioms fussEnthalten
#print axioms zugriffBasis
#print axioms zugriffOk
#print axioms addrAusgerichtet_null_verweigert
#print axioms probe_ausgerichtet_8192
#print axioms probe_unversetzt_8196
#print axioms zugriffOk_ohne_fuss
#print axioms fussDisjunktB
#print axioms klassifiziere
#print axioms aliasZulassen
#print axioms fussDisjunktB_leer_links
#print axioms klassifiziere_disjunkt
#print axioms klassifiziere_verweigert_unbekannt
#print axioms fussDisjunktB_klingt
#print axioms wortTraeger
#print axioms einzelTraeger_wertUeberein
#print axioms nachbarBild_wohlgeformt
#print axioms nachbarFund_a
#print axioms nachbarFund_grenze
#print axioms nachbarTraeger_disjunkt
#print axioms push_in_traeger_angenommen
#print axioms store_in_traeger_angenommen
#print axioms spanne_verweigert_unversetzt
#print axioms spanne_verweigert_aussen
#print axioms nachbarFuss_disjunkt
#print axioms nachbarKlasse_disjunkt
#print axioms nachbarPaar_zugelassen
#print axioms gegenbeispielC_unbekannt
#print axioms gegenbeispielC_verweigert
#print axioms einzelTraeger_wertUeberein_zeuge
#print axioms zugriffOk_zeuge

end Gabbro.Grammatik.X86
