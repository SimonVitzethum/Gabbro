/-
  File:      Grammatik/DisziplinBedarf.lean
  Subject:   Guards only where they are needed (D3).

  The discipline package `invariantenKontext_aus_disziplin`
  (`InterferenzAllgemein.lean`) requires `hGuardEx`: every carrier has a
  guard lock. Ordinary programs leave unshared or read-only carriers
  unguarded, so the premise fits nothing ordinary. This file proves the
  narrowed version: only carriers that some member thread WRITES need a
  guard (`hGuardBedarf`). A carrier no member writes keeps its slots
  along the whole chain (`traegerStill_ohneSchreiber`, via the
  non-writer preservation `nichtschreiber_erhaelt`); a written carrier
  runs through the existing per-carrier chain lemma
  (`hinv_kette_aus_disziplin`), exactly as the old proof did.
-/
import Grammatik.InterferenzAllgemein
import Grammatik.Maschine
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A carrier no member thread writes keeps its invariant along the
    chain: entry gives the head, every step is a non-writer step for
    this carrier (`nichtschreiber_erhaelt` over the whole-frame step),
    and `kette_erhaelt` folds both down the chain. -/
theorem traegerStill_ohneSchreiber (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (I : TraegerInv (D := D))
    (c : D.Tab ⊕ D.Glob) (Wc : D.Tab → Bool) (Gc : D.Glob → Bool)
    (hAb : HaengtAb Wc Gc (I.inv c))
    (hFrameT : ∀ t : D.Tab, Wc t = true → c = .inl t)
    (hFrameG : ∀ x : D.Glob, Gc x = true → c = .inr x)
    (hNie : ∀ (g : Faden), g ∈ J.faeden → TraegerSchreibt (J.code g) c = false)
    (hEntry : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv c σ₀) :
    ∀ (k : Nat) (σ : World D), J.welten[k]? = some σ → I.inv c σ := by
  refine kette_erhaelt J.welten J.schrittFaden J.hKette (I.inv c) hEntry ?_
  intro k g vor nach hkg hkv hkn
  obtain ⟨hgm, _⟩ := J.hSchritt k g vor nach hkg hkv hkn
  exact nichtschreiber_erhaelt Nb J I c Wc Gc hAb hFrameT hFrameG
    k g vor nach hkg hkv hkn (hNie g hgm)

/-- The derived context with guards only where they are needed. A
    carrier some member writes runs through the per-carrier chain
    lemma (`hinv_kette_aus_disziplin`) with the guard supplied by
    `hGuardBedarf` -- the old proof shape. A carrier no member writes
    keeps its invariant by `traegerStill_ohneSchreiber` above, with no
    guard owed. Unguarded carriers are exactly the unwritten ones, so
    their invariant is stable along the chain. -/
theorem invariantenKontext_aus_disziplin_bedarf (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb) (I : TraegerInv (D := D))
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardBedarf : ∀ c : D.Tab ⊕ D.Glob,
      (∃ g, g ∈ J.faeden ∧ TraegerSchreibt (J.code g) c = true) →
        ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g)) :
    InvariantenKontext Nb J I := by
  intro c σ hmem
  obtain ⟨k, hk⟩ := kette_belegt_of_mem J.welten σ hmem
  by_cases hW : (∃ g, g ∈ J.faeden ∧ TraegerSchreibt (J.code g) c = true)
  · obtain ⟨L, hL⟩ := hGuardBedarf c hW
    exact hinv_kette_aus_disziplin Nb J I c L (Wc c) (Gc c) (hAbD c) (hFrameTD c)
      (hFrameGD c) hL (hEntry c)
      (fun k g vor nach hgm hkg hkv hkn hW hHold =>
        hReturn c L k g vor nach hL hgm hkg hkv hkn hW hHold)
      (fun k g vor nach hgm hkg hkv hkn hW =>
        hWatch c L k g vor nach hL hgm hkg hkv hkn hW)
      k σ hk
  · have hNie : ∀ (g : Faden), g ∈ J.faeden →
        TraegerSchreibt (J.code g) c = false := by
      intro g hg
      cases heq : TraegerSchreibt (J.code g) c with
      | true => exact absurd ⟨g, hg, heq⟩ hW
      | false => rfl
    exact traegerStill_ohneSchreiber Nb J I c (Wc c) (Gc c) (hAbD c)
      (hFrameTD c) (hFrameGD c) hNie (hEntry c) k σ hk

/-! ## Witness: one written guarded carrier, one read-only unguarded carrier.

  The reference fixture `refD` has a single carrier, so the old `hGuardEx`
  cannot fail there. This witness uses its own two-table declaration
  `bedD`: table `true` (`konto`) is written and guarded by lock `()`;
  table `false` (`config`) is never written and has an empty watch list.
  The joint run `bedJ` has one member thread running the writer, over
  two worlds where the single step stores `100` into `konto` (memory
  really changes; `config` is untouched). The old guard-existence
  premise is false here (`bedGuardEx_falsch`, separate lemma). -/

/-- Writer signature: holds the lock, writes only table `true`. -/
def bedSigSchreib : Signatur Bool Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun t => t
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Reader signature: holds nothing, writes nothing. -/
def bedSigLies : Signatur Bool Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Two-table declaration: `true` is the shared guarded account table,
    `false` the unshared unguarded config table. -/
def bedD : Deklaration where
  Tab := Bool
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some true | 1 => some false | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun | true => true | false => false
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun | true => [Sum.inl ()] | false => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => bedSigSchreib | _ => bedSigLies
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t ht => by
    cases t with
    | true => decide
    | false => exact absurd ht (by decide)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-- Start memory: every slot reads `0`. -/
def bedSp0 : Speicher bedD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Head world: start memory, lock `()` taken. -/
def bedW0 : World bedD := bedSp0.welt [Ereignis.nimmt (D := bedD) () []]

/-- The stored value `100` in range. -/
def bedV100 : Wert bedD (.int 0 100) := ⟨100, by decide, by decide⟩

/-- Second world: `konto[0] := 100`, trace unchanged. -/
def bedW1 : World bedD := bedW0.storeSlot true 0 () bedV100

/-- The step stores the cap at `konto[0]`. -/
theorem bedW1_slot : bedW1.slots true 0 () = bedV100 :=
  storeSlot_hit bedW0 true 0 () bedV100

/-- The head world reads `0` at `konto[0]`. -/
theorem bedW0_slot : bedW0.slots true 0 () =
    (⟨0, by decide, by decide⟩ : Wert bedD (.int 0 100)) := rfl

/-- Memory really changes across the step. -/
theorem bedMemWechsel : bedW1.slots true 0 () ≠ bedW0.slots true 0 () := by
  rw [bedW1_slot, bedW0_slot]
  intro hcon
  have hn := congrArg Zahl.n hcon
  simp [bedV100] at hn

/-- The writer writes `konto`. -/
theorem bedSchreibt_konto : TraegerSchreibt (D := bedD) true (.inl true) = true :=
  rfl

/-- Nobody writes `config`: the writer does not. -/
theorem bedSchreibt_config_schreiber :
    TraegerSchreibt (D := bedD) true (.inl false) = false := rfl

/-- Nobody writes `config`: the reader does not write `konto`. -/
theorem bedSchreibt_konto_leser :
    TraegerSchreibt (D := bedD) false (.inl true) = false := rfl

/-- Nobody writes `config`: the reader does not write `config`. -/
theorem bedSchreibt_config_leser :
    TraegerSchreibt (D := bedD) false (.inl false) = false := rfl

/-- `konto` is guarded by lock `()`. -/
theorem bedGuard_konto : Bewacht (D := bedD) (.inl true) () :=
  List.mem_singleton.mpr rfl

/-- The head world holds exactly the lock. -/
theorem bedW0_haelt : bedW0.haelt = [()] := rfl

/-- The writer starts with exactly the lock in hand. -/
theorem bedAnfang_schreib :
    Signatur.anfang bedD (bedD.signatur true) = [Res.held (D := bedD) ()] := rfl

/-- `konto` is watched by the lock. -/
theorem bedBraucht_konto : bedD.braucht true = [Sum.inl ()] := rfl

/-- `config` has an empty watch list. -/
theorem bedBraucht_config : bedD.braucht false = [] := rfl

/-- The writer step stays in the writer frame: `config` slots ride
    along, globals are vacuous over `Empty`. -/
theorem bedRahmen :
    Rahmen (bedD.schreibt true) (bedD.gschreibt true) bedW0 bedW1 := by
  constructor
  · intro t ht k f
    cases t with
    | true => exact absurd ht (by decide)
    | false => rfl
  · intro g _
    exact nomatch g

/-- No threads are declared to share the witness run. -/
def bedNb : Nebeneinander := fun _ _ => False

/-- The joint witness run: thread `0` runs the writer, over the two
    worlds where the single step stores `100` into `konto`. -/
def bedJ : GemeinsamerLauf (D := bedD) bedNb :=
  { faeden := [0]
    code := fun _ => true
    eintritt := fun _ => bedW0
    welten := [bedW0, bedW1]
    schrittFaden := [0]
    l := []
    hKette := by rfl
    hSchritt := by
      intro k f vor nach hkg hkv hkn
      cases k with
      | zero =>
        have hf : 0 = f := by simpa using hkg
        have hv : bedW0 = vor := by simpa using hkv
        have hn : bedW1 = nach := by simpa using hkn
        subst hf
        subst hv
        subst hn
        exact ⟨by simp, bedRahmen⟩
      | succ n =>
        cases n with
        | zero => simp at hkn
        | succ n => simp at hkv
    hPaar := by
      intro f hf g hg hne
      simp at hf hg
      subst hf
      subst hg
      exact absurd rfl hne
    hGesittet := by
      show Gesittet ([] : Lauf bedD)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro f j
        have hsp : Lauf.spur ([] : Lauf bedD) f j = [] := by simp [Lauf.spur]
        rw [hsp]
        exact konsistent_nil
      · intro f j e he
        have hsp : Lauf.spur ([] : Lauf bedD) f j = [] := by simp [Lauf.spur]
        rw [hsp] at he
        simp at he
      · intro j f L h hi g hne
        simp at hi
      · intro i j f g m s s' ei ej hi hj hm hm'
        simp at hi
      · intro i j f g o ei ej hi hj ht1 ht2 hu
        simp at hi
    hBeschraenkt := by
      show BeschraenkteVerschraenkung (D := bedD) bedNb ([] : Lauf bedD)
      intro i j f g ei ej hi hj hne
      simp at hi
    hEintritt := by
      intro f hf
      simp at hf
      subst hf
      show HeldGenau (Signatur.anfang bedD (bedD.signatur true)) bedW0.haelt
      rw [bedAnfang_schreib]
      intro L
      have eL : L = () := by cases L <;> rfl
      have eH : bedW0.haelt = [()] := rfl
      rw [eH, eL]
      constructor
      · intro hL
        have heq : Res.held (D := bedD) L = Res.held (D := bedD) () :=
          (List.mem_singleton.mp hL)
        cases heq
        exact List.mem_singleton.mpr rfl
      · intro hL
        have heq : L = () :=
          (List.mem_singleton.mp (eH ▸ hL))
        cases heq
        exact List.mem_singleton.mpr rfl
    hSchuld := by
      intro f hf
      simp at hf
      subst hf
      intro i hs
      exact nomatch i
    hInvSicht := by
      intro f hf
      simp at hf
      subst hf
      intro i hs
      exact nomatch i
  }

/-- Equation helpers for rewriting in the witness proofs. -/
theorem bedJ_faeden : bedJ.faeden = [0] := rfl

theorem bedJ_welten : bedJ.welten = [bedW0, bedW1] := rfl

/-- Trivially true carrier invariant; its discipline holds because the
    writer holds the lock over the one carrier it writes. -/
def bedI : TraegerInv (D := bedD) where
  inv := fun _ _ => True
  disziplin := by
    intro f c h
    cases c with
    | inl t =>
      cases t with
      | true =>
        cases f with
        | true =>
          intro w hw
          rw [bedBraucht_konto] at hw
          have hw2 : w = Sum.inl () := List.mem_singleton.mp hw
          subst hw2
          rw [bedAnfang_schreib]
          exact List.mem_singleton.mpr rfl
        | false => exact absurd h (by decide)
      | false =>
        cases f with
        | true => exact absurd h (by decide)
        | false => exact absurd h (by decide)
    | inr g => exact nomatch g

/-- Singleton table footprint: the witness of the carrier itself. -/
def bedWc : (c : bedD.Tab ⊕ bedD.Glob) → bedD.Tab → Bool
  | .inl t', t => decide (t = t')
  | .inr g, _ => nomatch g

/-- Empty global footprint: there are no globals. -/
def bedGc : (c : bedD.Tab ⊕ bedD.Glob) → bedD.Glob → Bool
  | _, x => nomatch x

/-- The trivial invariant hangs on any footprint. -/
theorem bedAb : ∀ c, HaengtAb (bedWc c) (bedGc c) (bedI.inv c) := by
  intro c σ σ' _
  exact Iff.rfl

/-- The table footprint is a singleton frame. -/
theorem bedFrameT :
    ∀ (c : bedD.Tab ⊕ bedD.Glob) (t : bedD.Tab),
      bedWc c t = true → c = .inl t := by
  intro c t h
  cases c with
  | inl t' =>
    simp only [bedWc] at h
    have ht : t = t' := of_decide_eq_true h
    subst ht
    rfl
  | inr g => exact nomatch g

/-- The global footprint is a singleton frame, vacuously. -/
theorem bedFrameG :
    ∀ (c : bedD.Tab ⊕ bedD.Glob) (x : bedD.Glob),
      bedGc c x = true → c = .inr x := by
  intro c x _
  exact nomatch x

/-- Only `konto` is ever written, and it is guarded. -/
theorem bedGuardBedarf : ∀ c : bedD.Tab ⊕ bedD.Glob,
    (∃ g, g ∈ bedJ.faeden ∧ TraegerSchreibt (bedJ.code g) c = true) →
      ∃ L : bedD.Lock, Bewacht (D := bedD) c L := by
  intro c h
  obtain ⟨g, hg, hw⟩ := h
  rw [bedJ_faeden] at hg
  simp at hg
  subst hg
  cases c with
  | inl t =>
    cases t with
    | true => exact ⟨(), bedGuard_konto⟩
    | false => exact absurd hw (by decide)
  | inr x => exact nomatch x

/-- Entry holds: the invariant is trivially true. -/
theorem bedEntry : ∀ (c : bedD.Tab ⊕ bedD.Glob) (σ₀ : World bedD),
    bedJ.welten[0]? = some σ₀ → bedI.inv c σ₀ := by
  intro c σ₀ h
  rw [bedJ_welten] at h
  have h0 : bedW0 = σ₀ := by simpa using h
  subst h0
  trivial

/-- Return re-establishes the trivial invariant; the chain position is
    pinned by the two-element world list. -/
theorem bedReturn : ∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat)
    (g : Faden) (vor nach : World bedD),
    Bewacht (D := bedD) c L → g ∈ bedJ.faeden → bedJ.schrittFaden[k]? = some g →
      bedJ.welten[k]? = some vor → bedJ.welten[k + 1]? = some nach →
        TraegerSchreibt (bedJ.code g) c = true → L ∈ bedD.haelt (bedJ.code g) →
          bedI.inv c nach := by
  intro c L k g vor nach hB hg hkg hkv hkn hw hh
  rw [bedJ_welten] at hkn
  have hk0 : k = 0 := by
    have hlen : k + 1 < [bedW0, bedW1].length := lt_of_belegt _ _ _ hkn
    simp at hlen
    omega
  subst hk0
  have hn : bedW1 = nach := by simpa using hkn
  subst hn
  trivial

/-- Every writing step holds the guard: the only written carrier is
    `konto`, whose watch list forces the lock. -/
theorem bedWatch : ∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat)
    (g : Faden) (vor nach : World bedD),
    Bewacht (D := bedD) c L → g ∈ bedJ.faeden → bedJ.schrittFaden[k]? = some g →
      bedJ.welten[k]? = some vor → bedJ.welten[k + 1]? = some nach →
        TraegerSchreibt (bedJ.code g) c = true → L ∈ bedD.haelt (bedJ.code g) := by
  intro c L k g vor nach hB hg hkg hkv hkn hw
  rw [bedJ_faeden] at hg
  simp at hg
  subst hg
  rw [bedJ_welten] at hkn
  have hk0 : k = 0 := by
    have hlen : k + 1 < [bedW0, bedW1].length := lt_of_belegt _ _ _ hkn
    simp at hlen
    omega
  subst hk0
  cases c with
  | inl t =>
    cases t with
    | true =>
      have hL : L = () := by
        simp only [Bewacht, bedBraucht_konto] at hB
        have h2 : Sum.inl L = Sum.inl () := List.mem_singleton.mp hB
        injection h2 with hL'
      subst hL
      show () ∈ ([()] : List bedD.Lock)
      exact List.mem_singleton.mpr rfl
    | false => exact absurd hw (by decide)
  | inr x => exact nomatch x

/-- The old guard-existence premise is FALSE here: `config` has no
    guard. This is the separate lemma the narrowed premise improves on. -/
theorem bedGuardEx_falsch :
    ¬ ∀ c : bedD.Tab ⊕ bedD.Glob,
      ∃ L : bedD.Lock, Bewacht (D := bedD) c L := by
  intro h
  obtain ⟨L, hL⟩ := h (.inl false)
  simp only [Bewacht, bedBraucht_config] at hL
  simp at hL

/-- **Inhabitation (rule 13).** All premises of
    `invariantenKontext_aus_disziplin_bedarf` hold jointly on the
    two-table witness (`bedD`/`bedNb`/`bedJ`/`bedI`): `konto` is written
    and guarded, `config` is only read and unguarded. The old
    `hGuardEx` is false there (`bedGuardEx_falsch`), so the narrowed
    premise is strictly weaker. Non-degeneracy: the writer writes
    `konto` (`bedSchreibt_konto`), the chain step changes memory
    (`bedMemWechsel`), and the reference fixture contributes a reached
    run that moves memory (`refB_pc_erreicht`/`refB_pc_schreibt`). -/
theorem invariantenKontext_aus_disziplin_bedarf_zeuge :
    (∀ c, HaengtAb (bedWc c) (bedGc c) (bedI.inv c))
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (t : bedD.Tab),
        bedWc c t = true → c = .inl t)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (x : bedD.Glob),
        bedGc c x = true → c = .inr x)
    ∧ (∀ c : bedD.Tab ⊕ bedD.Glob,
        (∃ g, g ∈ bedJ.faeden ∧ TraegerSchreibt (bedJ.code g) c = true) →
          ∃ L : bedD.Lock, Bewacht (D := bedD) c L)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (σ₀ : World bedD),
        bedJ.welten[0]? = some σ₀ → bedI.inv c σ₀)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat) (g : Faden)
        (vor nach : World bedD),
        Bewacht (D := bedD) c L → g ∈ bedJ.faeden →
          bedJ.schrittFaden[k]? = some g → bedJ.welten[k]? = some vor →
            bedJ.welten[k + 1]? = some nach →
              TraegerSchreibt (bedJ.code g) c = true →
                L ∈ bedD.haelt (bedJ.code g) → bedI.inv c nach)
    ∧ (∀ (c : bedD.Tab ⊕ bedD.Glob) (L : bedD.Lock) (k : Nat) (g : Faden)
        (vor nach : World bedD),
        Bewacht (D := bedD) c L → g ∈ bedJ.faeden →
          bedJ.schrittFaden[k]? = some g → bedJ.welten[k]? = some vor →
            bedJ.welten[k + 1]? = some nach →
              TraegerSchreibt (bedJ.code g) c = true →
                L ∈ bedD.haelt (bedJ.code g))
    ∧ InvariantenKontext bedNb bedJ bedI
    ∧ (¬ ∀ c : bedD.Tab ⊕ bedD.Glob,
        ∃ L : bedD.Lock, Bewacht (D := bedD) c L)
    ∧ (∃ f : bedD.Fn, TraegerSchreibt f (.inl true) = true)
    ∧ (∃ k vor nach, bedJ.welten[k]? = some vor ∧
        bedJ.welten[k + 1]? = some nach ∧
        vor.slots true 0 () ≠ nach.slots true 0 ())
    ∧ ∃ (M : GenMaschine refD) (pc : PCStand),
        PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  refine ⟨bedAb, bedFrameT, bedFrameG, bedGuardBedarf, bedEntry, bedReturn,
    bedWatch, ?_, bedGuardEx_falsch, ⟨true, bedSchreibt_konto⟩,
    ⟨0, bedW0, bedW1, by simp [bedJ_welten], by simp [bedJ_welten],
      Ne.symm bedMemWechsel⟩,
    refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩
  exact invariantenKontext_aus_disziplin_bedarf bedNb bedJ bedI bedWc bedGc
    bedAb bedFrameT bedFrameG bedGuardBedarf bedEntry bedReturn bedWatch

/-! ## CUTS:
  - Proved: `traegerStill_ohneSchreiber` (helper), the target
    `invariantenKontext_aus_disziplin_bedarf`, and its rule-13 witness
    `invariantenKontext_aus_disziplin_bedarf_zeuge` with the two-table
    fixture (`bedD`, `bedJ`, `bedI`, footprints, all premise proofs) and
    the separate `bedGuardEx_falsch` lemma.
  - The witness invariant is trivially true, so `bedEntry`/`bedReturn`
    use only the world-identification hypotheses; the guard hypotheses
    of `bedReturn` are unused there (same shape as the merged precedent
    `refInv81_release`, whose reachability hypothesis is documented
    redundant). A minimal one-step chain cannot exercise restoration.
  - The witness is NOT on the reference fixture: `refD` has a single
    carrier, so the old `hGuardEx` cannot fail there. The task's demand
    (one written guarded carrier plus one read-only unguarded carrier)
    forces a two-carrier declaration; see the report.
-/

#print axioms Gabbro.Grammatik.traegerStill_ohneSchreiber
#print axioms Gabbro.Grammatik.invariantenKontext_aus_disziplin_bedarf
#print axioms Gabbro.Grammatik.invariantenKontext_aus_disziplin_bedarf_zeuge
#print axioms Gabbro.Grammatik.bedGuardEx_falsch

end Gabbro.Grammatik
