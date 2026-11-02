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
module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
    (⟨0, by decide, by decide⟩ : Wert bedD (.int 0 100)) := by rfl

/-- Memory really changes across the step. -/
theorem bedMemWechsel : bedW1.slots true 0 () ≠ bedW0.slots true 0 () := by
  rw [bedW1_slot, bedW0_slot]
  intro hcon
  have hn := congrArg Zahl.n hcon
  simp only [bedV100, Int.reduceEq] at hn

/-- The writer writes `konto`. -/
theorem bedSchreibt_konto : TraegerSchreibt (D := bedD) true (.inl true) = true :=
  by rfl

/-- Nobody writes `config`: the writer does not. -/
theorem bedSchreibt_config_schreiber :
    TraegerSchreibt (D := bedD) true (.inl false) = false := by rfl

/-- Nobody writes `config`: the reader does not write `konto`. -/
theorem bedSchreibt_konto_leser :
    TraegerSchreibt (D := bedD) false (.inl true) = false := by rfl

/-- Nobody writes `config`: the reader does not write `config`. -/
theorem bedSchreibt_config_leser :
    TraegerSchreibt (D := bedD) false (.inl false) = false := by rfl

/-- `konto` is guarded by lock `()`. -/
theorem bedGuard_konto : Bewacht (D := bedD) (.inl true) () :=
  List.mem_singleton.mpr rfl

/-- The head world holds exactly the lock. -/
theorem bedW0_haelt : bedW0.haelt = [()] := by rfl

/-- The writer starts with exactly the lock in hand. -/
theorem bedAnfang_schreib :
    Signatur.anfang bedD (bedD.signatur true) = [Res.held (D := bedD) ()] := by rfl

/-- `konto` is watched by the lock. -/
theorem bedBraucht_konto : bedD.braucht true = [Sum.inl ()] := by rfl

/-- `config` has an empty watch list. -/
theorem bedBraucht_config : bedD.braucht false = [] := by rfl

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


end Gabbro.Grammatik
