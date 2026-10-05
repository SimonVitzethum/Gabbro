/-
  File:      Grammatik/X86/TsoRunInduction.lean
  Subject:   TSO traces to W runs: run induction (lane 1187).

  Follow-up of lane 1143 (`TsoReadBridge.lean`) and `CarrierTraceBridge.lean`:
  those prove PER-STEP bridges (one lowered fragment store/read/drain step
  yields one typed-carrier `SchrittW`). This module proves RUN induction: a
  finite lowered-fragment trace yields a W run (`RufErreichbarW`).

  Covered steps (by construction): no-read store (`store`), committed read
  (`loadCommit`), forwarded read (`loadFwd`) -- exactly the three accepted
  per-step theorems. Drain-only TSO progress yields no W step: it preserves
  the inherited history (`erbtW_schritt`) instead. No LOCK/RMW, no shared
  atomics: the bridge steps quantify over plain table carriers and discharge
  the `rmw` field by refuting the exchange head at an `assignSlot`.
-/
import Grammatik.X86.TSO.Kern.TSOTrace
import Grammatik.X86.Bruecke.CarrierTraceBridge
import Grammatik.X86.Bruecke.TsoReadBridge
import Grammatik.Speichermodell.Maschine.MaschineW

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

variable {D : Deklaration}

/-- The covered fragment-step kinds: a no-read store, a committed read, a
    forwarded read, and drain-only TSO progress (which yields no W step). -/
inductive FragArt where
  | store : FragArt
  | loadCommit : FragArt
  | loadFwd : FragArt
  | drain : FragArt

/-- One bridged fragment step: its kind plus the actual `RufSchrittW` it
    yields. Drain-only progress is refused a W step (`art ≠ .drain`). -/
structure BrueckenSchritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Speichermodell.Ordnung)
    (W W' : RufMaschineW D) (u : Faden) where
  art : FragArt
  lauf : RufSchrittW P O passes ord W u W'
  abgedeckt : art ≠ .drain

/-- A finite lowered-fragment run: snoc-chained bridged steps. -/
inductive BrueckenLauf (P : Programm D) (O : Orakel D) (passes : Nat)
    (ord : D.Glob → Speichermodell.Ordnung) :
    RufMaschineW D → RufMaschineW D → List FragArt → Prop where
  | leer (W : RufMaschineW D) : BrueckenLauf P O passes ord W W []
  | erweitern {W Wm W' : RufMaschineW D} {u : Faden} {arts : List FragArt}
      (rest : BrueckenLauf P O passes ord W Wm arts)
      (s : BrueckenSchritt P O passes ord Wm W' u) :
      BrueckenLauf P O passes ord W W' (arts ++ [s.art])

/-! ## 1. Run induction: a finite lowered-fragment trace yields a W run. -/

/-- **RUN INDUCTION (`brueckenLauf_erreichbar`).** A finite chain of bridged
    fragment steps yields a reached W run from the chain start to its end.
    Proof by induction on the chain: the empty chain is the start run, each
    snoc step appends one `RufSchrittW`. Every premise is used: `h` drives
    the induction, each step through `s.lauf`. -/
theorem brueckenLauf_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat}
    {ord : D.Glob → Speichermodell.Ordnung}
    {W W' : RufMaschineW D} {arts : List FragArt}
    (h : BrueckenLauf P O passes ord W W' arts) :
    RufErreichbarW P O passes ord W W' := by
  induction h with
  | leer => exact RufErreichbarW.start
  | erweitern rest s ih =>
    exact RufErreichbarW.schritt _ _ _ ih s.lauf

/-- Every bridge step is one of the three covered kinds -- never drain-only
    progress, never LOCK/RMW. Uses `s` through both its kind and its
    coverage proof. -/
theorem brueckenSchritt_satz {P : Programm D} {O : Orakel D} {passes : Nat}
    {ord : D.Glob → Speichermodell.Ordnung}
    {W W' : RufMaschineW D} {u : Faden}
    (s : BrueckenSchritt P O passes ord W W' u) :
    s.art = .store ∨ s.art = .loadCommit ∨ s.art = .loadFwd := by
  cases h : s.art with
  | store => exact Or.inl rfl
  | loadCommit => exact Or.inr (Or.inl rfl)
  | loadFwd => exact Or.inr (Or.inr rfl)
  | drain => exact absurd h s.abgedeckt

/-- **PLANTED REFUSAL:** no bridge step is drain-only TSO progress. A pure
    drain advances the trace clock but writes no carrier, so it yields no
    `SchrittW`; it preserves the inherited history instead
    (`drain_erhaelt_erbt`). -/
theorem brueckenSchritt_kein_drain {P : Programm D} {O : Orakel D}
    {passes : Nat} {ord : D.Glob → Speichermodell.Ordnung}
    {W W' : RufMaschineW D} {u : Faden}
    (s : BrueckenSchritt P O passes ord W W' u) : s.art ≠ .drain :=
  s.abgedeckt

/-- Exact run coverage: every kind on a bridged run is covered. Induction
    over the run; the snoc kind through `brueckenSchritt_satz`. -/
theorem brueckenLauf_nur_abgedeckt {P : Programm D} {O : Orakel D}
    {passes : Nat} {ord : D.Glob → Speichermodell.Ordnung}
    {W W' : RufMaschineW D} {arts : List FragArt}
    (h : BrueckenLauf P O passes ord W W' arts) :
    ∀ a ∈ arts, a = .store ∨ a = .loadCommit ∨ a = .loadFwd := by
  induction h with
  | leer =>
    intro a ha
    simp at ha
  | erweitern rest s ih =>
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with hm | rfl
    · exact ih a hm
    · exact brueckenSchritt_satz s

/-- The coverage enumeration: every kind is either covered or drain-only
    progress (which the run induction refuses). -/
theorem fragArt_abgedeckt_oder_drain (a : FragArt) :
    a = .store ∨ a = .loadCommit ∨ a = .loadFwd ∨ a = .drain := by
  cases a with
  | store => exact Or.inl rfl
  | loadCommit => exact Or.inr (Or.inl rfl)
  | loadFwd => exact Or.inr (Or.inr (Or.inl rfl))
  | drain => exact Or.inr (Or.inr (Or.inr rfl))

/-! ## 2. Drain-only progress preserves the inheritance; RMW rides along. -/

/-- Drain-only TSO progress preserves the inherited history for the run
    consumer: the named accepted `erbtW_schritt`. Every premise is used. -/
theorem drain_erhaelt_erbt (n n' : SpurKnoten) (W : RufMaschineW D)
    (u : Faden) (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse)
    (hErbt : ErbtW n W u c e a) (hinv : SpurInv n)
    (hs : SpurSchritt n n') : ErbtW n' W u c e a :=
  erbtW_schritt n n' W u c e a hErbt hinv hs

/-- The RMW atomicity obligation rides along every bridged step: at an
    exchange head the write sits directly above the read message. This is
    the accepted `SchrittW.rmw` field unpacked; the per-step bridges
    discharge it by refuting the exchange head at an `assignSlot`, so no
    LOCK/RMW step enters a bridged run. Every premise is used. -/
theorem brueckenSchritt_rmw {P : Programm D} {O : Orakel D} {passes : Nat}
    {ord : D.Glob → Speichermodell.Ordnung}
    {W W' : RufMaschineW D} {u : Faden}
    (s : BrueckenSchritt P O passes ord W W' u)
    (g : D.Glob) (h : ExchangeKopf W.g u g) :
    ∃ (wahl : D.Tab ⊕ D.Glob → NachrichtW D) (neu : D.Tab ⊕ D.Glob → Nat),
      neu (.inr g) = (wahl (.inr g)).ts + 1 := by
  obtain ⟨σ, M'', wahl, neu, hSW⟩ := s.lauf
  exact ⟨wahl, neu, hSW.rmw g h⟩

/-! ## 3. Stale views: no global value for an unflushed store. -/

/-- **STALE DIVERGENCE (reused):** the accepted reads-bridge refusal --
    in `sbNach2` core 0 loads `0` at `sbY` while core 1 holds the
    unflushed `1` there. -/
theorem lauf_stale_kein_globaler_wert :
    ∃ (s : TSOZustand) (a : Adresse),
      loadByte s 0 a ≠ loadByte s 1 a :=
  stale_kein_globaler_wert

/-- **GLOBAL-VALUE REFUSAL:** no single byte value agrees with both cores
    at `sbY` in `sbNach2` -- a validator that needs one global value per
    address refuses this state. Every premise is used: `h0`/`h1` fix the
    two core observations, the accepted stale facts close them. -/
theorem lauf_global_verweigert (v : Byte)
    (h0 : loadByte sbNach2 0 sbY = some v)
    (h1 : loadByte sbNach2 1 sbY = some v) : False := by
  have e0 : loadByte sbNach2 0 sbY = some 0 := sb_beide_laden_null.1
  have e1 : loadByte sbNach2 1 sbY = some sbEins := by decide
  rw [e0] at h0
  rw [e1] at h1
  simp only [Option.some.injEq] at h0 h1
  rw [← h0] at h1
  exact absurd h1 (by decide)

/-! ## 4. Joint witness: a one-step bridged run that changes memory. -/

/-- **JOINT WITNESS for `brueckenLauf_erreichbar`.** Every premise holds
    jointly on concrete values: the witness declaration `witD` with one
    table the witness function writes (`ctHw`), a one-step bridged run
    that changes the source slot `0 → 42` and the mapped target bytes,
    the inherited history over the drain end, a reached one-flush trace
    with two distinct timestamps, a pending foreign byte outside the
    footprint, the stale-view divergence (core 0 canonically reads zero
    where core 1 forwards seven), and the reached two-core trace whose
    two flushes observably change canonical memory at two addresses.
    Non-degenerate: a written table, a memory-changing source step and
    target drain, two cores, forwarding visible to the owner only. -/
theorem brueckenLauf_erreichbar_zeuge :
    ∃ (W' : RufMaschineW witD) (arts : List FragArt),
      BrueckenLauf ctProg witO 0 (fun g => nomatch g) (RufStartW ctM) W' arts ∧
      RufErreichbarW ctProg witO 0 (fun g => nomatch g) (RufStartW ctM) W' ∧
      arts = [.store] ∧
      (vertragVon witD ()).schreibt () = true ∧
      (witSigma.slots () 0 ()).n = 0 ∧
      (∃ σ' : World witD, (σ'.slots () 0 ()).n = 42) ∧
      witM.bytes witA ≠ witM'.bytes witA ∧
      ErbtW (spurStart ctS11) (RufStartW ctM) 0 0 (Sum.inl ()) witA ∧
      SpurInv (spurStart ctS11) ∧
      SpurErreichbar ctNA ctNB ∧ ctNA.frisch ≠ ctNB.frisch ∧
      ctS4.puffer 1 = [⟨ctF, ctFv⟩] ∧ ctF ∉ Fuss witA ∧
      loadByte ctS4 0 ctF = some (BitVec.ofNat 8 0) ∧
      loadByte ctS4 1 ctF = some ctFv ∧
      SpurErreichbar spurW0 spurW4 ∧
      spurW0.tso.mem.bytes sbX ≠ spurW4.tso.mem.bytes sbX ∧
      spurW0.tso.mem.bytes sbY ≠ spurW4.tso.mem.bytes sbY := by
  obtain ⟨σ', ρ', hExec, hTgt, hBefore, hAfter, hBytes, hErbt, hInv,
    hErr, hUhr, hBuf, hFresh, hSt0, hSt1, W', σm, M'', wahl, neu, hSW,
    hVal, hRep⟩ := schrittW_aus_gruppen_drain_zeuge
  have hRS : RufSchrittW ctProg witO 0 (fun g => nomatch g)
      (RufStartW ctM) 0 W' :=
    ⟨σm, M'', wahl, neu, hSW⟩
  have hL : BrueckenLauf ctProg witO 0 (fun g => nomatch g)
      (RufStartW ctM) W' ([] ++ [FragArt.store]) :=
    .erweitern (.leer _)
      { art := .store, lauf := hRS, abgedeckt := fun h => by cases h }
  have hR := brueckenLauf_erreichbar hL
  exact ⟨W', [] ++ [FragArt.store], hL, hR, rfl, ctHw, hBefore, ⟨σ', hAfter⟩,
    hBytes, hErbt, hInv, hErr, hUhr, hBuf, hFresh, hSt0, hSt1,
    spurW_erreichbar, spurW_speicher.1, spurW_speicher.2⟩

/- CUTS:
    - Proved here: run induction (`brueckenLauf_erreichbar`): a finite
      chain of bridged fragment steps yields a reached W run
      (`RufErreichbarW`); exact step coverage (`brueckenSchritt_satz`,
      `brueckenLauf_nur_abgedeckt`, `fragArt_abgedeckt_oder_drain`):
      every bridged step is a no-read store, a committed read, or a
      forwarded read -- the three accepted per-step theorems
      (`schrittW_aus_gruppen_drain`,
      `schrittW_aus_lesefragment_gruppe`,
      `schrittW_aus_lesefragment_weiterleitung`); drain-only TSO
      progress is refused a W step (`brueckenSchritt_kein_drain`) and
      preserves the inherited history instead (`drain_erhaelt_erbt`,
      the accepted `erbtW_schritt`); the RMW atomicity obligation rides
      along (`brueckenSchritt_rmw`); the stale-view refusals
      (`lauf_stale_kein_globaler_wert`, `lauf_global_verweigert`): an
      unflushed store has no global value; a joint non-degenerate
      witness (`brueckenLauf_erreichbar_zeuge`): a written table, a
      memory-changing source step (`0 → 42`) and target drain, two
      cores with observably changed canonical memory, a buffered store
      visible via forwarding to the owner only.
    - NOT proved here, left OPEN: LOCK/RMW steps (the `rmw` field is
      carried, never constructed from a LOCK step); shared atomics
      (`.inr` carriers with `HavocA`/`GeteiltV` environments); the GX
      refinement consuming these runs; `valX86_sound`; scheduling,
      fairness, progress, timing; interrupts, devices, MMIO, DMA.
    - No `HwAdapter`/`HwSchritt` embedding is claimed: the consumer of
      this run induction is machine W, not `HwMaschine`; the TSO side
      reuses the accepted `TSOTrace`/`SourceMemory`/`WordAccessGrouping`
      vocabulary unchanged (never copied).
-/

#print axioms FragArt
#print axioms BrueckenSchritt
#print axioms BrueckenLauf
#print axioms brueckenLauf_erreichbar
#print axioms brueckenSchritt_satz
#print axioms brueckenSchritt_kein_drain
#print axioms brueckenLauf_nur_abgedeckt
#print axioms fragArt_abgedeckt_oder_drain
#print axioms drain_erhaelt_erbt
#print axioms brueckenSchritt_rmw
#print axioms lauf_stale_kein_globaler_wert
#print axioms lauf_global_verweigert
#print axioms brueckenLauf_erreichbar_zeuge

end Gabbro.Grammatik.X86
