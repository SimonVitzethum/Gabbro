/-
  File:      Grammatik/X86/TsoGxRefine.lean
  Subject:   From W runs to the GX refinement: the missing target leg (lane 1215).

  Follow-up of lane 1187 (`TsoRunInduction.lean`): bridged lowered-fragment
  traces yield W runs (`brueckenLauf_erreichbar`) for fragments without
  LOCK/shared atomics. This module states the GX refinement consuming those
  runs for shared atomic carriers (`HavocA`/`GeteiltV`, `.inr` carriers,
  `SchwachX`, `schwach_ist_gX`): what a target run of the lowered fragment
  guarantees about the GX machine's shared-atomic reads.

  Proved: the unconditional GX embedding of G steps (`gx_aus_g` reused);
  the conditional single-step and run refinement (the DRF/checker premises
  of `schwach_ist_gX` stay explicit -- they are the exact remaining
  obligation, never assumed); the `GeteiltV` specialization; the rely fact
  that no atomic environment touches a non-admitted carrier; the LOCK-leg
  disjointness (a forwarding core refuses the LOCK plug). The consumer is
  machine GX, not `HwMaschine`, so no new `HwAdapter` is defined (the
  accepted `tsoRmwAdapter` is reused); no existing file is changed except
  the one `import` line in `Grammatik.lean`.
-/
import Grammatik.X86.Bruecke.TsoRunInduction
import Grammatik.X86.Bruecke.TsoRmwBridge
import Grammatik.Speichermodell.Atomar.AtomarW
import Grammatik.Speichermodell.Atomar.AtomarLauf
import Grammatik.Zielsatz.Kern.Spec

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
variable {Tg : D.Tab ⊕ D.Glob → Prop}

/-! ## 1. GX embedding of G steps (unconditional). -/

/-- **GX EMBEDDING (`gxSchrittAusG`).** Every G step is a GX step, for any
    shared-atomic set: present G's own memory. The accepted `gx_aus_g`,
    named for the fragment consumer. The premise `hs` is the proof. -/
theorem gxSchrittAusG {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') :
    RufSchrittGX P O passes Tg M u M' :=
  gx_aus_g hs

/-- **GX RUN EMBEDDING (`gxLaufAusG`).** Every G run is a GX run, for any
    shared-atomic set. The accepted `gx_aus_g_lauf`, named for the
    fragment consumer. The premise `hr` drives the induction. -/
theorem gxLaufAusG {M0 M : RufMaschineG D}
    (hr : RufErreichbarG P O passes M0 M) :
    RufErreichbarGX P O passes Tg M0 M :=
  gx_aus_g_lauf hr

/-! ## 2. Single-step W-to-GX refinement (conditional). -/

variable {fs : List D.Fn} {K : Faden → D.Fn → Bool}
variable {sp : Gabbro.Grammatik.Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
variable {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool}
variable {ord : D.Glob → Speichermodell.Ordnung}

/-- **STEP REFINEMENT (`brueckenSchrittGx`).** A bridged fragment step from
    a W machine reached from the weak start over a G start refines to a GX
    step with the presented memory, and the presented memory IS G's memory
    at every carrier outside the shared atomics `Tg`: the ONLY freedom GX
    exercises over the fragment run is answering the shared-atomic reads.
    The accepted `schwach_ist_gX` applied to the step's `RufSchrittW`.
    Every premise is used: the DRF/checker premises feed `schwach_ist_gX`,
    `hr` the reachability, `s` the step. The DRF premises are the exact
    remaining obligation (checker + start-anchoring), never assumed. -/
theorem brueckenSchrittGx
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S lok Tg f)
    (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hex : StartExklusiv init)
    {W W' : RufMaschineW D} {u : Faden}
    (hr : RufErreichbarW P O passes ord (RufStartW (RufStartG P sp init)) W)
    (s : BrueckenSchritt P O passes ord W W' u) :
    ∃ σ : Gabbro.Grammatik.Speicher D, RufSchrittGX P O passes Tg W.g u W'.g ∧
      ∀ c, ¬ Tg c → TraegerGleich σ W.g.speicher c := by
  obtain ⟨σ, M'', wahl, neu, hSW⟩ := s.lauf
  exact ⟨σ, schwach_ist_gX hO hvoll hAbg hWurzel hFuss hlokK hTA hex hr hSW⟩

/-! ## 3. Run refinement: a start-anchored bridged run yields a GX run. -/

/-- **RUN REFINEMENT (`brueckenLaufGx`).** A finite bridged fragment run
    anchored at the weak start over a G start refines to a reached GX run
    ending at the run's G-part. Induction on the run: the empty run is the
    GX start; each snoc step appends one GX step via `brueckenSchrittGx`,
    whose reachability premise is the prefix run through
    `brueckenLauf_erreichbar`. Every premise is used: the DRF premises in
    every step, `h` driving the induction. -/
theorem brueckenLaufGx
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S lok Tg f)
    (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hTA : ∀ c, Tg c → AtomarAusgenommen c) (hex : StartExklusiv init)
    {W' : RufMaschineW D} {arts : List FragArt}
    (h : BrueckenLauf P O passes ord (RufStartW (RufStartG P sp init)) W' arts) :
    RufErreichbarGX P O passes Tg (RufStartG P sp init) W'.g := by
  induction h with
  | leer => exact .start
  | erweitern rest s ih =>
    have hr := brueckenLauf_erreichbar rest
    obtain ⟨σ, M'', wahl, neu, hSW⟩ := s.lauf
    have hGX :=
      (schwach_ist_gX hO hvoll hAbg hWurzel hFuss hlokK hTA hex hr hSW).1
    exact .schritt _ _ _ ih hGX

/-! ## 4. The admitted shared atomics: the `GeteiltV` form. -/

/-- An admitted shared atomic is atomic: `GeteiltV` carries
    `AtomarAusgenommen`. Uses `h` through both of its layers. -/
theorem geteiltVAtomar [DecidableEq D.Fn] {ws : List D.Fn} {c : D.Tab ⊕ D.Glob}
    (h : Zielsatz.GeteiltV P ws c) : AtomarAusgenommen c :=
  h.1.1

/-- **RUN REFINEMENT OVER THE ADMITTED SHARED ATOMICS
    (`brueckenLaufGxGeteilt`).** The run refinement with `Tg` the
    checker's admitted shared atomics: a start-anchored bridged fragment
    run yields a reached GX run in which the weak memory answers exactly
    the admitted shared atomics, and the presented memory agrees with G's
    at every other carrier -- plain carriers and thread-local atomics are
    sequentially consistent along the lowered fragment. The atomicity
    side-condition is discharged by `geteiltVAtomar`, not assumed. -/
theorem brueckenLaufGxGeteilt [DecidableEq D.Fn] (ws : List D.Fn)
    (hO : GutO O) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussSX P S lok (Zielsatz.GeteiltV P ws) f)
    (hlokK : ∀ c, lok c = true → GetrenntK P K c)
    (hex : StartExklusiv init)
    {W' : RufMaschineW D} {arts : List FragArt}
    (h : BrueckenLauf P O passes ord (RufStartW (RufStartG P sp init)) W' arts) :
    RufErreichbarGX P O passes (Zielsatz.GeteiltV P ws) (RufStartG P sp init)
      W'.g :=
  brueckenLaufGx hO hvoll hAbg hWurzel hFuss hlokK
    (fun _ hc => geteiltVAtomar hc) hex h

/-! ## 5. The rely touches no non-admitted carrier. -/

/-- **RELY STABILITY (`havocLaesstPlain`).** No atomic environment of the
    rely changes a carrier outside the admitted set `T`: a plain carrier
    (or a thread-local atomic) read through a lowered fragment load keeps
    the source value under every `HavocA` environment. The accepted
    `HavocA` class unpacked at a non-member. Both premises are used: `hA`
    for the class, `hT` discharging the membership. -/
theorem havocLaesstPlain {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D}
    (hA : HavocA T A) {X : List (D.Tab ⊕ D.Glob)} {σ : World D}
    {c : D.Tab ⊕ D.Glob} (hT : ¬ T c) :
    TraegerGleich (A X σ).speicher σ.speicher c :=
  (hA X σ).2 c fun h => hT h.2

/-! ## 6. The LOCK leg: a forwarding core refuses the LOCK plug. -/

/-- **LOCK/FORWARDING DISJOINTNESS (`lockBeiWeiterleitungVerweigert`).**
    A core that forwards a byte (a pending own entry, the premise the
    forwarded-read bridge `schrittW_aus_lesefragment_weiterleitung` stands
    on) refuses every admitted LOCK XADD step (whose guard needs the empty
    own buffer): the RMW leg and the forwarded-read leg never coincide on
    one core. The forwarding observation splits the buffer
    (`neuestens_jüngste`) into a cons, which the accepted buffer refusal
    closes. Every premise is used: `hFwd` for the split, the registers
    and length for the refused event. -/
theorem lockBeiWeiterleitungVerweigert (m : HwMaschine) (c : Nat)
    (x : Adresse) (w : Byte)
    (hFwd : neuestens (m.puffer c) x = some w)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hok : laengeOk len = true) :
    tsoRmwAdapter.schritt m c (.ok (.xadd64 src base d) len) = none := by
  obtain ⟨pre, post, w', hsplit, _, _⟩ := neuestens_jüngste (m.puffer c) x w hFwd
  cases hpre : pre with
  | nil =>
    have hbuf : m.puffer c = ⟨x, w'⟩ :: post := by
      simp [hsplit, hpre]
    exact tsoRmw_puffer_bleibt_verweigert m c src base d len _ _ hbuf hok
  | cons e rest =>
    have hbuf : m.puffer c = e :: (rest ++ [⟨x, w'⟩] ++ post) := by
      simp [hsplit, hpre]
    exact tsoRmw_puffer_bleibt_verweigert m c src base d len _ _ hbuf hok

/-! ## 7. Joint witnesses. -/

/-- The witness declaration's functions decide equality (they are `Unit`). -/
instance : DecidableEq witD.Fn := inferInstanceAs (DecidableEq Unit)

/-- **JOINT WITNESS for `gxSchrittAusG`.** Every premise holds jointly on
    concrete values: the witness declaration `witD` with one table the
    witness function writes (`ctHw`), a concrete G step that changes the
    source slot `0 → 42` and the mapped target bytes, its GX embedding
    over the admitted shared atomics (here instantiated as
    `GeteiltV ctProg []`), the reached one-step GX run, the inherited
    history over the drain end, a reached one-flush trace with two
    distinct timestamps, a pending foreign byte outside the footprint,
    the stale-view divergence (core 0 canonically reads zero where core 1
    forwards seven -- forwarding visible to the owner only), and the
    reached two-core trace whose flushes observably change canonical
    memory at two addresses. Non-degenerate: a written table, a
    memory-changing source step and target drain, two cores. The GX leg
    itself is one step; the consumed TSO evidence is multi-step. -/
theorem gxSchrittAusG_zeuge :
    ∃ (M0 M' : RufMaschineG witD),
      RufSchrittG ctProg witO 0 M0 0 M' ∧
      RufSchrittGX ctProg witO 0 (Zielsatz.GeteiltV ctProg []) M0 0 M' ∧
      RufErreichbarGX ctProg witO 0 (Zielsatz.GeteiltV ctProg []) M0 M' ∧
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
  have hGX := gxSchrittAusG (Tg := Zielsatz.GeteiltV ctProg []) hSW.schritt
  have hR : RufErreichbarGX ctProg witO 0 (Zielsatz.GeteiltV ctProg [])
      _ M'' :=
    .schritt _ _ _ .start hGX
  exact ⟨_, _, hSW.schritt, hGX, hR, ctHw, hBefore, ⟨σ', hAfter⟩,
    hBytes, hErbt, hInv, hErr, hUhr, hBuf, hFresh, hSt0, hSt1,
    spurW_erreichbar, spurW_speicher.1, spurW_speicher.2⟩

/--Locked length 9 decodes: the witness LOCK event is well-formed. -/
theorem gxLockLaenge : laengeOk 9 = true := by decide

/-- **JOINT WITNESS for `lockBeiWeiterleitungVerweigert`.** Every premise
    holds jointly on concrete values: the coherent witness start carrying
    the `ctS4` buffers (well-formed), core 1 forwarding the foreign seven
    at `ctF` outside the slot footprint while core 0 canonically reads
    zero there -- the buffered store visible via forwarding to the owner
    only -- and the LOCK XADD plug refusing that core. Non-degenerate:
    two cores with divergent observations at one address, a pending
    foreign byte, a refused LOCK step. -/
theorem lockBeiWeiterleitungVerweigert_zeuge :
    ∃ (m : HwMaschine),
      (∃ x : Adresse, ∃ w : Byte, neuestens (m.puffer 1) x = some w) ∧
      HwWf m ∧
      tsoRmwAdapter.schritt m 1 (.ok (.xadd64 .rax .rbp 0) 9) = none ∧
      loadByte (tsoAnsicht m) 1 ctF = some ctFv ∧
      loadByte (tsoAnsicht m) 0 ctF = some (BitVec.ofNat 8 0) ∧
      m.puffer 1 = [⟨ctF, ctFv⟩] ∧ ctF ∉ Fuss witA := by
  have hBuf : (setTso hwWitStart ctS4).puffer 1 = [⟨ctF, ctFv⟩] := ctBuf1_4
  have hFwd : neuestens ((setTso hwWitStart ctS4).puffer 1) ctF = some ctFv := by
    rw [hBuf]
    rfl
  refine ⟨setTso hwWitStart ctS4, ⟨ctF, ctFv, hFwd⟩,
    setTso_wf _ _ hwWitStart_wf,
    lockBeiWeiterleitungVerweigert _ _ ctF ctFv hFwd _ _ _ _ gxLockLaenge,
    ?_, ?_, hBuf, ctFfresh⟩
  · rw [setTso_ansicht]
    exact ct_stale1
  · rw [setTso_ansicht]
    exact ct_stale0

/- CUTS:
    - Proved here:
      (1) GX embedding (`gxSchrittAusG`, `gxLaufAusG`): every G step/run
      is a GX step/run, for any shared-atomic set (accepted `gx_aus_g`,
      `gx_aus_g_lauf` named for the fragment consumer).
      (2) Step refinement (`brueckenSchrittGx`): a bridged fragment step
      from a reached W refines to a GX step with outside-`Tg` memory
      agreement, under the explicit DRF/checker premises of
      `schwach_ist_gX` (never assumed).
      (3) Run refinement (`brueckenLaufGx`, `brueckenLaufGxGeteilt`): a
      start-anchored bridged run yields a reached GX run, in general and
      over the admitted shared atomics (`geteiltVAtomar` discharges the
      atomicity side-condition).
      (4) Rely stability (`havocLaesstPlain`): no atomic environment
      touches a non-admitted carrier.
      (5) LOCK-leg disjointness (`lockBeiWeiterleitungVerweigert`,
      `gxLockLaenge`): a forwarding core refuses the LOCK plug.
      (6) Joint non-degenerate witnesses (`gxSchrittAusG_zeuge`,
      `lockBeiWeiterleitungVerweigert_zeuge`): written table,
      memory-changing source step (`0 → 42`) and target drain, two cores
      with observably changed memory, forwarding visible to the owner
      only, a refused LOCK step.
    - NOT proved here, left OPEN (the exact remaining obligation):
      (a) discharging the DRF/checker premises (`GutO`, `AbgK`,
      `FussSX` over `GeteiltV`, `StartExklusiv`) for a lowered program,
      i.e. the checker side of the bridge;
      (b) a start-anchored bridged run: the fragment head must first be
      REACHED from `RufStartG` by entry/call prefix execution, which the
      three bridged fragment kinds do not cover -- hence no joint
      `_zeuge` for `brueckenLaufGx`/`brueckenLaufGxGeteilt` yet (a
      finding, not a weakening);
      (c) constructing a `SchrittW` with the `rmw` field from an
      admitted LOCK step (the accepted single-RMW shape
      `tsoRmw_xadd_einzel_rmw`, the no-split/no-loss chain
      `tsoRmw_kein_split`/`tsoRmw_kette_ohne_verlust` and the lowering
      certificate linking the `exchange` head to LOCK bytes are all
      present, but the assembly is not done here);
      (d) `valX86_sound`; scheduling, fairness, progress, timing;
      interrupts, devices, MMIO, DMA.
    - No `HwAdapter` is defined here by design: the consumer is machine
      GX, not `HwMaschine` (as in lane 1187 for W); the accepted
      `tsoRmwAdapter` is reused for the LOCK leg, never redefined.
    - No hardware correspondence beyond self-consistency is claimed;
      silicon assumptions are those of the reused accepted modules.
-/

#print axioms gxSchrittAusG
#print axioms gxLaufAusG
#print axioms brueckenSchrittGx
#print axioms brueckenLaufGx
#print axioms geteiltVAtomar
#print axioms brueckenLaufGxGeteilt
#print axioms havocLaesstPlain
#print axioms lockBeiWeiterleitungVerweigert
#print axioms gxLockLaenge
#print axioms gxSchrittAusG_zeuge
#print axioms lockBeiWeiterleitungVerweigert_zeuge

end Gabbro.Grammatik.X86
