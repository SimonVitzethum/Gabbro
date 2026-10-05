/-
  File:      Grammatik/X86/HwKapsteinTsoRest.lean
  Subject:   Capstone rest: TSO projection for the device, FP, vector,
             fault, gate, interrupt and image tags.

  Lane 1329: classify the ten remaining union tags of `HwVollSchritt`
  (`HwKapstein.lean`) against the TSO store-buffer projection `kapTso`
  (`HwKapsteinTso.lean`, lane 1295):
  - uc, port: device paths are NOT store-buffered in the stated model.
    Both are projection-unchanged for the TSO buffers, with the device
    effect named (posted UC write on the extended machine; accepted
    bus latch for ports, gated on the drained buffer).
  - fp, vec: register, load-observation and refusal legs are
    projection-unchanged; byte stores are single `issueByte` events and
    drains single `flushKern` events; a 16-byte vector row is sixteen
    issues (no whole-vector atomicity).
  - fehler, tor, bild, instanzen: projection-unchanged (a faulting or
    refused step has no buffer effect; a fetch/register step changes
    core data only).
  - nested, int: FINDING. Delivery is explicitly NOT a buffered push
    (S3 in `HwNestedInterrupts.lean`, `asyncMasch_puffer_still`): the
    frame lands in canonical memory through direct `write64` pushes
    (`schiebeRahmen`) with every store buffer untouched. The exhibited
    NMI run provably changes memory (`witNmi_aendert_ss`) while no
    buffer grows (`witNmi_puffer_0/1`). A memory write by a path other
    than the TSO events is therefore classified as a FINDING of high
    priority, never as stack-push events: the per-access bridge needs
    a drained-own-buffer guard for delivery.

  Every accepted definition is reused unchanged, never redefined.
  Vendor neutral (rule 17): no silicon value is pinned; Intel SDM
  provenance is cited from the family files, never restated.
-/
import Grammatik.X86.Hw.Kapstein.HwKapsteinTso
import Grammatik.X86.Hw.Kapstein.HwKapsteinSteps

namespace Gabbro.Grammatik.X86

/-! ## 1. Device paths: UC and ports are not store-buffered.

  The stated model retires UC stores past the WB buffer (posted,
  never buffered: `ucStore_bypass`) and re-embeds port steps as core
  data only. Both plugs therefore leave the TSO projection unchanged;
  the device effect is named alongside (posted UC write on the
  extended machine; accepted bus latch for ports). -/

/-- UC plug steps leave the TSO projection unchanged: an admitted
    store steps to the same machine (bypass), a load never admits. -/
theorem rest_uc_still (m : HwMaschine) (c : Nat)
    (e : HwDev1133.UcZugriff1133) (m' : HwMaschine)
    (h : HwDev1133.adapterUc1133.schritt m c e = some m') :
    kapTso m' = kapTso m := by
  cases e with
  | speichere b a v profil =>
    have h' : HwDev1133.ucAdapterSchritt m c
        (HwDev1133.UcZugriff1133.speichere b a v profil) = some m' := h
    unfold HwDev1133.ucAdapterSchritt at h'
    simp only at h'
    split at h'
    · cases h'
      rfl
    · cases h'
  | lade b dst a profil =>
    have h' : HwDev1133.ucAdapterSchritt m c
        (HwDev1133.UcZugriff1133.lade b dst a profil) = some m' := h
    unfold HwDev1133.ucAdapterSchritt at h'
    simp only at h'
    cases h'

/-- A classified UC union step reaches through the projection
    silently: device paths are never buffer events. -/
theorem rest_union_uc (m m' : HwMaschine) (c : Nat)
    (e : HwDev1133.UcZugriff1133)
    (h : HwVollSchritt m m' (KapEreignis.uc c e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | uc _ _ heq =>
    have hs := rest_uc_still _ _ _ _ heq
    rw [hs]
    exact .start

/-- DEVICE EFFECT (UC): an admitted plug store is exactly a reached
    extended UC-store step whose coherent machine is unchanged: the
    write posts to the bus queue and log, never to a store buffer. -/
theorem rest_uc_geraet (d : HwDev1133.HwDevMaschine) (c : Nat)
    (b : Breite) (a : Adresse) (v : Wort)
    (hz : breiteZugelassen d.masch.hw (d.masch.bereit c) b = true)
    (hu : istUc d.profil a b.bytes = true)
    (hf : imFenster a b.bytes = true) :
    ∃ d' : HwDev1133.HwDevMaschine,
      HwDev1133.HwDevSchritt d d' (.ucSpeichern b a v) ∧
        d'.masch = d.masch :=
  (HwDev1133.adapterUc1133_stimmt_ueberein d c b a v hz hu hf).2

/-- Port plug steps leave the TSO projection unchanged: the plug
    re-embeds core data only (`setKernDaten`), never memory. -/
theorem rest_port_still (m : HwMaschine) (c : Nat)
    (e : HwDev1133.PortZugriff1133) (m' : HwMaschine)
    (h : HwDev1133.adapterPort1133.schritt m c e = some m') :
    kapTso m' = kapTso m := by
  have hdef : HwDev1133.portAdapterSchritt m c e = some m' := h
  unfold HwDev1133.portAdapterSchritt at hdef
  cases hk : HwDev1133.portAdapterKern m c e with
  | none =>
    simp [hk] at hdef
  | some k =>
    simp [hk] at hdef
    cases hdef
    exact kapTso_setKernDaten m c k

/-- A classified port union step reaches through the projection
    silently: ports are never buffer events. -/
theorem rest_union_port (m m' : HwMaschine) (c : Nat)
    (e : HwDev1133.PortZugriff1133)
    (h : HwVollSchritt m m' (KapEreignis.port c e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | port _ _ heq =>
    have hs := rest_port_still _ _ _ _ heq
    rw [hs]
    exact .start

/-- DEVICE EFFECT (port OUT): a fetched OUT under the accepted gates
    justifies the reached generic bus step with the latch answer. -/
theorem rest_port_bus (m : HwMaschine) (c : Nat)
    (dec : IoDec) (g : GeraetZustand) (spur : List IoEreignis)
    (r : Bus704.IoBerechtigung) (k : Bus704.TssKarte)
    (d : IoDec) (rest : List Byte) (b : IoBreite) (q : PortQuelle)
    (hf : fetchIo (projZustand m c) = some (d, rest))
    (heq : d = dec)
    (hop : dec.op = ⟨.aus, b, q⟩)
    (hlen : laengeOk dec.laenge = true)
    (hperm : Bus704.archZugelassen r k
      (portVon dec.op (projZustand m c).register) b = true)
    (hord : zaunBereit (tsoAnsicht m) c = true) :
    Bus704.BusSchritt GeraetZustand Bus704.latchErlaubt r k
      ⟨projZustand m c, g, spur⟩
      ⟨Bus704.ausKern (projZustand m c) dec,
        (geraetAntwort g .aus b
          (ausGabe b ((projZustand m c).register .rax))).1,
        spur ++ [⟨.aus, b,
          portVon dec.op (projZustand m c).register,
          ausGabe b ((projZustand m c).register .rax)⟩]⟩ :=
  (HwDev1133.portAdapter_aus_fetch m c dec g spur r k d rest b q
    hf heq hop hlen hperm hord).2

/-! ## 2. Scalar FP: register legs are silent, memory legs are bytes.

  The three register legs (`s32reg`, `f64reg`, `mxcsrLd`) re-embed
  core data only; the load leg observes with forwarding and the
  refusal leg steps to itself (both silent); the store leg is exactly
  one `issueByte` event and the drain leg exactly one `flushKern`
  event, each with its footprint named. -/

/-- Every FP family step classifies on the TSO projection: register
    and fault steps are silent, loads observe with forwarding, stores
    are single `issueByte` events, drains single `flushKern` events. -/
theorem rest_fp_tso (m m' : HwMaschine) (e : FpCtrlEreignis)
    (h : FpCtrlSchritt m m' e) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | s32reg c d t' hstep hmem =>
    rw [kapTso_setKernVonFp]
    exact .start
  | f64reg c d t' hstep hmem =>
    rw [kapTso_setKernVonFp]
    exact .start
  | mxcsrLd c d t' hstep hmem =>
    rw [kapTso_setKernVonFp]
    exact .start
  | lade c a v h =>
    exact .start
  | gibAus c a v s' h =>
    have h' : issueByte (kapTso m) c a v = some s' := h
    rw [kapTso_setTso]
    exact kapTso_schritt_erreichbar _ _ (.issue _ s' c a v h')
  | spüle c e s' h hkopf =>
    have h' : flushKern (kapTso m) c = some s' := h
    rw [kapTso_setTso]
    exact kapTso_schritt_erreichbar _ _ (.flush _ s' c h')
  | fehler c h =>
    exact .start

/-- A classified FP union step reaches through the projection. -/
theorem rest_union_fp (m m' : HwMaschine) (e : FpCtrlEreignis)
    (h : HwVollSchritt m m' (KapEreignis.fp e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | fp _ hstep => exact rest_fp_tso _ _ _ hstep

/-! ## 3. Faults and feature gates: no buffer effect.

  A fault step never moves the state (`hwFehlerSchritt_fehler_still`);
  an embedded old step reuses the base classification. An admitted
  gate step re-embeds core data only; the refused gate leg steps to
  itself. All four shapes are projection-unchanged or base-reaching. -/

/-- Every fault-family step reaches through the projection: embedded
    old steps reuse the base leg, fault outcomes are silent
    self-loops with the ordered fault named. -/
theorem rest_fehler_tso (m m' : HwMaschine) (e : HwFehlerEreignis)
    (h : HwFehlerSchritt m m' e) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | einbettet e hstep => exact kap_basis_reichbar _ _ _ hstep
  | fehler c z pg st ill teiltFalle f hwahl => exact .start

/-- A classified fault union step reaches through the projection. -/
theorem rest_union_fehler (m m' : HwMaschine) (e : HwFehlerEreignis)
    (h : HwVollSchritt m m' (KapEreignis.fehler e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | fehler _ hstep => exact rest_fehler_tso _ _ _ hstep

/-- Gate steps leave the TSO projection unchanged: the admitted leg
    re-embeds core data only, the refused leg steps to itself. -/
theorem rest_tor_still (leaf1 : CpuOut) (xcrLo : BitVec 32)
    (m m' : HwMaschine) (e : HwTorEreignis)
    (h : HwTorSchritt leaf1 xcrLo m m' e) :
    kapTso m' = kapTso m := by
  cases h with
  | ok c i t' hoff hstep hmem => exact kapTso_setKernVonFp _ _ _
  | ud c i hzu => rfl

/-- A classified gate union step reaches through the projection
    silently. -/
theorem rest_union_tor (m m' : HwMaschine) (leaf1 : CpuOut)
    (xcrLo : BitVec 32) (e : HwTorEreignis)
    (h : HwVollSchritt m m' (KapEreignis.tor leaf1 xcrLo e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | tor _ _ _ hstep =>
    have hs := rest_tor_still _ _ _ _ _ hstep
    rw [hs]
    exact .start

/-! ## 4. Packed vectors: loads observe, stores issue sixteen bytes.

  Register rows and both load rows re-embed core data only (loads
  observe through `vecLaden` but change no buffer); both store rows
  fold sixteen `issueByte` events through `vecSpeichern`
  (`vecEintraege_laenge`): no whole-vector atomicity. The refusal leg
  steps to itself. -/

/-- A buffered vector store reaches through the projection: sixteen
    byte issues, never a direct memory write. -/
theorem rest_vec_speicher_erreichbar (s : TSOZustand) (c : Nat)
    (a : Adresse) (v : Vektor) (s' : TSOZustand)
    (h : vecSpeichern s c a v = some s') :
    TSOErreichbar s s' := by
  have h' : issueListe s c (vecEintraege a v) = some s' := h
  exact kapTso_issueListe_erreichbar s c (vecEintraege a v) s' h'

/-- Every vector-family step reaches through the projection:
    register, load and refusal legs are silent, stores fold sixteen
    single-byte issues with the footprint named. -/
theorem rest_vec_tso (m m' : HwMaschine) (e : HwVecEreignis)
    (h : HwVecSchritt m m' e) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | alt hstep => exact kap_basis_reichbar _ _ _ hstep
  | reg hreg hok hgate hstep hmem =>
    rw [kapTso_setKernVonFp]
    exact .start
  | ladeA hop hok hgate hgp hread =>
    rw [kapTso_setKernVonFp]
    exact .start
  | ladeU hop hok hgate hread =>
    rw [kapTso_setKernVonFp]
    exact .start
  | speichereA hop hok hgate hgp hwr =>
    rw [kapTso_setTso]
    exact rest_vec_speicher_erreichbar _ _ _ _ _ hwr
  | speichereU hop hok hgate hwr =>
    rw [kapTso_setTso]
    exact rest_vec_speicher_erreichbar _ _ _ _ _ hwr
  | fehler h =>
    exact .start

/-- A classified vector union step reaches through the projection. -/
theorem rest_union_vec (m m' : HwMaschine) (e : HwVecEreignis)
    (h : HwVollSchritt m m' (KapEreignis.vec e)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | vec _ hstep => exact rest_vec_tso _ _ _ hstep

/-! ## 5. Loaded image and loader instances: fetch changes nothing.

  Both plugs ARE the accepted register-path plug (`adapterBild`
  and `adapterInstanzen` are `adapterInteger666` by definition): an
  admitted step re-embeds core data only, a fetch refusal or halt
  admits nothing at all. -/

/-- Register-path plug steps leave the TSO projection unchanged:
    only core data moves, never memory or buffers. -/
theorem rest_integer666_still (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : adapterInteger666.schritt m c i = some m') :
    kapTso m' = kapTso m := by
  unfold adapterInteger666 at h
  simp only at h
  cases hs : stepExt i (projFp m c) (m.bereit c) with
  | weiter t' =>
    rw [hs] at h
    simp only at h
    cases h
    exact kapTso_setKernVonFp _ _ _
  | halt =>
    rw [hs] at h
    simp only at h
    cases h
  | verweigert =>
    rw [hs] at h
    simp only at h
    cases h

/-- A classified loaded-image union step reaches through the
    projection silently. -/
theorem rest_union_bild (m m' : HwMaschine) (c : Nat) (i : ExtInstr)
    (h : HwVollSchritt m m' (KapEreignis.bild c i)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | bild _ _ heq =>
    have hs := rest_integer666_still _ _ _ _ heq
    rw [hs]
    exact .start

/-- A classified loader-instance union step reaches through the
    projection silently. -/
theorem rest_union_instanzen (m m' : HwMaschine) (c : Nat)
    (i : ExtInstr)
    (h : HwVollSchritt m m' (KapEreignis.instanzen c i)) :
    TSOErreichbar (kapTso m) (kapTso m') := by
  cases h with
  | instanzen _ _ heq =>
    have hs := rest_integer666_still _ _ _ _ heq
    rw [hs]
    exact .start

/-! ## 6. Interrupts: buffer-silent delivery is a FINDING, not TSO.

  Delivery is explicitly NOT a serialising drain of the per-core
  store buffer (S3 in `HwNestedInterrupts.lean`,
  `asyncMasch_puffer_still`): the frame lands in canonical memory
  through direct `write64` pushes (`schiebeRahmen`) with every store
  buffer untouched. A memory write by a path other than the TSO
  events is therefore a FINDING of high priority: no `TSOErreichbar`
  leg is claimed for the `nested`/`int` tags, and the per-access
  bridge needs a drained-own-buffer guard for delivery. What IS
  proved: buffer silence for every successful single and nested
  delivery, the exhibited NMI run changing memory with still
  buffers, and the exhibited delivery refusals. -/

/-- Buffer silence of the push stage: a successful frame push never
    touches any store buffer. -/
theorem rest_asyncFertig_puffer (m : HwMaschine) (c : Nat)
    (st : Steuerstand) (g : IdtTor) (q : LieferAnfrage) (rsp : Wort)
    (gew : Bool) (r : HwMaschine × Bool × Bool)
    (h : asyncFertig m c st g q rsp gew = some r) (d : Nat) :
    r.1.puffer d = m.puffer d := by
  unfold asyncFertig at h
  cases hk : istKanonisch rsp with
  | false =>
    simp [hk] at h
  | true =>
    simp [hk] at h
    cases hpush : schiebeRahmen m.mem rsp (rahmenWorte q) with
    | none =>
      simp [hpush] at h
    | some m2 =>
      simp [hpush] at h
      cases h
      exact asyncMasch_puffer_still _ _ _ _ _ _ _

/-- Buffer silence of single delivery: every successful `asyncSchritt`
    leaves every store buffer byte-identical. -/
theorem rest_async_puffer_still (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (st : Steuerstand)
    (r : HwMaschine × Bool × Bool)
    (h : asyncSchritt m c ev st = some r) (d : Nat) :
    r.1.puffer d = m.puffer d := by
  unfold asyncSchritt at h
  cases hv : asyncVektorOk ev with
  | false =>
    simp [hv] at h
  | true =>
    simp [hv] at h
    cases hb : asyncBereit ev with
    | false =>
      simp [hb] at h
    | true =>
      simp [hb] at h
      cases hl : torImLimit st.idtLimit ev.vektor with
      | false =>
        simp [hl] at h
      | true =>
        simp [hl] at h
        cases ht : liesTorBytes m.mem
            (torAdresse st.idtBasis ev.vektor) with
        | none =>
          simp [ht] at h
        | some t =>
          simp [ht] at h
          cases hp : pruefeTor ev.vektor st.idtLimit t .extern st.cpl
              ev.codeOk with
          | fehler _ =>
            simp [hp] at h
          | bereit g =>
            simp [hp] at h
            cases hs : waehleStapel m.mem st g.ist ev.neuDpl ev.wechsel
                ((m.kerne c).register Register.rsp) with
            | stapelFehler _ =>
              simp [hs] at h
            | behalten rsp =>
              simp [hs] at h
              exact rest_asyncFertig_puffer _ _ _ _ _ _ _ _ h d
            | wechseln rsp =>
              simp [hs] at h
              exact rest_asyncFertig_puffer _ _ _ _ _ _ _ _ h d

/-- Adapter-level buffer silence of single delivery. -/
theorem rest_int_puffer (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis) (m' : HwMaschine)
    (h : adapterInterrupt1125.schritt m c ev = some m') (d : Nat) :
    m'.puffer d = m.puffer d := by
  unfold adapterInterrupt1125 at h
  cases hr : asyncSchritt m c ev ev.steuer with
  | none =>
    simp [hr] at h
  | some r =>
    simp [hr] at h
    cases h
    exact rest_async_puffer_still m c ev ev.steuer _ hr d

/-- Buffer silence of nested delivery: both legs are `asyncSchritt`
    legs, each buffer-silent. -/
theorem rest_nest_puffer_still (m : HwMaschine) (c : Nat)
    (ev1 ev2 : AsyncEreignis) (st1 : Steuerstand)
    (m2 : HwMaschine) (a b cc : Bool)
    (h : verschachteltSchritt m c ev1 ev2 st1 = some (m2, a, b, cc))
    (d : Nat) :
    m2.puffer d = m.puffer d := by
  unfold verschachteltSchritt at h
  cases h1 : asyncSchritt m c ev1 st1 with
  | none =>
    simp [h1] at h
  | some r1 =>
    rw [h1] at h
    simp only at h
    cases hd : decide (ev2.steuer = { st1 with ifBit := r1.2.1 }) with
    | false =>
      simp [hd] at h
    | true =>
      simp [hd] at h
      cases h2 : asyncSchritt r1.1 c ev2
          { st1 with ifBit := r1.2.1 } with
      | none =>
        simp [h2] at h
      | some r2 =>
        rw [h2] at h
        simp only at h
        cases h
        have hleg1 : r1.1.puffer d = m.puffer d :=
          rest_async_puffer_still m c ev1 st1 r1 h1 d
        have hleg2 : r2.1.puffer d = r1.1.puffer d :=
          rest_async_puffer_still r1.1 c ev2
            { st1 with ifBit := r1.2.1 } r2 h2 d
        exact hleg2.trans hleg1

/-- Adapter-level buffer silence of nested delivery. -/
theorem rest_nested_puffer (m : HwMaschine) (c : Nat)
    (ev : AsyncEreignis × AsyncEreignis) (m' : HwMaschine)
    (h : adapterVerschachtelt.schritt m c ev = some m') (d : Nat) :
    m'.puffer d = m.puffer d := by
  unfold adapterVerschachtelt at h
  simp only at h
  cases hn : verschachteltSchritt m c ev.1 ev.2 ev.1.steuer with
  | none =>
    rw [hn] at h
    simp only at h
    cases h
  | some r =>
    obtain ⟨m2, a, b, cc⟩ := r
    rw [hn] at h
    simp only at h
    have hm' : m' = m2 := (Option.some_inj.mp h).symm
    rw [hm']
    exact rest_nest_puffer_still m c ev.1 ev.2 ev.1.steuer
      m2 a b cc hn d

/-- FINDING, sharp: the exhibited NMI delivery changes canonical
    memory through the direct-push path while every store buffer
    stays still. This is a memory write by a path other than the TSO
    events, so no `TSOErreichbar` leg is claimed for it. -/
theorem rest_int_befund (m' : HwMaschine)
    (hplug : adapterInterrupt1125.schritt intWitStart 0 witNmi
      = some m') :
    m'.mem ≠ intWitStart.mem ∧
      ∀ d : Nat, m'.puffer d = intWitStart.puffer d := by
  obtain ⟨m0, ifNeu, gew, hplug0, hschritt⟩ := kapPlug_int
  have hm' : m' = m0 := (Option.some_inj.mp (hplug0.symm.trans hplug)).symm
  rw [hm']
  refine ⟨?_, fun d => rest_int_puffer _ _ _ _ hplug0 d⟩
  have hmem : asyncMemOut witSchritt = m0.mem := by
    have hws : witSchritt = some (m0, ifNeu, gew) := hschritt
    rw [hws]
    rfl
  intro hcon
  have hbyte : (asyncMemOut witSchritt).bytes (BitVec.ofNat 64 16376) =
      witMem.bytes (BitVec.ofNat 64 16376) := by
    rw [hmem, hcon]
    rfl
  exact witNmi_aendert_ss hbyte.symm

/-- Exhibited delivery refusals stay refused: masked, over-limit and
    dark-stack probes admit no delivery step. -/
theorem rest_int_verweigert :
    asyncSchritt intWitStart 1 witMaskiert witSteuerNmi = none ∧
      asyncSchritt intWitStart 1 witLimit witLimitSteuer = none ∧
        asyncSchritt intWitDunkel 0 witNmi witSteuerNmi = none :=
  ⟨witNmi_maskiert_verweigert, witNmi_limit_verweigert,
    witNmi_dunkel_verweigert⟩

/-! ## 7. Joint summary and witness.

  Eight tags reach through the TSO projection (§§1-5); the two
  interrupt tags are the proved FINDING of §6 (buffer-silence plus
  the sharp memory-change exhibit, never a `TSOErreichbar` leg). -/

/-- Joint summary: all eight reaching tags reach through the TSO
    projection. Each premise is used by its own leg. -/
theorem rest_acht_tso :
    (∀ (m m' : HwMaschine) (c : Nat) (e : HwDev1133.UcZugriff1133),
      HwVollSchritt m m' (.uc c e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (e : HwDev1133.PortZugriff1133),
      HwVollSchritt m m' (.port c e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (e : FpCtrlEreignis),
      HwVollSchritt m m' (.fp e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (e : HwFehlerEreignis),
      HwVollSchritt m m' (.fehler e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (leaf1 : CpuOut) (xcrLo : BitVec 32)
      (e : HwTorEreignis),
      HwVollSchritt m m' (.tor leaf1 xcrLo e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (e : HwVecEreignis),
      HwVollSchritt m m' (.vec e) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (i : ExtInstr),
      HwVollSchritt m m' (.bild c i) →
        TSOErreichbar (kapTso m) (kapTso m'))
    ∧ (∀ (m m' : HwMaschine) (c : Nat) (i : ExtInstr),
      HwVollSchritt m m' (.instanzen c i) →
        TSOErreichbar (kapTso m) (kapTso m')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m m' c e h
    exact rest_union_uc m m' c e h
  · intro m m' c e h
    exact rest_union_port m m' c e h
  · intro m m' e h
    exact rest_union_fp m m' e h
  · intro m m' e h
    exact rest_union_fehler m m' e h
  · intro m m' leaf1 xcrLo e h
    exact rest_union_tor m m' leaf1 xcrLo e h
  · intro m m' e h
    exact rest_union_vec m m' e h
  · intro m m' c i h
    exact rest_union_bild m m' c i h
  · intro m m' c i h
    exact rest_union_instanzen m m' c i h

/-- Joint witness: one exhibited union step per rest tag. The eight
    reaching tags reach through the projection; the nested run keeps
    every buffer still; the NMI run changes memory with still
    buffers (the FINDING); owner-only forwarding, foreign stale
    reads and drain-into-memory hold on the same TSO model; the
    masked, over-limit and dark-stack deliveries refuse. -/
theorem rest_zeuge :
    (∃ m1, HwVollSchritt hwWitStart m1
      (KapEreignis.uc 0
        (.speichere .b64 HwDev1133.witDev1133 (BitVec.ofNat 64 7)
          HwDev1133.witProfil1133)) ∧
      TSOErreichbar (kapTso hwWitStart) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt kapPortStart m1
      (KapEreignis.port 0 kapPortEv) ∧
      TSOErreichbar (kapTso kapPortStart) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt stapelWitM0 m1
      (KapEreignis.fp
        (.schreibAusgabe 0 stapelWitSlotAddr (BitVec.ofNat 8 7))) ∧
      TSOErreichbar (kapTso stapelWitM0) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt hwWitStart m1
      (KapEreignis.fehler (HwFehlerEreignis.fehler 1 ⟨.abruf, .pf⟩)) ∧
      TSOErreichbar (kapTso hwWitStart) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt hwWitStart m1
      (KapEreignis.tor zeugeOut1 (BitVec.ofNat 32 0x6)
        (.ausf 0 (.vec hwTorWitV))) ∧
      TSOErreichbar (kapTso hwWitStart) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt hvecWitStart m1
      (KapEreignis.vec
        (.vecReg 0 basisCpu basisKontrolle hvecWitD1)) ∧
      TSOErreichbar (kapTso hvecWitStart) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt instStart_muldiv m1
      (KapEreignis.bild 0 (.muldiv ⟨.mulRax .rcx, 3⟩)) ∧
      TSOErreichbar (kapTso instStart_muldiv) (kapTso m1))
    ∧ (∃ m1, HwVollSchritt instStart_vec m1
      (KapEreignis.instanzen 0
        (.vec ⟨.pxorRR .xmm0 .xmm1, 5⟩)) ∧
      TSOErreichbar (kapTso instStart_vec) (kapTso m1))
    ∧ (∃ m2, HwVollSchritt nestStart m2
      (KapEreignis.nested 0 evMask32 evMask33) ∧
      ∀ d : Nat, m2.puffer d = nestStart.puffer d)
    ∧ (∃ m', HwVollSchritt intWitStart m'
      (KapEreignis.int 0 witNmi) ∧
      m'.mem ≠ intWitStart.mem ∧
      ∀ d : Nat, m'.puffer d = intWitStart.puffer d)
    ∧ hwWitLoadEigen = some (some (BitVec.ofNat 8 42))
    ∧ hwWitLoadFremd = some (some (BitVec.ofNat 8 0))
    ∧ hwWitNachFlush = some (some (BitVec.ofNat 8 42))
    ∧ asyncSchritt intWitStart 1 witMaskiert witSteuerNmi = none ∧
      asyncSchritt intWitStart 1 witLimit witLimitSteuer = none ∧
        asyncSchritt intWitDunkel 0 witNmi witSteuerNmi = none := by
  obtain ⟨mPort, hsPort⟩ := kapStep_port
  obtain ⟨mFp, hsFp⟩ := kap_step_fp
  obtain ⟨mBild, hsBild⟩ := kapStep_bild
  obtain ⟨mInst, hsInst⟩ := kapStep_instanzen
  obtain ⟨mNest, ifNeu2, gew1, gew2, hplugNest, _⟩ := kapPlug_nested
  obtain ⟨mInt, ifNeu, gew, hplugInt, _⟩ := kapPlug_int
  have hNestUnion : HwVollSchritt nestStart mNest
      (KapEreignis.nested 0 evMask32 evMask33) :=
    (kap_nested_embedded _ _ _ _ _).mp hplugNest
  have hIntUnion : HwVollSchritt intWitStart mInt
      (KapEreignis.int 0 witNmi) :=
    (kap_int_embedded _ _ _ _).mp hplugInt
  have hIntBefund := rest_int_befund _ hplugInt
  have hNestBuf : ∀ d : Nat, mNest.puffer d = nestStart.puffer d :=
    fun d => rest_nested_puffer _ _ _ _ hplugNest d
  refine ⟨⟨_, kap_step_uc, rest_union_uc _ _ _ _ kap_step_uc⟩,
    ⟨mPort, hsPort, rest_union_port _ _ _ _ hsPort⟩,
    ⟨mFp, hsFp, rest_union_fp _ _ _ hsFp⟩,
    ⟨_, kap_step_fehler, rest_union_fehler _ _ _ kap_step_fehler⟩,
    ⟨_, kap_step_tor, rest_union_tor _ _ _ _ _ kap_step_tor⟩,
    ⟨_, kap_step_vec, rest_union_vec _ _ _ kap_step_vec⟩,
    ⟨mBild, hsBild, rest_union_bild _ _ _ _ hsBild⟩,
    ⟨mInst, hsInst, rest_union_instanzen _ _ _ _ hsInst⟩,
    ⟨mNest, hNestUnion, hNestBuf⟩,
    ⟨mInt, hIntUnion, hIntBefund.1, hIntBefund.2⟩,
    hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher, rest_int_verweigert⟩

/- CUTS:
    Proved here, over the reused accepted vocabulary only (every
    definition lifted, never redefined):
    - UC projection `rest_uc_still`/`rest_union_uc`: admitted plug
      stores step to the same machine (bypass), loads never admit;
      device effect `rest_uc_geraet` (posted write plus log on the
      extended machine, coherent machine unchanged);
    - port projection `rest_port_still`/`rest_union_port`: the plug
      re-embeds core data only; bus effect `rest_port_bus` (reached
      generic bus step with the accepted latch answer); the drained-
      buffer gate is cited, not re-proved
      (`portAdapter_vollerPuffer_verweigert`);
    - FP classification `rest_fp_tso`/`rest_union_fp`: register legs
      silent, loads observe with forwarding, stores single
      `issueByte`, drains single `flushKern`, refusals silent;
    - fault classification `rest_fehler_tso`/`rest_union_fehler`:
      embedded old steps reuse the base leg, fault outcomes are
      silent self-loops;
    - gate classification `rest_tor_still`/`rest_union_tor`:
      admitted legs re-embed core data only, refused legs self-loop;
    - vector classification `rest_vec_speicher_erreichbar`,
      `rest_vec_tso`/`rest_union_vec`: register/load/refusal legs
      silent, stores fold sixteen `issueByte` events
      (`vecEintraege_laenge`), no whole-vector atomicity;
    - image/instance classification `rest_integer666_still`,
      `rest_union_bild`, `rest_union_instanzen`: the register-path
      plug moves core data only;
    - interrupt buffer silence `rest_asyncFertig_puffer`,
      `rest_async_puffer_still`, `rest_int_puffer`,
      `rest_nest_puffer_still`, `rest_nested_puffer`: every
      successful single and nested delivery leaves every store
      buffer byte-identical;
    - sharp FINDING `rest_int_befund`: the exhibited NMI delivery
      changes canonical memory through the direct-push path with
      still buffers -- a memory write by a path other than the TSO
      events, so no `TSOErreichbar` leg is claimed for the
      `nested`/`int` tags;
    - exhibited refusals `rest_int_verweigert` (masked, over-limit,
      dark-stack);
    - joint summary `rest_acht_tso` and joint witness `rest_zeuge`:
      one exhibited union step per rest tag, reachability for the
      eight reaching tags, buffer silence plus memory change for
      delivery, owner-only forwarding with foreign staleness and
      drain-into-memory on the same TSO model, and the delivery
      refusals.
    NOT proved here, and not claimed (FINDINGs for follow-ups):
    - the `nested`/`int` tags have no `TSOErreichbar` leg: delivery
      installs direct-pushed memory with untouched buffers, so the
      per-access target-to-W/GX bridge needs a drained-own-buffer
      guard for delivery (or delivery treated as a serialising
      context switch); the task's "stack-push events" premise is
      declined with reason (S3, `asyncMasch_puffer_still`,
      `schiebeRahmen`/`write64` path, `witNmi_aendert_ss`);
    - the remaining six union tags (lockRmw, isa, addr, muldiv,
      lockFetch, system) belong to other lanes, not this file;
    - no W/GX bridge (target-only reachability); no whole-word or
      whole-vector atomicity beyond the guarded folds; no source,
      checker, contract, entry, ABI, loader, budget or liveness
      claim; no hardware correspondence beyond self-consistency
      (silicon and timing assumptions live in the family files,
      not re-checked here).
-/

#print axioms rest_uc_still
#print axioms rest_union_uc
#print axioms rest_uc_geraet
#print axioms rest_port_still
#print axioms rest_union_port
#print axioms rest_port_bus
#print axioms rest_fp_tso
#print axioms rest_union_fp
#print axioms rest_fehler_tso
#print axioms rest_union_fehler
#print axioms rest_tor_still
#print axioms rest_union_tor
#print axioms rest_vec_speicher_erreichbar
#print axioms rest_vec_tso
#print axioms rest_union_vec
#print axioms rest_integer666_still
#print axioms rest_union_bild
#print axioms rest_union_instanzen
#print axioms rest_asyncFertig_puffer
#print axioms rest_async_puffer_still
#print axioms rest_int_puffer
#print axioms rest_nest_puffer_still
#print axioms rest_nested_puffer
#print axioms rest_int_befund
#print axioms rest_int_verweigert
#print axioms rest_acht_tso
#print axioms rest_zeuge

end Gabbro.Grammatik.X86
