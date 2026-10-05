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
import Grammatik.X86.HwKapsteinTso
import Grammatik.X86.HwKapsteinSteps

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

end Gabbro.Grammatik.X86
