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

end Gabbro.Grammatik.X86
