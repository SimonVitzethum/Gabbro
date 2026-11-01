/-
  File:    Grammatik/Geraet.lean
  Subject: **The async device as a step of the run model** -- and what that step
             does NOT cover.

  ## Context

  Today the device exists only synchronously: `Orakel.wirkt` acts AT the call
  site (an axiom call), `Orakel.regLies` answers AT the read, `Orakel.regSchreib`
  leaves the world unchanged. There is no step in `Lauf` (Wettlauf.lean) that IS
  the device. And per SYNTAX.md:985 a register is OUTSIDE the world -- a device
  is not a carrier, so no grammar transition can move its state.

  This file adds that step: `GSchritt.dma t` writes the DMA-visible buffer
  carrier `t` WITHOUT taking any lock (by construction it carries no `Λ` and no
  held list; `geraet_ohne_sperre` is `rfl`). The step is ordered into the run by
  `GHB`, which keeps the two CPU edges of `HB` (program order, lock sync) and
  adds the two device edges (`devVor`, `devNach`) keyed on an explicit guard
  handoff.

  ## Theorems and premises

    `geraet_ohne_sperre`   -- the device step carries no locks (`rfl`).
    `geraet_ohne_wettlauf` -- RACE-FREEDOM for DMA-visible carriers: a CPU access
      and the device write to the same carrier `t` are `GHB`-ordered, UNDER:
      (a) `GeraetWache`: handoff (`gibt W`) before, take-back (`nimmt W`) after
          the device write, plus `DmaSichtbar t` (shared carrier);
      (b) `haussen`: the CPU access is ordered against the window ENDPOINTS
          (`GHB i k` or `GHB m i`). That half is the driver's lock-discipline
          obligation -- the shape `geordnet_durch_sperre` discharges per driver;
          this theorem connects it to the device step, nothing more.
    `dma_uebergabe`        -- ordering (proved) next to content (assumed), so the
      two halves never mix silently.
    `fenster_ende`         -- one window orders itself: handoff before
      take-back, through its write.
    `glied_kante`          -- across one link: take-back before next handoff,
      by program order of the driver thread that hands the buffer over again.
    `kette_anfang_vor_schreib` / `kette_anfang_vor_ende` /
    `kette_schreib_vor_ende` -- chained windows preserve ordering: the first
      handoff precedes every write, every write precedes the last take-back.
    `kette_ohne_wettlauf`  -- a CPU access ordered against the chain ENDPOINTS
      (first handoff, last take-back) is ordered against EVERY device write of
      the chain.
    `kette_uebergabe`      -- the chain umbrella: ordering proved, content
      (`dma_inhalt`, per window) assumed.

  ## What stays an assumption

  `dma_inhalt` is the CONTENT invariant as a NAMED assumption: what the device
  observes at `(gl, t, j)`. It must be taken as a hypothesis; nothing here
  derives it. That is structural, not caution: events carry no values, so from a
  run alone no content claim follows. `#print axioms` below shows the split:
  `geraet_ohne_wettlauf` does not depend on it, `dma_uebergabe` does.

  `dma_visibility_in_order` covers ORDER ONLY: that two volatile accesses become
  visible to the device in program order. It says nothing about VALUES -- order
  without `dma_inhalt` leaves the content half open, content without order
  leaves the race half open. Each name carries exactly one duty.

  ## Cuts (booked, not hidden)

    (C1) One guard per chain: every window of a `KetteGeordnet` runs under the
         SAME guard `W`, and consecutive windows are linked by the driver
         thread that takes the buffer back and hands it over again
         (`FensterGlied`, discharged per driver like `haussen`). Windows under
         DIFFERENT guards have no edge between them here -- `sync` needs one
         lock -- so a multi-guard chain stays cut, not faked.
    (C2) The CPU-side ordering `haussen` is a premise, discharged per driver
         (cf. `geordnet_durch_sperre`). This file proves the device connection.
    (C3) The guard is a lock give/take. A doorbell handoff through a REGISTER
         has no event -- registers are outside the world -- so mapping a real
         doorbell onto `gibt`/`nimmt` is a driver-side argument, not a theorem.
     (C4) No full-run interleaving with device steps: `GLauf` carries the steps,
          but there is no `Gesittet` over `GLauf` yet (W3-W5 speak CPU only).

   ## Entwurfsformen (nur `def`, keine Saetze) -- Nummern 6-8 unten

     (M1) Kette ueber WachenMENGEN: `GeraetFensterM` (Fenster mit eigenem
          Waechter), `FensterGliedM` (Verknuepfung ueber verschiedene Wachen
          durch denselben Treiberfaden), `KetteGeordnetM` (geordnete Kette),
          `KetteUeberWachen` (Kette ueber einer Wachenmenge `Ws`).
     (M2) Tuerklingel als EREIGNIS: `TuerklingelEreignis` (Registersatz als
          Uebergabe -- das Register steht nur mit Namen und Klasse darin,
          sein Zustand lebt ausserhalb der Welt: die Tuer, nicht der Raum),
          `TuerklingelZuFenster` (Klingel oeffnet Fenster: `d = k`),
          `TuerklingelRueckgabe` (Rueckklingel am `nimmt`).
     (M3) Gesittet ueber Geraetelaeufen: `GLauf.cpuAnteil` (CPU-Anteil),
          `GGesittet` (Wohlgeformtheit als Praedikat: CPU-Anteil gesittet,
          jeder Geraeteschritt in bewachtem Fenster).

   ## Schnitte (gebucht, nicht versteckt) -- Fortsetzung

     (C5) Kanten ueber verschiedene Wachen tragen nur `po` des verkettenden
          Fadens, kein `sync`: zwischen fremden Wachen gibt es hier keine
          Kante -- die Kreuzordnung bleibt Treiberpflicht wie `haussen`.
     (C6) Die Abbildung eines echten Registersatzes auf `gibt`/`nimmt` ist ein
          treiberseitiges Argument, kein Satz (wie C3): die Klingel nennt das
          Register, nicht seinen Zustand.
     (C7) `GGesittet` ist die FORM; §11 verbindet jeden BEWACHTEN Einzelschritt
          mit `GHB` (`ggesittet_fenster_geordnet`, `ggesittet_ohne_wettlauf`) --
          das Ketten-Gegenstueck ueber `GGesittet` und die Bruecke `HB` -> `GHB`
          ueber `cpuAnteil` bleiben Schnitt (C4 fuellt das Praedikat, nicht den Satz).
-/
module

public import Grammatik.Kern.Semantik.Geraet.Teil1
public import Grammatik.Kern.Semantik.Geraet.Teil2
