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
import Grammatik.Wettlauf

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The device step: a buffer write that takes no locks -/

/-- A run step is a CPU step or a device write of the buffer carrier `t`.
    The device branch carries no guard list and no held list -- unlike
    `Ereignis.zugriff`, which records both. -/
inductive GSchritt where
  | cpu : Schritt D → GSchritt
  | dma : D.Tab → GSchritt

/-- A run with device steps. -/
abbrev GLauf (D : Deklaration) := List (GSchritt (D := D))

/-- A DMA-visible carrier is a shared one: a private carrier never meets the device. -/
def DmaSichtbar (t : D.Tab) : Prop := D.geteilt t = true

/-- The locks a step holds, as recorded on the step itself. -/
def GSchritt.sperren : GSchritt (D := D) → List D.Lock
  | .cpu s =>
      match s.ereignis with
      | .zugriff _ _ _ h => h
      | .gzugriff _ _ _ h => h
      | .nimmt _ h => h
      | .gibt _ => []
  | .dma _ => []

/-- **The device takes no locks.** By construction: the `dma` branch has no
    lock list to fill. -/
theorem geraet_ohne_sperre (t : D.Tab) :
    (GSchritt.dma (D := D) t).sperren = [] :=
  rfl

/-! ## 2. Guard-respect: the device fires only inside a handed-over window -/

/-- Guard-respect for one device write `j` to `t`: some thread hands the buffer
    over (`gibt W` at `k`), some thread takes it back (`nimmt W` at `m`), and
    the write lies strictly between. The carrier is DMA-visible. -/
structure GeraetWache (gl : GLauf D) (W : D.Lock) (t : D.Tab) (k m j : Nat) : Prop where
  sichtbar : DmaSichtbar t
  gibt : ∃ f, gl[k]? = some (GSchritt.cpu ⟨f, .gibt W⟩)
  schreibt : gl[j]? = some (GSchritt.dma t)
  nimmt : ∃ f h, gl[m]? = some (GSchritt.cpu ⟨f, .nimmt W h⟩)
  vor : k < j
  nach : j < m

/-- A CPU access to carrier `t` at index `i`: the step and the carrier match. -/
structure CpuZugriff (gl : GLauf D) (t : D.Tab) where
  idx : Nat
  f : Faden
  ei : Ereignis D
  hi : gl[idx]? = some (GSchritt.cpu ⟨f, ei⟩)
  ht : ei.traeger = some (.inl t)

/-! ## 3. Happens-before with the device edge -/

/-- Happens-before over runs with device steps: the two CPU edges (`po`,
    `sync`, as in `HB`) plus the guard edges -- handoff before the device
    write, device write before take-back -- closed under transitivity. -/
inductive GHB (gl : GLauf D) : Nat → Nat → Prop where
  | po (f : Faden) (i j : Nat) (ei ej : Ereignis D)
      (hi : gl[i]? = some (GSchritt.cpu ⟨f, ei⟩))
      (hj : gl[j]? = some (GSchritt.cpu ⟨f, ej⟩)) (hij : i < j) : GHB gl i j
  | sync (f g : Faden) (L : D.Lock) (h : List D.Lock) (i j : Nat)
      (hi : gl[i]? = some (GSchritt.cpu ⟨f, .gibt L⟩))
      (hj : gl[j]? = some (GSchritt.cpu ⟨g, .nimmt L h⟩)) (hij : i < j) : GHB gl i j
  | devVor (W : D.Lock) (f : Faden) (k j : Nat) (t : D.Tab)
      (hk : gl[k]? = some (GSchritt.cpu ⟨f, .gibt W⟩))
      (hj : gl[j]? = some (GSchritt.dma t)) (hkj : k < j) : GHB gl k j
  | devNach (W : D.Lock) (f : Faden) (h : List D.Lock) (j m : Nat) (t : D.Tab)
      (hj : gl[j]? = some (GSchritt.dma t))
      (hm : gl[m]? = some (GSchritt.cpu ⟨f, .nimmt W h⟩)) (hjm : j < m) : GHB gl j m
  | trans (i j k : Nat) (h1 : GHB gl i j) (h2 : GHB gl j k) : GHB gl i k

/-! ## 4. Race-freedom under the guard premise; content only by name -/

/-- **No race on a DMA-visible carrier, under the device-guard premise.**
    A CPU access at `hz.idx` and the device write at `j` to the same carrier
    are ordered -- provided the write sits in a guarded window (`hw`) and the
    access is ordered against the window endpoints (`haussen`, the driver's
    lock-discipline half). The new content over `geordnet_durch_sperre` is the
    device connection: the two guard edges plus transitivity. -/
theorem geraet_ohne_wettlauf (gl : GLauf D) (W : D.Lock) (t : D.Tab) (k m j : Nat)
    (hw : GeraetWache gl W t k m j) (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx k ∨ GHB gl m hz.idx) :
    GHB gl hz.idx j ∨ GHB gl j hz.idx := by
  obtain ⟨f1, hk⟩ := hw.gibt
  obtain ⟨f2, h, hm⟩ := hw.nimmt
  rcases haussen with h1 | h1
  · exact Or.inl (GHB.trans _ _ _ h1 (GHB.devVor W f1 k j t hk hw.schreibt hw.vor))
  · exact Or.inr (GHB.trans _ _ _ (GHB.devNach W f2 h j m t hw.schreibt hm hw.nach) h1)

/-- **The content invariant as a NAMED assumption.** What the device observes
    at `(gl, t, j)`. Events carry no values, so no run fact implies it -- any
    content claim takes this as a hypothesis. Order (`dma_visibility_in_order`)
    is a different name for a different duty. -/
axiom dma_inhalt (D : Deklaration) : GLauf D → D.Tab → Nat → Prop

/-- Ordering proved, content assumed -- side by side, never mixed silently. -/
theorem dma_uebergabe (gl : GLauf D) (W : D.Lock) (t : D.Tab) (k m j : Nat)
    (hw : GeraetWache gl W t k m j) (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx k ∨ GHB gl m hz.idx) (hinhalt : dma_inhalt D gl t j) :
    (GHB gl hz.idx j ∨ GHB gl j hz.idx) ∧ dma_inhalt D gl t j :=
  ⟨geraet_ohne_wettlauf gl W t k m j hw hz haussen, hinhalt⟩

/-! ## 5. Window chaining: several device writes, linked explicitly -/

/-- One link of a window chain: a guarded window for carrier `t` under the
    SAME guard `W`, with its witness carried along. Chaining under one guard
    is what keeps every edge inside `GHB`: the window interiors ride `devVor`
    / `devNach`, the links ride `po` (see `FensterGlied`). -/
structure GeraetFenster (gl : GLauf D) (W : D.Lock) (t : D.Tab) where
  k : Nat
  m : Nat
  j : Nat
  wache : GeraetWache gl W t k m j

/-- Linkage: the thread that takes the buffer back hands it over again --
    take-back at `a.m` and handoff at `b.k` by the SAME thread, in order.
    The same-thread premise is the driver's chaining discipline (like
    `haussen`, discharged per driver); the `po` edge it yields is what links
    the windows. A take-back followed by a FOREIGN handoff has no edge here.
    The thread is existentially bound, so the linkage stays a `Prop`. -/
structure FensterGlied {gl : GLauf D} {W : D.Lock} {t : D.Tab}
    (a b : GeraetFenster gl W t) : Prop where
  nimmt_gibt : ∃ f h, gl[a.m]? = some (GSchritt.cpu ⟨f, .nimmt W h⟩) ∧
    gl[b.k]? = some (GSchritt.cpu ⟨f, .gibt W⟩)
  reihe : a.m < b.k

/-- An ordered chain: every window hands to the next through one driver
    thread's take-back / handoff pair. -/
def KetteGeordnet (gl : GLauf D) (W : D.Lock) (t : D.Tab) :
    List (GeraetFenster gl W t) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => FensterGlied a b ∧ KetteGeordnet gl W t (b :: rest)

/-- The last window of a chain, if any. Own definition so the inductions below
    compute by `rfl` instead of leaning on library lemma names. -/
def kettenEnde : List (GeraetFenster gl W t) → Option (GeraetFenster gl W t)
  | [] => none
  | [x] => some x
  | _ :: y :: rest => kettenEnde (y :: rest)

/-- One window orders itself: handoff before take-back, through its write. -/
theorem fenster_ende (w : GeraetFenster gl W t) : GHB gl w.k w.m := by
  obtain ⟨f1, hk⟩ := w.wache.gibt
  obtain ⟨f2, h, hm⟩ := w.wache.nimmt
  exact GHB.trans _ _ _ (GHB.devVor W f1 w.k w.j t hk w.wache.schreibt w.wache.vor)
    (GHB.devNach W f2 h w.j w.m t w.wache.schreibt hm w.wache.nach)

/-- Across one link: the earlier take-back precedes the later handoff, by
    program order of the linking driver thread. -/
theorem glied_kante {a b : GeraetFenster gl W t} (l : FensterGlied a b) :
    GHB gl a.m b.k := by
  obtain ⟨f, h, hnimmt, hgibt⟩ := l.nimmt_gibt
  exact GHB.po f a.m b.k _ _ hnimmt hgibt l.reihe

/-- Chained windows preserve ordering, first half: the first handoff precedes
    EVERY write of the chain. -/
theorem kette_anfang_vor_schreib : ∀ (ch : List (GeraetFenster gl W t)),
    KetteGeordnet gl W t ch → ∀ (a : GeraetFenster gl W t),
    ch.head? = some a → ∀ (w : GeraetFenster gl W t), w ∈ ch → GHB gl a.k w.j := by
  intro ch
  induction ch with
  | nil =>
    intro _ a ha w hm
    cases hm
  | cons x rest ih =>
    intro ho a ha w hm
    have hax : a = x := (Option.some_inj.mp ha).symm
    subst a
    cases List.mem_cons.mp hm with
    | inl heq =>
      subst w
      obtain ⟨f1, hk⟩ := x.wache.gibt
      exact GHB.devVor W f1 x.k x.j t hk x.wache.schreibt x.wache.vor
    | inr hmem =>
      cases rest with
      | nil => cases hmem
      | cons y rest' =>
        simp only [KetteGeordnet] at ho
        obtain ⟨link, ho'⟩ := ho
        have hhead : (y :: rest').head? = some y := rfl
        have ih' := ih ho' y hhead w hmem
        exact GHB.trans _ _ _ (GHB.trans _ _ _ (fenster_ende x) (glied_kante link)) ih'

/-- Chained windows preserve ordering, endpoints: the first handoff precedes
    the last take-back, through every link. -/
theorem kette_anfang_vor_ende : ∀ (ch : List (GeraetFenster gl W t)),
    KetteGeordnet gl W t ch → ∀ (a z : GeraetFenster gl W t),
    ch.head? = some a → kettenEnde ch = some z → GHB gl a.k z.m := by
  intro ch
  induction ch with
  | nil =>
    intro _ a z ha _
    exact nomatch ha
  | cons x rest ih =>
    intro ho a z ha hz
    have hax : a = x := (Option.some_inj.mp ha).symm
    subst a
    cases rest with
    | nil =>
      have hzx : z = x := (Option.some_inj.mp hz).symm
      subst z
      exact fenster_ende x
    | cons y rest' =>
      simp only [KetteGeordnet] at ho
      obtain ⟨link, ho'⟩ := ho
      have hhead : (y :: rest').head? = some y := rfl
      have hend : kettenEnde (y :: rest') = some z := hz
      have ih' := ih ho' y z hhead hend
      exact GHB.trans _ _ _ (GHB.trans _ _ _ (fenster_ende x) (glied_kante link)) ih'

/-- Chained windows preserve ordering, second half: EVERY write of the chain
    precedes the last take-back. -/
theorem kette_schreib_vor_ende : ∀ (ch : List (GeraetFenster gl W t)),
    KetteGeordnet gl W t ch → ∀ (z : GeraetFenster gl W t),
    kettenEnde ch = some z → ∀ (w : GeraetFenster gl W t), w ∈ ch → GHB gl w.j z.m := by
  intro ch
  induction ch with
  | nil =>
    intro _ z hz w hm
    cases hm
  | cons x rest ih =>
    intro ho z hz w hm
    cases List.mem_cons.mp hm with
    | inl heq =>
      subst w
      cases rest with
      | nil =>
        have hzx : z = x := (Option.some_inj.mp hz).symm
        subst z
        obtain ⟨f2, h, hm⟩ := x.wache.nimmt
        exact GHB.devNach W f2 h x.j x.m t x.wache.schreibt hm x.wache.nach
      | cons y rest' =>
        simp only [KetteGeordnet] at ho
        obtain ⟨link, ho'⟩ := ho
        have hhead : (y :: rest').head? = some y := rfl
        have hend : kettenEnde (y :: rest') = some z := hz
        have hrest := kette_anfang_vor_ende (y :: rest') ho' y z hhead hend
        obtain ⟨f2, h, hm⟩ := x.wache.nimmt
        exact GHB.trans _ _ _
          (GHB.devNach W f2 h x.j x.m t x.wache.schreibt hm x.wache.nach)
          (GHB.trans _ _ _ (glied_kante link) hrest)
    | inr hmem =>
      cases rest with
      | nil => cases hmem
      | cons y rest' =>
        simp only [KetteGeordnet] at ho
        obtain ⟨_, ho'⟩ := ho
        have hend : kettenEnde (y :: rest') = some z := hz
        exact ih ho' z hend w hmem

/-- **Chained race-freedom.** A CPU access ordered against the chain ENDPOINTS
    (first handoff, last take-back) is ordered against EVERY device write of
    the chain -- the chain analogue of `geraet_ohne_wettlauf`. The endpoint
    half stays the driver's obligation; this theorem connects it to every
    write of the chain, nothing more. -/
theorem kette_ohne_wettlauf (ch : List (GeraetFenster gl W t))
    (ho : KetteGeordnet gl W t ch) (hz : CpuZugriff gl t)
    (a z : GeraetFenster gl W t)
    (ha : ch.head? = some a) (hzend : kettenEnde ch = some z)
    (haussen : GHB gl hz.idx a.k ∨ GHB gl z.m hz.idx) :
    ∀ w ∈ ch, GHB gl hz.idx w.j ∨ GHB gl w.j hz.idx := by
  intro w hm
  rcases haussen with h1 | h1
  · exact Or.inl (GHB.trans _ _ _ h1 (kette_anfang_vor_schreib ch ho a ha w hm))
  · exact Or.inr (GHB.trans _ _ _ (kette_schreib_vor_ende ch ho z hzend w hm) h1)

/-- Ordering proved, content assumed -- over the whole chain. Each window's
    content half still takes `dma_inhalt` as a hypothesis: events carry no
    values, so a chain of runs derives no more content than one run. -/
theorem kette_uebergabe (ch : List (GeraetFenster gl W t))
    (ho : KetteGeordnet gl W t ch) (hz : CpuZugriff gl t)
    (a z : GeraetFenster gl W t)
    (ha : ch.head? = some a) (hzend : kettenEnde ch = some z)
    (haussen : GHB gl hz.idx a.k ∨ GHB gl z.m hz.idx)
    (hinhalt : ∀ w ∈ ch, dma_inhalt D gl t w.j) :
    (∀ w ∈ ch, GHB gl hz.idx w.j ∨ GHB gl w.j hz.idx) ∧
    ∀ w ∈ ch, dma_inhalt D gl t w.j :=
  ⟨kette_ohne_wettlauf ch ho hz a z ha hzend haussen, hinhalt⟩

#print axioms Gabbro.Grammatik.geraet_ohne_sperre
#print axioms Gabbro.Grammatik.geraet_ohne_wettlauf
#print axioms Gabbro.Grammatik.dma_uebergabe
#print axioms Gabbro.Grammatik.fenster_ende
#print axioms Gabbro.Grammatik.glied_kante
#print axioms Gabbro.Grammatik.kette_anfang_vor_schreib
#print axioms Gabbro.Grammatik.kette_anfang_vor_ende
#print axioms Gabbro.Grammatik.kette_schreib_vor_ende
#print axioms Gabbro.Grammatik.kette_ohne_wettlauf
#print axioms Gabbro.Grammatik.kette_uebergabe

/-! ## 6. Ketten ueber mehrere Wachen: jedes Fenster traegt seine eigene -/

/-- Ein Fenster mit eigenem Waechter: das Paar aus Wache `W` und Fenster
    darunter. Die Kette aus Abschnitt 5 laeuft unter EINER Wache `W`; hier
    traegt jedes Fenster seine eigene -- die Menge der Wachen einer Kette
    steht erst in `KetteUeberWachen`. -/
def GeraetFensterM (gl : GLauf D) (t : D.Tab) : Type :=
  (W : D.Lock) × GeraetFenster gl W t

/-- Verknuepfung ueber (moeglicherweise) verschiedene Wachen hinweg: derselbe
    Faden nimmt den Puffer unter `a.1` zurueck und gibt ihn unter `b.1` wieder
    heraus, in dieser Reihenfolge. Bei gleicher Wache faellt das mit
    `FensterGlied` zusammen; bei fremder Wache traegt nur `po` des
    verkettenden Fadens -- kein `sync` (Schnitt C5). -/
def FensterGliedM {gl : GLauf D} {t : D.Tab} (a b : GeraetFensterM gl t) : Prop :=
  ∃ f h, gl[a.2.m]? = some (GSchritt.cpu ⟨f, .nimmt a.1 h⟩) ∧
    gl[b.2.k]? = some (GSchritt.cpu ⟨f, .gibt b.1⟩) ∧ a.2.m < b.2.k

/-- Eine geordnete Kette ueber mehrere Wachen: jedes Fenster reicht an das
    naechste durch einen Treiberfaden weiter (`FensterGliedM`). -/
def KetteGeordnetM (gl : GLauf D) (t : D.Tab) : List (GeraetFensterM gl t) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => FensterGliedM a b ∧ KetteGeordnetM gl t (b :: rest)

/-- Kette ueber einer WachenMENGE `Ws`: jedes Fenster der Kette wacht unter
    einer Wache aus `Ws`, und die Fenster sind geordnet verkettet. -/
def KetteUeberWachen (gl : GLauf D) (t : D.Tab) (Ws : List D.Lock)
    (ch : List (GeraetFensterM gl t)) : Prop :=
  (∀ w ∈ ch, w.1 ∈ Ws) ∧ KetteGeordnetM gl t ch

/-! ## 7. Tuerklingel als Ereignis: der Registersatz als Uebergabe -/

/-- Das Tuerklingelereignis am Index `d`: ein Faden gibt die Wache `W` heraus
    -- und genau dieser Schritt STEHT fuer den Registersatz auf `r`. Das
    Register erscheint nur mit Namen und Klasse (`schreibbar`); sein Zustand
    lebt ausserhalb der Welt, darum modelliert das Ereignis die Tuer, nicht
    den Raum. -/
def TuerklingelEreignis (gl : GLauf D) (r : D.Reg) (W : D.Lock) (d : Nat) : Prop :=
  (D.rklasse r).schreibbar = true ∧
    ∃ f, gl[d]? = some (GSchritt.cpu ⟨f, .gibt W⟩)

/-- Die Klingel oeffnet das Fenster: die Wache aus `GeraetWache` gilt, die
    Klingel laeutet, und beides trifft sich am Uebergabeindex (`d = k`). Dass
    ein echter Registersatz genau dort wirkt, bleibt ein treiberseitiges
    Argument (Schnitt C6). -/
def TuerklingelZuFenster (gl : GLauf D) (r : D.Reg) (W : D.Lock) (t : D.Tab)
    (k m j d : Nat) : Prop :=
  GeraetWache gl W t k m j ∧ TuerklingelEreignis gl r W d ∧ d = k

/-- Die Rueckklingel am Index `d`: ein Faden nimmt die Wache `W` zurueck --
    das Gegenstueck zur Uebergabe am Fensterende. Das Register ist hier das
    lesbare Zustandsregister, an dem der Treiber die Rueckgabe sieht; auch
    hier steht nur Name und Klasse darin, kein Zustand. -/
def TuerklingelRueckgabe (gl : GLauf D) (r : D.Reg) (W : D.Lock) (d : Nat) : Prop :=
  (D.rklasse r).lesbar = true ∧
    ∃ f h, gl[d]? = some (GSchritt.cpu ⟨f, .nimmt W h⟩)

/-! ## 8. Gesittet ueber Geraetelaeufen: Wohlgeformtheit als Praedikat -/

/-- Der CPU-Anteil eines Geraetelaufs: die `cpu`-Schritte in Reihenfolge, die
    `dma`-Schritte entfallen. Ueber ihn spricht W1-W5 weiter. -/
def GLauf.cpuAnteil : GLauf D → Lauf D
  | [] => []
  | GSchritt.cpu s :: rest => s :: GLauf.cpuAnteil rest
  | GSchritt.dma _ :: rest => GLauf.cpuAnteil rest

/-- Wohlgeformtheit eines Geraetelaufs als Praedikat: der CPU-Anteil ist
    gesittet (W1-W5 sprechen nur CPU), und jeder Geraeteschritt sitzt in einem
    bewachten Fenster (`GeraetWache` traegt `DmaSichtbar` schon). Die FORM
    steht hier; der Satz, der sie mit `GHB` verbindet, bleibt Schnitt (C7). -/
def GGesittet (gl : GLauf D) : Prop :=
  Gesittet gl.cpuAnteil ∧
    ∀ (t : D.Tab) (j : Nat),
      gl[j]? = some (GSchritt.dma t) → ∃ W k m, GeraetWache gl W t k m j

/-! ## 9. Cross-guard chains preserve endpoint ordering -/

/-- The last window of a multi-guard chain, if any. Own definition so the
    inductions below compute by `rfl`, like `kettenEnde` in §5. -/
def kettenEndeM : List (GeraetFensterM gl t) → Option (GeraetFensterM gl t)
  | [] => none
  | [x] => some x
  | _ :: y :: rest => kettenEndeM (y :: rest)

/-- Across one cross-guard link: the earlier take-back precedes the later
    handoff, by program order of the linking driver thread. The guards may
    differ (`a.1`, `b.1`); the edge carries only that thread's `po`, never a
    `sync` between foreign guards (cut C5). -/
theorem gliedM_kante {a b : GeraetFensterM gl t} (l : FensterGliedM a b) :
    GHB gl a.2.m b.2.k := by
  obtain ⟨f, h, hnimmt, hgibt, hreihe⟩ := l
  exact GHB.po f a.2.m b.2.k _ _ hnimmt hgibt hreihe

/-- Cross-guard chains preserve ordering, first half: the first handoff
    precedes EVERY write of the chain. Each window rides its OWN guard's
    `devVor`/`devNach`; the links ride the driver's `po` (`gliedM_kante`). -/
theorem ketteM_anfang_vor_schreib : ∀ (ch : List (GeraetFensterM gl t)),
    KetteGeordnetM gl t ch → ∀ (a : GeraetFensterM gl t),
    ch.head? = some a → ∀ (w : GeraetFensterM gl t), w ∈ ch → GHB gl a.2.k w.2.j := by
  intro ch
  induction ch with
  | nil =>
    intro _ a ha w hm
    cases hm
  | cons x rest ih =>
    intro ho a ha w hm
    have hax : a = x := (Option.some_inj.mp ha).symm
    subst a
    cases List.mem_cons.mp hm with
    | inl heq =>
      subst w
      obtain ⟨f1, hk⟩ := x.2.wache.gibt
      exact GHB.devVor x.1 f1 x.2.k x.2.j t hk x.2.wache.schreibt x.2.wache.vor
    | inr hmem =>
      cases rest with
      | nil => cases hmem
      | cons y rest' =>
        simp only [KetteGeordnetM] at ho
        obtain ⟨link, ho'⟩ := ho
        have hhead : (y :: rest').head? = some y := rfl
        have ih' := ih ho' y hhead w hmem
        exact GHB.trans _ _ _ (GHB.trans _ _ _ (fenster_ende x.2) (gliedM_kante link)) ih'

/-- Cross-guard chains preserve ordering, endpoints: the first handoff
    precedes the last take-back, through every link. -/
theorem ketteM_anfang_vor_ende : ∀ (ch : List (GeraetFensterM gl t)),
    KetteGeordnetM gl t ch → ∀ (a z : GeraetFensterM gl t),
    ch.head? = some a → kettenEndeM ch = some z → GHB gl a.2.k z.2.m := by
  intro ch
  induction ch with
  | nil =>
    intro _ a z ha _
    exact nomatch ha
  | cons x rest ih =>
    intro ho a z ha hz
    have hax : a = x := (Option.some_inj.mp ha).symm
    subst a
    cases rest with
    | nil =>
      have hzx : z = x := (Option.some_inj.mp hz).symm
      subst z
      exact fenster_ende x.2
    | cons y rest' =>
      simp only [KetteGeordnetM] at ho
      obtain ⟨link, ho'⟩ := ho
      have hhead : (y :: rest').head? = some y := rfl
      have hend : kettenEndeM (y :: rest') = some z := hz
      have ih' := ih ho' y z hhead hend
      exact GHB.trans _ _ _ (GHB.trans _ _ _ (fenster_ende x.2) (gliedM_kante link)) ih'

/-- Cross-guard chains preserve ordering, second half: EVERY write of the
    chain precedes the last take-back. -/
theorem ketteM_schreib_vor_ende : ∀ (ch : List (GeraetFensterM gl t)),
    KetteGeordnetM gl t ch → ∀ (z : GeraetFensterM gl t),
    kettenEndeM ch = some z → ∀ (w : GeraetFensterM gl t), w ∈ ch → GHB gl w.2.j z.2.m := by
  intro ch
  induction ch with
  | nil =>
    intro _ z hz w hm
    cases hm
  | cons x rest ih =>
    intro ho z hz w hm
    cases List.mem_cons.mp hm with
    | inl heq =>
      subst w
      cases rest with
      | nil =>
        have hzx : z = x := (Option.some_inj.mp hz).symm
        subst z
        obtain ⟨f2, h, hm⟩ := x.2.wache.nimmt
        exact GHB.devNach x.1 f2 h x.2.j x.2.m t x.2.wache.schreibt hm x.2.wache.nach
      | cons y rest' =>
        simp only [KetteGeordnetM] at ho
        obtain ⟨link, ho'⟩ := ho
        have hhead : (y :: rest').head? = some y := rfl
        have hend : kettenEndeM (y :: rest') = some z := hz
        have hrest := ketteM_anfang_vor_ende (y :: rest') ho' y z hhead hend
        obtain ⟨f2, h, hm⟩ := x.2.wache.nimmt
        exact GHB.trans _ _ _
          (GHB.devNach x.1 f2 h x.2.j x.2.m t x.2.wache.schreibt hm x.2.wache.nach)
          (GHB.trans _ _ _ (gliedM_kante link) hrest)
    | inr hmem =>
      cases rest with
      | nil => cases hmem
      | cons y rest' =>
        simp only [KetteGeordnetM] at ho
        obtain ⟨_, ho'⟩ := ho
        have hend : kettenEndeM (y :: rest') = some z := hz
        exact ih ho' z hend w hmem

/-- **Cross-guard race-freedom.** A CPU access ordered against the chain
    ENDPOINTS (first handoff, last take-back) is ordered against EVERY device
    write of the chain -- the chain analogue of `geraet_ohne_wettlauf` over
    several guards. The endpoint half stays the driver's obligation. -/
theorem ketteM_ohne_wettlauf (ch : List (GeraetFensterM gl t))
    (ho : KetteGeordnetM gl t ch) (hz : CpuZugriff gl t)
    (a z : GeraetFensterM gl t)
    (ha : ch.head? = some a) (hzend : kettenEndeM ch = some z)
    (haussen : GHB gl hz.idx a.2.k ∨ GHB gl z.2.m hz.idx) :
    ∀ w ∈ ch, GHB gl hz.idx w.2.j ∨ GHB gl w.2.j hz.idx := by
  intro w hm
  rcases haussen with h1 | h1
  · exact Or.inl (GHB.trans _ _ _ h1 (ketteM_anfang_vor_schreib ch ho a ha w hm))
  · exact Or.inr (GHB.trans _ _ _ (ketteM_schreib_vor_ende ch ho z hzend w hm) h1)

/-- Ordering proved, content assumed -- over the whole cross-guard chain. Each
    window's content half still takes `dma_inhalt` as a hypothesis: events
    carry no values, so a chain of runs derives no more content than one run. -/
theorem ketteM_uebergabe (ch : List (GeraetFensterM gl t))
    (ho : KetteGeordnetM gl t ch) (hz : CpuZugriff gl t)
    (a z : GeraetFensterM gl t)
    (ha : ch.head? = some a) (hzend : kettenEndeM ch = some z)
    (haussen : GHB gl hz.idx a.2.k ∨ GHB gl z.2.m hz.idx)
    (hinhalt : ∀ w ∈ ch, dma_inhalt D gl t w.2.j) :
    (∀ w ∈ ch, GHB gl hz.idx w.2.j ∨ GHB gl w.2.j hz.idx) ∧
    ∀ w ∈ ch, dma_inhalt D gl t w.2.j :=
  ⟨ketteM_ohne_wettlauf ch ho hz a z ha hzend haussen, hinhalt⟩

/-- **Chain over a guard SET, endpoints.** A `KetteUeberWachen` is a
    `KetteGeordnetM` whose windows all watch under guards from `Ws`; the
    endpoint ordering needs nothing beyond that bundle. -/
theorem ketteWachen_anfang_vor_ende (Ws : List D.Lock) (ch : List (GeraetFensterM gl t))
    (hW : KetteUeberWachen gl t Ws ch) (a z : GeraetFensterM gl t)
    (ha : ch.head? = some a) (hzend : kettenEndeM ch = some z) :
    GHB gl a.2.k z.2.m := by
  obtain ⟨_, ho⟩ := hW
  exact ketteM_anfang_vor_ende ch ho a z ha hzend

/-- **Chain over a guard SET, race-freedom.** A CPU access ordered against the
    chain endpoints is ordered against every device write of the chain. -/
theorem ketteWachen_ohne_wettlauf (Ws : List D.Lock) (ch : List (GeraetFensterM gl t))
    (hW : KetteUeberWachen gl t Ws ch) (hz : CpuZugriff gl t)
    (a z : GeraetFensterM gl t)
    (ha : ch.head? = some a) (hzend : kettenEndeM ch = some z)
    (haussen : GHB gl hz.idx a.2.k ∨ GHB gl z.2.m hz.idx) :
    ∀ w ∈ ch, GHB gl hz.idx w.2.j ∨ GHB gl w.2.j hz.idx := by
  obtain ⟨_, ho⟩ := hW
  exact ketteM_ohne_wettlauf ch ho hz a z ha hzend haussen

/-! ## 10. The doorbell opens the window -/

/-- **The bell opens the window.** A doorbell event that coincides with the
    window handoff (`d = k`) precedes the device write -- the handoff edge,
    named at the bell. That a real register write acts exactly there stays a
    driver-side argument (cut C6); this lemma connects the bell to the write,
    nothing more. -/
theorem tuerklingel_vor_schreib (h : TuerklingelZuFenster gl r W t k m j d) :
    GHB gl d j := by
  obtain ⟨hw, hkling, hdk⟩ := h
  obtain ⟨_, f, hk⟩ := hkling
  rw [hdk] at hk ⊢
  exact GHB.devVor W f k j t hk hw.schreibt hw.vor

/-- The bell precedes the window end, through the write. -/
theorem tuerklingel_vor_ende (h : TuerklingelZuFenster gl r W t k m j d) :
    GHB gl d m := by
  obtain ⟨hw, hkling, hdk⟩ := h
  obtain ⟨_, f1, hk⟩ := hkling
  obtain ⟨f2, hh, hm⟩ := hw.nimmt
  rw [hdk] at hk ⊢
  exact GHB.trans _ _ _ (GHB.devVor W f1 k j t hk hw.schreibt hw.vor)
    (GHB.devNach W f2 hh j m t hw.schreibt hm hw.nach)

/-- **The return bell closes the window.** A return bell that coincides with
    the take-back (`d' = m`) comes after the device write. -/
theorem rueckklingel_nach_schreib (hw : GeraetWache gl W t k m j)
    (hr : TuerklingelRueckgabe gl r' W d') (hdm : d' = m) : GHB gl j d' := by
  obtain ⟨_, f, hh, hm⟩ := hr
  rw [hdm] at hm ⊢
  exact GHB.devNach W f hh j m t hw.schreibt hm hw.nach

/-- Bell to return bell, through the write: the whole window ordered between
    its two bells. -/
theorem tuerklingel_fenster_geordnet (h : TuerklingelZuFenster gl r W t k m j d)
    (hr : TuerklingelRueckgabe gl r' W d') (hdm : d' = m) : GHB gl d d' := by
  obtain ⟨hw, hkling, hdk⟩ := h
  obtain ⟨_, f1, hk⟩ := hkling
  obtain ⟨_, f2, hh, hm⟩ := hr
  rw [hdk] at hk ⊢
  rw [hdm] at hm ⊢
  exact GHB.trans _ _ _ (GHB.devVor W f1 k j t hk hw.schreibt hw.vor)
    (GHB.devNach W f2 hh j m t hw.schreibt hm hw.nach)

/-- **Race-freedom at the bells.** A CPU access ordered against the two bells
    (handoff bell, return bell) is ordered against the device write -- the
    doorbell analogue of `geraet_ohne_wettlauf`. The return-bell premise ties
    `d'` to a real bell; only its index equation travels into the proof. -/
theorem tuerklingel_ohne_wettlauf (h : TuerklingelZuFenster gl r W t k m j d)
    (_hr : TuerklingelRueckgabe gl r' W d') (hdm : d' = m)
    (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx d ∨ GHB gl d' hz.idx) :
    GHB gl hz.idx j ∨ GHB gl j hz.idx := by
  obtain ⟨hw, _, hdk⟩ := h
  rw [hdk, hdm] at haussen
  exact geraet_ohne_wettlauf gl W t k m j hw hz haussen

/-! ## 11. `GGesittet` meets `GHB`: every guarded step sits in an ordered window -/

/-- The CPU half of a well-formed device run is well-formed (W1-W5 speak CPU
    only, over `cpuAnteil`). -/
theorem ggesittet_cpu (h : GGesittet gl) : Gesittet gl.cpuAnteil := by
  obtain ⟨hcpu, _⟩ := h
  exact hcpu

/-- Every device step of a well-formed device run sits in a guarded window.
    The window carries `DmaSichtbar` already. -/
theorem ggesittet_fenster (h : GGesittet gl) (t : D.Tab) (j : Nat)
    (hj : gl[j]? = some (GSchritt.dma t)) : ∃ W k m, GeraetWache gl W t k m j := by
  obtain ⟨_, hfenster⟩ := h
  exact hfenster t j hj

/-- **Every guarded step is `GHB`-ordered between its window endpoints.**
    This is the per-step link from `GGesittet` to `GHB`: no new premise, just
    the window `GGesittet` supplies, read through the two device edges. The
    window travels in the conclusion, so the guard stays named. -/
theorem ggesittet_fenster_geordnet (h : GGesittet gl) (t : D.Tab) (j : Nat)
    (hj : gl[j]? = some (GSchritt.dma t)) :
    ∃ W k m, GeraetWache gl W t k m j ∧ GHB gl k j ∧ GHB gl j m := by
  obtain ⟨_, hfenster⟩ := h
  obtain ⟨W, k, m, hw⟩ := hfenster t j hj
  obtain ⟨f1, hk⟩ := hw.gibt
  obtain ⟨f2, hh, hm⟩ := hw.nimmt
  exact ⟨W, k, m, hw, GHB.devVor W f1 k j t hk hw.schreibt hw.vor,
    GHB.devNach W f2 hh j m t hw.schreibt hm hw.nach⟩

/-- **Race-freedom over `GGesittet`, per step.** The window comes from
    `GGesittet` (no new premise); only the endpoint half stays the driver's
    obligation (`haussen`), discharged per driver like in `geraet_ohne_wettlauf`. -/
theorem ggesittet_ohne_wettlauf (h : GGesittet gl) (hz : CpuZugriff gl t)
    (hj : gl[j]? = some (GSchritt.dma t))
    (haussen : ∀ W k m, GeraetWache gl W t k m j → GHB gl hz.idx k ∨ GHB gl m hz.idx) :
    GHB gl hz.idx j ∨ GHB gl j hz.idx := by
  obtain ⟨_, hfenster⟩ := h
  obtain ⟨W, k, m, hw⟩ := hfenster t j hj
  exact geraet_ohne_wettlauf gl W t k m j hw hz (haussen W k m hw)

#print axioms Gabbro.Grammatik.gliedM_kante
#print axioms Gabbro.Grammatik.ketteM_anfang_vor_schreib
#print axioms Gabbro.Grammatik.ketteM_anfang_vor_ende
#print axioms Gabbro.Grammatik.ketteM_schreib_vor_ende
#print axioms Gabbro.Grammatik.ketteM_ohne_wettlauf
#print axioms Gabbro.Grammatik.ketteM_uebergabe
#print axioms Gabbro.Grammatik.ketteWachen_anfang_vor_ende
#print axioms Gabbro.Grammatik.ketteWachen_ohne_wettlauf
#print axioms Gabbro.Grammatik.tuerklingel_vor_schreib
#print axioms Gabbro.Grammatik.tuerklingel_vor_ende
#print axioms Gabbro.Grammatik.rueckklingel_nach_schreib
#print axioms Gabbro.Grammatik.tuerklingel_fenster_geordnet
#print axioms Gabbro.Grammatik.tuerklingel_ohne_wettlauf
#print axioms Gabbro.Grammatik.ggesittet_cpu
#print axioms Gabbro.Grammatik.ggesittet_fenster
#print axioms Gabbro.Grammatik.ggesittet_fenster_geordnet
#print axioms Gabbro.Grammatik.ggesittet_ohne_wettlauf

end Gabbro.Grammatik

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 12. The CPU-device seam as publish/await pairing -/

/-- The CPU publish half of the seam: the driver hands the DMA-visible buffer
    over (`gibt W` at `k`). The publish names the guard and the handoff index;
    the device write it releases is named only in `SeamPair`. -/
structure SeamPublish (gl : GLauf D) (W : D.Lock) (t : D.Tab) where
  k : Nat
  gibt : ∃ f, gl[k]? = some (GSchritt.cpu ⟨f, .gibt W⟩)
  sichtbar : DmaSichtbar t

/-- The CPU await half of the seam: the driver takes the buffer back
    (`nimmt W` at `m`). The await names the guard and the take-back index;
    which device write it follows is named only in `SeamPair`. -/
structure SeamAwait (gl : GLauf D) (W : D.Lock) (t : D.Tab) where
  m : Nat
  nimmt : ∃ f h, gl[m]? = some (GSchritt.cpu ⟨f, .nimmt W h⟩)

/-- Publish/await pairing across the seam: one publish, one device write, one
    await, in that order. The pair is the transfer discipline around the named
    content assumption `dma_inhalt`: order is proved below (`seam_pair_ordered`,
    `seam_pair_race_free`), content is assumed per write (`seam_handoff`). -/
structure SeamPair (gl : GLauf D) (W : D.Lock) (t : D.Tab) where
  pub : SeamPublish gl W t
  aw : SeamAwait gl W t
  j : Nat
  schreibt : gl[j]? = some (GSchritt.dma t)
  vor : pub.k < j
  nach : j < aw.m

/-- Every publish/await pair is a guarded window: the bridge into §4. -/
theorem SeamPair.wache (p : SeamPair gl W t) : GeraetWache gl W t p.pub.k p.aw.m p.j :=
  { sichtbar := p.pub.sichtbar
    gibt := p.pub.gibt
    schreibt := p.schreibt
    nimmt := p.aw.nimmt
    vor := p.vor
    nach := p.nach }

/-- **The pair preserves order across the seam.** The publish precedes the
    await through the device write -- the handoff edge and the take-back edge,
    closed by transitivity. -/
theorem seam_pair_ordered (p : SeamPair gl W t) : GHB gl p.pub.k p.aw.m := by
  obtain ⟨f1, hk⟩ := p.pub.gibt
  obtain ⟨f2, h, hm⟩ := p.aw.nimmt
  exact GHB.trans _ _ _ (GHB.devVor W f1 p.pub.k p.j t hk p.schreibt p.vor)
    (GHB.devNach W f2 h p.j p.aw.m t p.schreibt hm p.nach)

/-- **The pair preserves race-freedom across the seam.** A CPU access ordered
    against the pair endpoints (publish, await) is ordered against the device
    write between them. The endpoint half stays the driver's obligation
    (`haussen`); this theorem connects it to the write, nothing more. -/
theorem seam_pair_race_free (p : SeamPair gl W t) (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx p.pub.k ∨ GHB gl p.aw.m hz.idx) :
    GHB gl hz.idx p.j ∨ GHB gl p.j hz.idx :=
  geraet_ohne_wettlauf gl W t p.pub.k p.aw.m p.j p.wache hz haussen

/-- Ordering proved, content assumed -- at the seam pair. `dma_inhalt` stays
    the NAMED hardware assumption: events carry no values, so the content the
    device observes at `(gl, t, p.j)` is taken as a hypothesis, never derived. -/
theorem seam_handoff (p : SeamPair gl W t) (hz : CpuZugriff gl t)
    (haussen : GHB gl hz.idx p.pub.k ∨ GHB gl p.aw.m hz.idx)
    (hinhalt : dma_inhalt D gl t p.j) :
    (GHB gl hz.idx p.j ∨ GHB gl p.j hz.idx) ∧ dma_inhalt D gl t p.j :=
  ⟨seam_pair_race_free p hz haussen, hinhalt⟩

#print axioms Gabbro.Grammatik.seam_pair_ordered
#print axioms Gabbro.Grammatik.seam_pair_race_free
#print axioms Gabbro.Grammatik.seam_handoff

end Gabbro.Grammatik

