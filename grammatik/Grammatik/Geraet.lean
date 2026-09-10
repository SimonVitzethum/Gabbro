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

    (C1) One window per device write: a single handoff/take-back pair `(k, m)`
         around one write `j`. Chaining several device writes needs the windows
         linked explicitly; that induction is not here.
    (C2) The CPU-side ordering `haussen` is a premise, discharged per driver
         (cf. `geordnet_durch_sperre`). This file proves the device connection.
    (C3) The guard is a lock give/take. A doorbell handoff through a REGISTER
         has no event -- registers are outside the world -- so mapping a real
         doorbell onto `gibt`/`nimmt` is a driver-side argument, not a theorem.
    (C4) No full-run interleaving with device steps: `GLauf` carries the steps,
         but there is no `Gesittet` over `GLauf` yet (W3-W5 speak CPU only).
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

#print axioms Gabbro.Grammatik.geraet_ohne_sperre
#print axioms Gabbro.Grammatik.geraet_ohne_wettlauf
#print axioms Gabbro.Grammatik.dma_uebergabe

end Gabbro.Grammatik
