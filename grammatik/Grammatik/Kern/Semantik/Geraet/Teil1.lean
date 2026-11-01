module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf

@[expose] public section



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
      | .fremd _ => []
  | .dma _ => []

/-- **The device takes no locks.** By construction: the `dma` branch has no
    lock list to fill. -/
theorem geraet_ohne_sperre (t : D.Tab) :
    (GSchritt.dma (D := D) t).sperren = [] :=
  by rfl

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
end Gabbro.Grammatik
