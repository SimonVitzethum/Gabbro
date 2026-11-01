module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
public import Grammatik.Kern.Semantik.Geraet.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

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
