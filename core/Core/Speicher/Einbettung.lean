/-
  File:      core/Core/Speicher/Einbettung.lean
  Subject:   EMBEDDINGS of execution graphs: an injective map that carries the labels and reflects
             `po`, `rf` and `mo` carries consistency back (`Einbettung.konsistent`) -- the restriction
             of `Praefix.lean` is one instance (`einschraenken_einbettung`), a renaming of the events
             is another. And COMPLETENESS of a graph (`Vollstaendig`): every read has a source, so no
             read returns a value from nowhere (PERFECT-MODEL §3.4: no garbage values).
-/
module

public import Core.Speicher.Praefix

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E F Ort Wert : Type}

/-- **Every read has a source** in reads-from. `Konsistent` alone allows a read without a writer
    (its value is then unconstrained); the graph machine (`Graphmaschine.lean`) keeps every
    state complete. -/
def Vollstaendig (G : Graph E Ort Wert) : Prop := ∀ r, G.liest r → ∃ w, G.rf w r

/-- **An embedding of execution graphs** `H ↪ G` along `g`: injective, label-preserving, and
    `po`, `rf`, `mo` of `H` are exactly those of `G` between the images. -/
structure Einbettung (H : Graph F Ort Wert) (G : Graph E Ort Wert) (g : F → E) : Prop where
  inj : ∀ a b, g a = g b → a = b
  lab : ∀ a, H.lab a = G.lab (g a)
  po : ∀ a b, H.po a b ↔ G.po (g a) (g b)
  rf : ∀ a b, H.rf a b ↔ G.rf (g a) (g b)
  mo : ∀ a b, H.mo a b ↔ G.mo (g a) (g b)

/-- The restriction to a set of events is an embedding (along the inclusion). -/
theorem einschraenken_einbettung (G : Graph E Ort Wert) (P : E → Prop) :
    Einbettung (G.einschraenken P) G Subtype.val where
  inj := fun _ _ h => Subtype.ext h
  lab := fun _ => rfl
  po := fun _ _ => Iff.rfl
  rf := fun _ _ => Iff.rfl
  mo := fun _ _ => Iff.rfl

namespace Einbettung

variable {H : Graph F Ort Wert} {G : Graph E Ort Wert} {g : F → E}

theorem ort (h : Einbettung H G g) (a : F) : H.ort a = G.ort (g a) := by
  unfold Graph.ort
  rw [h.lab]

theorem modus (h : Einbettung H G g) (a : F) : H.modus a = G.modus (g a) := by
  unfold Graph.modus
  rw [h.lab]

theorem liest (h : Einbettung H G g) (a : F) : H.liest a ↔ G.liest (g a) := by
  unfold Graph.liest
  rw [h.lab]

theorem schreibt (h : Einbettung H G g) (a : F) : H.schreibt a ↔ G.schreibt (g a) := by
  unfold Graph.schreibt
  rw [h.lab]

theorem istRmw (h : Einbettung H G g) (a : F) : H.istRmw a ↔ G.istRmw (g a) := by
  unfold Graph.istRmw
  rw [h.lab]

theorem istZaun (h : Einbettung H G g) (a : F) : H.istZaun a ↔ G.istZaun (g a) := by
  unfold Graph.istZaun
  rw [h.lab]

theorem istSyncZaun (h : Einbettung H G g) (a : F) :
    H.istSyncZaun a ↔ G.istSyncZaun (g a) := by
  unfold Graph.istSyncZaun
  rw [h.istZaun a, h.modus a]

theorem istSCZaun (h : Einbettung H G g) (a : F) :
    H.istSCZaun a ↔ G.istSCZaun (g a) := by
  unfold Graph.istSCZaun
  rw [h.istZaun a, h.modus a]

/-- The shape survives an embedding. -/
theorem wf (h : Einbettung H G g) (hw : G.Wohlgeformt) : H.Wohlgeformt where
  po_trans := fun a b c h1 h2 =>
    (h.po a c).2 (hw.po_trans _ _ _ ((h.po a b).1 h1) ((h.po b c).1 h2))
  po_irrefl := fun a h1 => hw.po_irrefl _ ((h.po a a).1 h1)
  rf_schreibt := fun w r h1 => (h.schreibt w).2 (hw.rf_schreibt _ _ ((h.rf w r).1 h1))
  rf_liest := fun w r h1 => (h.liest r).2 (hw.rf_liest _ _ ((h.rf w r).1 h1))
  rf_ort := fun w r h1 => by
    rw [h.ort, h.ort]
    exact hw.rf_ort _ _ ((h.rf w r).1 h1)
  rf_wert := fun w r h1 => by
    rw [h.lab, h.lab]
    exact hw.rf_wert _ _ ((h.rf w r).1 h1)
  rf_eindeutig := fun w w' r h1 h2 =>
    h.inj _ _ (hw.rf_eindeutig _ _ _ ((h.rf w r).1 h1) ((h.rf w' r).1 h2))
  mo_schreibt := fun a b h1 => by
    obtain ⟨x, y⟩ := hw.mo_schreibt _ _ ((h.mo a b).1 h1)
    exact ⟨(h.schreibt a).2 x, (h.schreibt b).2 y⟩
  mo_ort := fun a b h1 => by
    rw [h.ort, h.ort]
    exact hw.mo_ort _ _ ((h.mo a b).1 h1)
  mo_trans := fun a b c h1 h2 =>
    (h.mo a c).2 (hw.mo_trans _ _ _ ((h.mo a b).1 h1) ((h.mo b c).1 h2))
  mo_irrefl := fun a h1 => hw.mo_irrefl _ ((h.mo a a).1 h1)
  mo_total := fun a b ha hb ho hne => by
    rw [h.ort, h.ort] at ho
    rcases hw.mo_total _ _ ((h.schreibt a).1 ha) ((h.schreibt b).1 hb) ho
        (fun e => hne (h.inj _ _ e)) with m | m
    · exact Or.inl ((h.mo a b).2 m)
    · exact Or.inr ((h.mo b a).2 m)
  rmw_nicht_na := fun a ha hna => by
    have hna' : G.modus (g a) = .na := by
      rw [← h.modus a]
      exact hna
    exact (hw.rmw_nicht_na (g a) ((h.istRmw a).1 ha)) hna'

theorem rs (h : Einbettung H G g) {a b : F} (hr : H.Rs a b) : G.Rs (g a) (g b) := by
  induction hr with
  | selbst hs hat => exact .selbst ((h.schreibt _).1 hs) (h.modus _ ▸ hat)
  | po h1 h2 h3 h4 h5 =>
    rw [h.ort, h.ort] at h4
    rw [h.modus] at h5
    exact .po ((h.schreibt _).1 h1) ((h.po _ _).1 h2) ((h.schreibt _).1 h3) h4 h5
  | rmw _ h2 h3 ih => exact .rmw ih ((h.rf _ _).1 h2) ((h.istRmw _).1 h3)

theorem sw (h : Einbettung H G g) {a b : F} (hs : H.sw a b) : G.sw (g a) (g b) := by
  obtain ⟨w, x, r, hkopf, hrs, hrf, hatom, hliest, hschwanz⟩ := hs
  have hatom' : (G.modus (g r)).atomar := by
    rw [← h.modus r]
    exact hatom
  have hkopf' : G.FreigabeKopf (g a) (g w) := by
    unfold Graph.FreigabeKopf at hkopf ⊢
    rcases hkopf with ⟨rfl, hsa, hma⟩ | ⟨hza, hpo, hsw⟩
    · exact Or.inl ⟨rfl, (h.schreibt _).1 hsa, h.modus _ ▸ hma⟩
    · exact Or.inr ⟨(h.istSyncZaun _).1 hza, (h.po _ _).1 hpo, (h.schreibt _).1 hsw⟩
  have hschwanz' : G.ErwerbSchwanz (g r) (g b) := by
    unfold Graph.ErwerbSchwanz at hschwanz ⊢
    rcases hschwanz with ⟨rfl, hlb, hmb⟩ | ⟨hrl, hat, hpo, hzb⟩
    · exact Or.inl ⟨rfl, (h.liest _).1 hlb, h.modus _ ▸ hmb⟩
    · exact Or.inr ⟨(h.liest _).1 hrl, h.modus _ ▸ hat, (h.po _ _).1 hpo,
        (h.istSyncZaun _).1 hzb⟩
  unfold Graph.sw
  exact ⟨g w, g x, g r, hkopf', h.rs hrs, (h.rf _ _).1 hrf, hatom', (h.liest r).1 hliest,
    hschwanz'⟩

theorem hb (h : Einbettung H G g) {a b : F} (hh : H.hb a b) : G.hb (g a) (g b) := by
  refine transGen_abbild g (fun x y hxy => ?_) hh
  rcases hxy with hpo | hsw
  · exact Or.inl ((h.po _ _).1 hpo)
  · exact Or.inr (h.sw hsw)

theorem rb (h : Einbettung H G g) {a b : F} (hr : H.rb a b) : G.rb (g a) (g b) := by
  obtain ⟨w, hrf, hmo, hne⟩ := hr
  exact ⟨g w, (h.rf _ _).1 hrf, (h.mo _ _).1 hmo, fun e => hne (h.inj _ _ e)⟩

theorem eco (h : Einbettung H G g) {a b : F} (he : H.eco a b) : G.eco (g a) (g b) := by
  refine transGen_abbild g (fun x y hxy => ?_) he
  rcases hxy with h1 | h1 | h1
  · exact Or.inl ((h.rf _ _).1 h1)
  · exact Or.inr (Or.inl ((h.mo _ _).1 h1))
  · exact Or.inr (Or.inr (h.rb h1))

theorem sc (h : Einbettung H G g) (a : F) : H.sc a ↔ G.sc (g a) := by
  unfold Graph.sc
  rw [h.modus]

theorem scb (h : Einbettung H G g) {a b : F} (hs : H.scb a b) : G.scb (g a) (g b) := by
  rcases hs with hpo | ⟨c, d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | hs | hs
  · exact Or.inl ((h.po _ _).1 hpo)
  · rw [h.ort, h.ort] at h2 h5
    exact Or.inr (Or.inl ⟨g c, g d, (h.po _ _).1 h1, h2, h.hb h3, (h.po _ _).1 h4, h5⟩)
  · rw [h.ort, h.ort] at h2
    exact Or.inr (Or.inr (Or.inl ⟨h.hb h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ((h.mo _ _).1 hs))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h.rb hs))))

theorem psc (h : Einbettung H G g) {a b : F} (hp : H.psc a b) : G.psc (g a) (g b) := by
  rcases hp with ⟨c, d, hscb, hl, hr⟩ | ⟨hza, hzb, hz⟩
  · refine Or.inl ⟨g c, g d, h.scb hscb, ?_, ?_⟩
    · rcases hl with hl | hr
      · obtain ⟨hsc, rfl⟩ := hl
        exact Or.inl ⟨(h.sc a).1 hsc, rfl⟩
      · obtain ⟨hza, hcc⟩ := hr
        refine Or.inr ⟨(h.istSCZaun _).1 hza, ?_⟩
        rcases hcc with rfl | hhb
        · exact Or.inl rfl
        · exact Or.inr (h.hb hhb)
    · rcases hr with hl | hr
      · obtain ⟨hsc, hcb⟩ := hl
        exact Or.inl ⟨(h.sc b).1 hsc, congrArg g hcb⟩
      · obtain ⟨hzb, hcc⟩ := hr
        refine Or.inr ⟨(h.istSCZaun _).1 hzb, ?_⟩
        rcases hcc with hcb | hhb
        · exact Or.inl (congrArg g hcb)
        · exact Or.inr (h.hb hhb)
  · refine Or.inr ⟨(h.istSCZaun _).1 hza, (h.istSCZaun _).1 hzb, ?_⟩
    rcases hz with hhb | ⟨c, d, h1, h2, h3⟩
    · exact Or.inl (h.hb hhb)
    · exact Or.inr ⟨g c, g d, h.hb h1, h.eco h2, h.hb h3⟩

theorem porf (h : Einbettung H G g) {a b : F} (hp : H.porf a b) : G.porf (g a) (g b) := by
  rcases hp with hp | hp
  · exact Or.inl ((h.po _ _).1 hp)
  · exact Or.inr ((h.rf _ _).1 hp)

/-- **Consistency is carried back along an embedding.** -/
theorem konsistent (h : Einbettung H G g) (hk : G.Konsistent) : H.Konsistent where
  wf := h.wf hk.wf
  hb_irrefl := fun _ ha => hk.hb_irrefl _ (h.hb ha)
  kohaerent := fun _ _ h1 h2 => hk.kohaerent _ _ (h.hb h1) (h.eco h2)
  atomar := fun _ _ _ h1 h2 h3 h4 =>
    hk.atomar _ _ _ ((h.rf _ _).1 h1) ((h.istRmw _).1 h2) ((h.mo _ _).1 h3) ((h.mo _ _).1 h4)
  psc := azyklisch_abbild g (fun _ _ hp => h.psc hp) hk.psc
  ohneLB := azyklisch_abbild g (fun _ _ hp => h.porf hp) hk.ohneLB
  liest_vorher := fun _ _ h1 h2 =>
    (h.mo _ _).2 (hk.liest_vorher _ _ ((h.rf _ _).1 h1) ((h.istRmw _).1 h2))

/-- **Completeness is carried back along a surjective embedding.** -/
theorem vollstaendig (h : Einbettung H G g) (hs : ∀ x, ∃ a, g a = x) (hv : G.Vollstaendig) :
    H.Vollstaendig := by
  intro r hr
  obtain ⟨w, hw⟩ := hv _ ((h.liest r).1 hr)
  obtain ⟨a, rfl⟩ := hs w
  exact ⟨a, (h.rf _ _).2 hw⟩

end Einbettung

end Graph

end Gabbro.Core.Speicher
