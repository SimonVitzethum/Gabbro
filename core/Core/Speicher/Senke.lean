/-
  File:      core/Core/Speicher/Senke.lean
  Subject:   A SINK keeps consistency (`senke_konsistent`): if no program-order, reads-from,
             modification-order or reads-before edge leaves the event `e`, and `e`, if it is an
             update, has no write between its source and itself and its source precedes it in
             `mo`, then the graph is consistent as soon as it is well formed and the graph
             without `e` is consistent. Every relation path that ends elsewhere avoids `e`
             (`pfad_ohne`), so the axioms over the other events are those of the smaller graph.
             This is the step a machine of M4 takes when it appends an event that reads the last
             write of its location in `mo` and writes at the end of `mo` (the non-vacuity of its
             memory).
-/
module

public import Core.Speicher.Kohaerenz

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type}

/-- A path that does not end at a node without outgoing edges never visits it. -/
theorem pfad_ohne {r : E → E → Prop} {e : E} (he : ∀ x, ¬ r e x) {a b : E}
    (h : Relation.TransGen r a b) (hb : b ≠ e) :
    a ≠ e ∧ ∀ ha : a ≠ e,
      Relation.TransGen (fun x y : {x // x ≠ e} => r x.1 y.1) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | single hab =>
    refine ⟨fun h0 => he _ (h0 ▸ hab), fun ha => .single hab⟩
  | @tail c b' h1 hcb ih =>
    have hce : c ≠ e := fun h0 => he _ (h0 ▸ hcb)
    obtain ⟨ha, hp⟩ := ih hce
    exact ⟨ha, fun ha' => .tail (hp ha') hcb⟩

/-- **`e` is a sink**: no `po`, `rf`, `mo` or `rb` edge leaves it. -/
structure Senke (G : Graph E Ort Wert) (e : E) : Prop where
  po : ∀ x, ¬ G.po e x
  rf : ∀ x, ¬ G.rf e x
  mo : ∀ x, ¬ G.mo e x
  rb : ∀ x, ¬ G.rb e x

namespace Senke

variable {G : Graph E Ort Wert} {e : E}

theorem rs (hs : G.Senke e) {y : E} (h : G.Rs e y) : y = e := by
  induction h with
  | selbst _ _ => rfl
  | po _ h2 _ _ _ => exact absurd h2 (hs.po _)
  | rmw _ h2 _ ih =>
    rw [ih] at h2
    exact absurd h2 (hs.rf _)

theorem hbSchritt (hs : G.Senke e) (x : E) : ¬ G.hbSchritt e x := by
  rintro (h | ⟨w, y, r, hkopf, hy, hrf, _, _, _⟩)
  · exact hs.po _ h
  · rcases hkopf with ⟨rfl, _, _⟩ | ⟨_, hpo, _⟩
    · rw [hs.rs hy] at hrf
      exact hs.rf _ hrf
    · exact hs.po _ hpo

theorem hb (hs : G.Senke e) (x : E) : ¬ G.hb e x := fun h => by
  obtain ⟨c, hc⟩ := transGen_kopf h
  exact hs.hbSchritt _ hc

theorem ecoSchritt (hs : G.Senke e) (x : E) : ¬ G.ecoSchritt e x := by
  rintro (h | h | h)
  · exact hs.rf _ h
  · exact hs.mo _ h
  · exact hs.rb _ h

theorem scb_ohne (hs : G.Senke e) {d : E} (h : G.scb e d) : False := by
  rcases h with hpo | ⟨_, _, hpo, _, _, _, _⟩ | ⟨hhb, _⟩ | hmo | hrb
  · exact hs.po _ hpo
  · exact hs.po _ hpo
  · exact hs.hb _ hhb
  · exact hs.mo _ hmo
  · exact hs.rb _ hrb

theorem psc (hs : G.Senke e) (x : E) : ¬ G.psc e x := by
  rintro (⟨c, d, hscb, hl, _⟩ | ⟨_, _, hhb | ⟨c, _, h1, _, _⟩⟩)
  · rcases hl with ⟨_, rfl⟩ | ⟨_, hcc⟩
    · exact hs.scb_ohne hscb
    · rcases hcc with rfl | hhb
      · exact hs.scb_ohne hscb
      · exact hs.hb _ hhb
  · exact hs.hb _ hhb
  · exact hs.hb _ h1

theorem porf (hs : G.Senke e) (x : E) : ¬ G.porf e x := by
  rintro (h | h)
  · exact hs.po _ h
  · exact hs.rf _ h

/-! ### The relations away from the sink are those of the graph without it -/

/-- The graph without `e`. -/
abbrev ohne (G : Graph E Ort Wert) (e : E) : Graph {x // x ≠ e} Ort Wert :=
  G.einschraenken (· ≠ e)

theorem rs_ohne (hs : G.Senke e) {x z : E} (h : G.Rs x z) :
    ∀ (hx : x ≠ e) (hz : z ≠ e), (ohne G e).Rs ⟨x, hx⟩ ⟨z, hz⟩ := by
  induction h with
  | selbst h1 h2 => exact fun _ _ => .selbst h1 h2
  | po h1 h2 h3 h4 h5 => exact fun _ _ => .po h1 h2 h3 h4 h5
  | @rmw x' u _ h2 h3 ih =>
    intro hw hu
    have hx' : x' ≠ e := fun h0 => hs.rf _ (h0 ▸ h2)
    exact .rmw (ih hw hx') h2 h3

/-- A synchronisation whose ends avoid the sink avoids it throughout. -/
theorem sw_ohne (hs : G.Senke e) {a b : E} (h : G.sw a b) (ha : a ≠ e) (hb : b ≠ e) :
    (ohne G e).sw ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨w, x, r, hkopf, hrs, hrf, hatom, hliest, hschwanz⟩ := h
  have hwe : w ≠ e := by
    intro h0
    rcases hkopf with ⟨haw, _, _⟩ | ⟨_, hpo, _⟩
    · exact ha (haw.trans h0)
    · have hxe : x = e := hs.rs (h0 ▸ hrs)
      exact hs.rf _ (hxe ▸ hrf)
  have hxe : x ≠ e := fun h0 => hs.rf _ (h0 ▸ hrf)
  have hre : r ≠ e := by
    intro h0
    rcases hschwanz with ⟨hrb, _, _⟩ | ⟨_, _, hpo, _⟩
    · exact hb (hrb.symm.trans h0)
    · exact hs.po _ (h0 ▸ hpo)
  refine ⟨⟨w, hwe⟩, ⟨x, hxe⟩, ⟨r, hre⟩, ?_, hs.rs_ohne hrs hwe hxe, hrf, hatom, hliest, ?_⟩
  · rcases hkopf with ⟨haw, hsa, hma⟩ | ⟨hza, hpo, hsw⟩
    · exact Or.inl ⟨Subtype.ext haw, hsa, hma⟩
    · exact Or.inr ⟨hza, hpo, hsw⟩
  · rcases hschwanz with ⟨hrb, hlb, hmb⟩ | ⟨hrl, hat, hpo, hzb⟩
    · exact Or.inl ⟨Subtype.ext hrb, hlb, hmb⟩
    · exact Or.inr ⟨hrl, hat, hpo, hzb⟩

theorem hb_ohne (hs : G.Senke e) {a b : E} (h : G.hb a b) (hb : b ≠ e) :
    ∃ ha : a ≠ e, (ohne G e).hb ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨ha, hp⟩ := pfad_ohne hs.hbSchritt h hb
  refine ⟨ha, transGen_mono (fun x y hxy => ?_) (hp ha)⟩
  rcases hxy with h1 | hsw
  · exact Or.inl h1
  · exact Or.inr (hs.sw_ohne hsw x.2 y.2)

theorem rb_ohne (hs : G.Senke e) {a b : E} (h : G.rb a b) (ha : a ≠ e) (hb : b ≠ e) :
    (ohne G e).rb ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨w, hrf, hmo, hne⟩ := h
  have hw : w ≠ e := fun h0 => hs.rf _ (h0 ▸ hrf)
  exact ⟨⟨w, hw⟩, hrf, hmo, fun h0 => hne (congrArg Subtype.val h0)⟩

theorem eco_ohne (hs : G.Senke e) {a b : E} (h : G.eco a b) (hb : b ≠ e) :
    ∃ ha : a ≠ e, (ohne G e).eco ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨ha, hp⟩ := pfad_ohne hs.ecoSchritt h hb
  refine ⟨ha, transGen_mono (fun x y hxy => ?_) (hp ha)⟩
  rcases hxy with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (hs.rb_ohne h1 x.2 y.2))

theorem scb_ohne_trans (hs : G.Senke e) {c d : E} (h : G.scb c d) (hc : c ≠ e)
    (hd : d ≠ e) : (ohne G e).scb ⟨c, hc⟩ ⟨d, hd⟩ := by
  rcases h with hpo | ⟨x, y, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | h | h
  · exact Or.inl hpo
  · by_cases hxe : x = e
    · exact absurd (hxe ▸ h3) (hs.hb _)
    · by_cases hye : y = e
      · exact absurd (hye ▸ h4) (hs.po _)
      · exact Or.inr
          (Or.inl ⟨⟨x, hxe⟩, ⟨y, hye⟩, h1, h2, (hs.hb_ohne h3 hye).2, h4, h5⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(hs.hb_ohne h1 hd).2, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hs.rb_ohne h hc hd))))

theorem psc_ohne (hs : G.Senke e) {a b : {x // x ≠ e}} (h : G.psc a.1 b.1) :
    (ohne G e).psc a b := by
  rcases h with ⟨c, d, hscb, hl, hr⟩ | ⟨hza, hzb, h⟩
  · have hc : c ≠ e := by
      rcases hl with hl | hr
      · obtain ⟨_, rfl⟩ := hl
        exact a.2
      · obtain ⟨_, hcc⟩ := hr
        rcases hcc with rfl | hhb
        · exact a.2
        · intro h0
          exact hs.scb_ohne (h0 ▸ hscb)
    have hd : d ≠ e := by
      rcases hr with hl | hr
      · obtain ⟨_, hcb⟩ := hl
        exact hcb.symm ▸ b.2
      · obtain ⟨_, hcc⟩ := hr
        rcases hcc with rfl | hhb
        · exact b.2
        · intro h0
          exact hs.hb _ (h0 ▸ hhb)
    refine Or.inl ⟨⟨c, hc⟩, ⟨d, hd⟩, hs.scb_ohne_trans hscb hc hd, ?_, ?_⟩
    · rcases hl with hl | hr
      · obtain ⟨hsc, rfl⟩ := hl
        exact Or.inl ⟨hsc, rfl⟩
      · obtain ⟨hza, hcc⟩ := hr
        refine Or.inr ⟨hza, ?_⟩
        rcases hcc with rfl | hhb
        · exact Or.inl rfl
        · exact Or.inr (hs.hb_ohne hhb hc).2
    · rcases hr with hl | hr
      · obtain ⟨hsc, hcb⟩ := hl
        exact Or.inl ⟨hsc, Subtype.ext hcb⟩
      · obtain ⟨hzb, hcc⟩ := hr
        refine Or.inr ⟨hzb, ?_⟩
        rcases hcc with hcb | hhb
        · exact Or.inl (Subtype.ext hcb)
        · exact Or.inr (hs.hb_ohne hhb b.2).2
  · refine Or.inr ⟨hza, hzb, ?_⟩
    rcases h with hhb | ⟨x, y, h1, h2, h3⟩
    · exact Or.inl (hs.hb_ohne hhb b.2).2
    · have hxe : x ≠ e := by
        intro h0
        obtain ⟨z, hz⟩ := transGen_kopf h2
        exact hs.ecoSchritt _ (h0 ▸ hz)
      have hye : y ≠ e := (hs.hb_ohne h3 b.2).1
      obtain ⟨_, h1'⟩ := hs.hb_ohne h1 hxe
      obtain ⟨_, h2'⟩ := hs.eco_ohne h2 hye
      obtain ⟨_, h3'⟩ := hs.hb_ohne h3 b.2
      exact Or.inr ⟨⟨x, hxe⟩, ⟨y, hye⟩, h1', h2', h3'⟩

end Senke

/-- **A sink keeps consistency.** -/
theorem senke_konsistent {G : Graph E Ort Wert} {e : E} (hs : G.Senke e) (hw : G.Wohlgeformt)
    (hk : (Senke.ohne G e).Konsistent)
    (hat : ∀ w w', G.rf w e → G.istRmw e → G.mo w w' → ¬ G.mo w' e)
    (hvor : ∀ w, G.rf w e → G.istRmw e → G.mo w e) : G.Konsistent where
  wf := hw
  hb_irrefl := fun a h => by
    have hae : a ≠ e := fun h0 => hs.hb _ (h0 ▸ h)
    obtain ⟨_, h'⟩ := hs.hb_ohne h hae
    exact hk.hb_irrefl _ h'
  kohaerent := fun a b hab hba => by
    have hae : a ≠ e := fun h0 => hs.hb _ (h0 ▸ hab)
    have hbe : b ≠ e := by
      intro h0
      obtain ⟨c, hc⟩ := transGen_kopf hba
      exact hs.ecoSchritt _ (h0 ▸ hc)
    obtain ⟨_, hab'⟩ := hs.hb_ohne hab hbe
    obtain ⟨_, hba'⟩ := hs.eco_ohne hba hae
    exact hk.kohaerent _ _ hab' hba'
  atomar := fun w u w' h1 h2 h3 h4 => by
    by_cases hu : u = e
    · rw [hu] at h1 h2 h4
      exact hat w w' h1 h2 h3 h4
    · have hwe : w ≠ e := fun h0 => hs.rf _ (h0 ▸ h1)
      have hw'e : w' ≠ e := fun h0 => hs.mo _ (h0 ▸ h4)
      exact hk.atomar ⟨w, hwe⟩ ⟨u, hu⟩ ⟨w', hw'e⟩ h1 h2 h3 h4
  psc := fun a h => by
    have hae : a ≠ e := by
      intro h0
      obtain ⟨c, hc⟩ := transGen_kopf h
      exact hs.psc _ (h0 ▸ hc)
    obtain ⟨_, hp⟩ := pfad_ohne hs.psc h hae
    exact hk.psc ⟨a, hae⟩ (transGen_mono (fun x y hxy => hs.psc_ohne hxy) (hp hae))
  ohneLB := fun a h => by
    have hae : a ≠ e := by
      intro h0
      obtain ⟨c, hc⟩ := transGen_kopf h
      exact hs.porf _ (h0 ▸ hc)
    obtain ⟨_, hp⟩ := pfad_ohne hs.porf h hae
    exact hk.ohneLB ⟨a, hae⟩ (hp hae)
  liest_vorher := fun w u h1 h2 => by
    by_cases hu : u = e
    · rw [hu] at h1 h2 ⊢
      by_cases hw : w = e
      · rw [hw] at h1
        exact absurd h1 (hs.rf _)
      · exact hvor w h1 h2
    · have hwe : w ≠ e := fun h0 => hs.rf _ (h0 ▸ h1)
      exact hk.liest_vorher ⟨w, hwe⟩ ⟨u, hu⟩ h1 h2

end Graph

end Gabbro.Core.Speicher
