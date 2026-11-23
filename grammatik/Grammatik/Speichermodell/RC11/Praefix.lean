/-
  File:      Grammatik/Speichermodell/RC11/Praefix.lean
  Subject:   THE IN-ORDER READING of the memory model W: consistency survives restriction to any set
             of events (`einschraenken_konsistent`), and since `po ∪ rf` is acyclic every consistent
             graph is executed event by event in ONE order that respects program order and in which
             every read comes after the write it reads, each prefix consistent
             (`ausfuehrung_in_ordnung`). This is why W needs no promises: without load buffering
             the axiomatic model is an in-order machine whose step adds one event to a consistent
             prefix.
-/
module

public import Grammatik.Speichermodell.RC11.SCOrdnung

@[expose] public section

namespace Gabbro.Grammatik.Speichermodell.RC11

namespace Graph

variable {E Ort Wert : Type}

/-- **The restriction of a graph** to the events satisfying `P`. -/
def einschraenken (G : Graph E Ort Wert) (P : E → Prop) : Graph {e // P e} Ort Wert where
  lab a := G.lab a.1
  po a b := G.po a.1 b.1
  rf a b := G.rf a.1 b.1
  mo a b := G.mo a.1 b.1

variable {G : Graph E Ort Wert} {P : E → Prop}

theorem einschraenken_wf (hw : G.Wohlgeformt) : (G.einschraenken P).Wohlgeformt where
  po_trans := fun a b c h1 h2 => hw.po_trans a.1 b.1 c.1 h1 h2
  po_irrefl := fun a h => hw.po_irrefl a.1 h
  rf_schreibt := fun w r h => hw.rf_schreibt w.1 r.1 h
  rf_liest := fun w r h => hw.rf_liest w.1 r.1 h
  rf_ort := fun w r h => hw.rf_ort w.1 r.1 h
  rf_wert := fun w r h => hw.rf_wert w.1 r.1 h
  rf_eindeutig := fun w w' r h1 h2 => Subtype.ext (hw.rf_eindeutig w.1 w'.1 r.1 h1 h2)
  mo_schreibt := fun a b h => hw.mo_schreibt a.1 b.1 h
  mo_ort := fun a b h => hw.mo_ort a.1 b.1 h
  mo_trans := fun a b c h1 h2 => hw.mo_trans a.1 b.1 c.1 h1 h2
  mo_irrefl := fun a h => hw.mo_irrefl a.1 h
  mo_total := fun a b ha hb ho hne =>
    hw.mo_total a.1 b.1 ha hb ho (fun e => hne (Subtype.ext e))

theorem einschraenken_rs {a b : {e // P e}} (h : (G.einschraenken P).Rs a b) : G.Rs a.1 b.1 := by
  induction h with
  | selbst hs => exact .selbst hs
  | po h1 h2 h3 h4 h5 => exact .po h1 h2 h3 h4 h5
  | rmw _ h2 h3 ih => exact .rmw ih h2 h3

theorem einschraenken_sw {a b : {e // P e}} (h : (G.einschraenken P).sw a b) : G.sw a.1 b.1 := by
  obtain ⟨h1, h2, h3, h4, x, hrs, hrf⟩ := h
  exact ⟨h1, h2, h3, h4, x.1, einschraenken_rs hrs, hrf⟩

theorem einschraenken_hb {a b : {e // P e}} (h : (G.einschraenken P).hb a b) : G.hb a.1 b.1 := by
  refine transGen_abbild Subtype.val (fun x y hxy => ?_) h
  rcases hxy with hpo | hsw
  · exact Or.inl hpo
  · exact Or.inr (einschraenken_sw hsw)

theorem einschraenken_rb {a b : {e // P e}} (h : (G.einschraenken P).rb a b) : G.rb a.1 b.1 := by
  obtain ⟨w, hrf, hmo, hne⟩ := h
  exact ⟨w.1, hrf, hmo, fun e => hne (Subtype.ext e)⟩

theorem einschraenken_eco {a b : {e // P e}} (h : (G.einschraenken P).eco a b) :
    G.eco a.1 b.1 := by
  refine transGen_abbild Subtype.val (fun x y hxy => ?_) h
  rcases hxy with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (einschraenken_rb h1))

theorem einschraenken_psc {a b : {e // P e}} (h : (G.einschraenken P).psc a b) :
    G.psc a.1 b.1 := by
  obtain ⟨ha, hb, h⟩ := h
  refine ⟨ha, hb, ?_⟩
  rcases h with h | ⟨c, d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c.1, d.1, h1, h2, einschraenken_hb h3, h4, h5⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨einschraenken_hb h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (einschraenken_rb h))))

/-- **Consistency survives restriction** to any set of events. -/
theorem einschraenken_konsistent (hk : G.Konsistent) (P : E → Prop) :
    (G.einschraenken P).Konsistent where
  wf := einschraenken_wf hk.wf
  hb_irrefl := fun a h => hk.hb_irrefl a.1 (einschraenken_hb h)
  kohaerent := fun a b h1 h2 => hk.kohaerent a.1 b.1 (einschraenken_hb h1) (einschraenken_eco h2)
  atomar := fun w u w' h1 h2 h3 => hk.atomar w.1 u.1 w'.1 h1 h2 h3
  psc := azyklisch_abbild Subtype.val (fun _ _ h => einschraenken_psc h) hk.psc
  ohneLB := azyklisch_abbild Subtype.val (fun _ _ h => h) hk.ohneLB

/-- **In-order execution.** A consistent graph is executed in ONE strict total order `T` of its
    events that extends program order and in which every read comes after the write it reads;
    the events before any event form a consistent graph. So W's runs are produced by an in-order
    machine whose step appends one event to a consistent prefix -- no promises, no load
    buffering. -/
theorem ausfuehrung_in_ordnung (hk : G.Konsistent) :
    ∃ T : E → E → Prop, (∀ a b c, T a b → T b c → T a c) ∧ (∀ a, ¬ T a a) ∧
      (∀ a b, a ≠ b → T a b ∨ T b a) ∧ (∀ a b, G.po a b → T a b) ∧
      (∀ a b, G.rf a b → T a b) ∧ ∀ x, (G.einschraenken (fun e => T e x)).Konsistent := by
  obtain ⟨T, htr, hirr, htot, hext⟩ := lineare_erweiterung hk.ohneLB
  exact ⟨T, htr, hirr, htot, fun a b h => hext a b (Or.inl h), fun a b h => hext a b (Or.inr h),
    fun x => einschraenken_konsistent hk _⟩

end Graph

end Gabbro.Grammatik.Speichermodell.RC11
