module

public import Grammatik.Niedrig.Authority.Preservation

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

variable {D : Deklaration}

/-- Realization is a software/layout obligation in addition to LayoutOk:
    LayoutOk alone cannot place a fixed numeric span in every arbitrary layout.
    An OPEN carrier still gets only this finite authorized reservation. -/
def Span.Realizes (span : Span D) (layout : AdressLayout D) : Prop :=
  span.space.backing = layout.raum span.table ∧
  layout.basis span.table ≤ span.base ∧
  (D.offen span.table = true ∨ span.base + span.length ≤
    layout.basis span.table + (D.count span.table).toNat * layout.breite span.table)

def Authority.Realizes (a : Authority D) (layout : AdressLayout D) : Prop :=
  ∀ span ∈ a.spans, span.Realizes layout

/-- Every byte of an issued view lies in its existing layout carrier, for every
    correct layout realizing the declared authority. It also realizes the
    declared nominal space, rather than inventing separation from its name. -/
theorem ram_view_in_layout {P I : Type} {a : Authority D} {c : Context D P I}
    (r : ViewResult a c) (layout : AdressLayout D)
    (correct : LayoutOk layout) (realizes : a.Realizes layout)
    {byte : Adresse} (inside : r.view.Contains byte) :
    layout.inTabelle r.view.span.table byte ∧
    layout.nominal byte.1 = D.tableSpace r.view.span.table := by
  have hs := realizes r.view.span r.admission.span
  have hb := ram_view_inside_span r inside
  have low : r.view.span.base ≤ byte.2 := hb.2.1
  have high : byte.2 < r.view.span.base + r.view.span.length := hb.2.2
  have hspace := hb.1.trans hs.1
  have hin : layout.inTabelle r.view.span.table byte := by
    refine ⟨hspace, ?_, ?_⟩
    · have hlo := hs.2.1
      omega
    · rcases hs.2.2 with hopen | hend
      · exact .inl hopen
      · right
        omega
  exact ⟨hin, (congrArg layout.nominal hspace).trans (correct.tabellenRaum r.view.span.table).2⟩

/-- A write uses the EXISTING typed carrier store. Its proof receipt requires
    the complete cell extent inside a live, currently accessible writable view.
    This does not add a G statement or bypass its lock/effect rules. L3 must
    connect representation and source reference introduction to this boundary. -/
structure ViewWrite {P I : Type} (a : Authority D) (c : Context D P I)
    (layout : AdressLayout D) (before after : World D) where
  view : View D
  live : view ∈ c.views
  active : c.frame = view.borrower
  valid : c.Valid a
  writable : view.rights.write = true
  index : Int
  field : D.Feld view.span.table
  extent : ImBereich D view.span.table index
  bytes : ∀ byte, layout.inZelle view.span.table index field byte → view.Contains byte
  value : Wert D (D.typ view.span.table field)
  store : after = before.storeSlot view.span.table index field value

/-- A witnessed typed write uses only bytes in the live region and its carrier. -/
theorem view_write_confined {P I : Type} {a : Authority D} {c : Context D P I}
    {layout : AdressLayout D} {before after : World D}
    (correct : LayoutOk layout) (write : ViewWrite a c layout before after)
    {byte : Adresse} (cell : layout.inZelle write.view.span.table write.index write.field byte) :
    write.view.Contains byte ∧ layout.inTabelle write.view.span.table byte :=
  ⟨write.bytes byte cell,
    zelle_im_bereich (D := D) (lay := layout) correct write.extent write.field cell⟩

end Gabbro.Grammatik.LowLevel
