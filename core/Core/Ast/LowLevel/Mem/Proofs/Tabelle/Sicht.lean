module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Sicht

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # The table view of the memory model

`MmuSicht.tables` is the MMU's table function: space and page to the installed entry.
`MemFrame.tabellenSicht` reads that function out of the frame: it is exactly the mapping of every
address space (`Adressraum.abbildung`), with no entry anywhere else. Together with the cache view
(`TranslationCache.sicht`) it is the view the MMU translates over (`MemFrame.mmuSicht`).
The table invariant (`TabellenGedeckt`) speaks about the same entries. -/

/-- The MMU table function of the frame: the installed entry of a space and a page, if any. -/
def MemFrame.tabellenSicht (frame : MemFrame) (space page : Nat) : Option Seiteneintrag :=
  match frame.spaces[space]? with
  | none => none
  | some addr => addr.abbildung page

/-- The full MMU view of the frame: installed tables plus cached translations. -/
def MemFrame.mmuSicht (frame : MemFrame) : MmuSicht :=
  { tables := frame.tabellenSicht, tlb := frame.tlb.sicht }

/-- On an existing space the table view is the mapping of that space. -/
theorem MemFrame.tabellenSicht_abbildung {frame : MemFrame} {sp : Nat} {space : Adressraum}
    (found : frame.spaces[sp]? = some space) (page : Nat) :
    frame.tabellenSicht sp page = space.abbildung page := by
  simp only [MemFrame.tabellenSicht, found]

/-- Outside the spaces there is no table entry. -/
theorem MemFrame.tabellenSicht_none {frame : MemFrame} {sp page : Nat}
    (missing : frame.spaces[sp]? = none) :
    frame.tabellenSicht sp page = none := by
  simp only [MemFrame.tabellenSicht, missing]

/-- The table view after replacing a space is the mapping of the new space. -/
theorem MemFrame.tabellenSicht_set {frame : MemFrame} {sp : Nat} {new : Adressraum}
    (lt : sp < frame.spaces.length) (page : Nat) :
    ({ frame with spaces := frame.spaces.set sp new } : MemFrame).tabellenSicht sp page =
      new.abbildung page := by
  have found : (frame.spaces.set sp new)[sp]? = some new :=
    List.getElem?_set_self lt
  have hfound : ({ frame with spaces := frame.spaces.set sp new } : MemFrame).spaces[sp]? =
      some new :=
    found
  exact MemFrame.tabellenSicht_abbildung hfound page

end Gabbro.Core.Ast.LowLevel
