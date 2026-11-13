module

public import Grammatik.Niedrig.Witnesses.Fixture

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

def layout : AdressLayout D :=
  { raum := fun _ => 0
    basis := fun _ => 100
    breite := fun _ => 16
    versatz := fun _ _ => 0
    groesse := fun _ _ => 1
    gbasis := fun g => g.elim
    ggroesse := fun g => g.elim
    graum := fun g => g.elim
    nominal := fun _ => 0 }

theorem layout_correct : LayoutOk layout :=
  { tabellenRaum := (by intro t; exact ⟨by change 0 < 1; omega, rfl⟩)
    offen := (by intro t h; cases h)
    feld := (by intro t f; change 0 + 1 ≤ 16; omega)
    felder := (by intro t f f' h; exact False.elim (h (Subsingleton.elim _ _)))
    tabellen := (by intro t t' byte h; exact False.elim (h (Subsingleton.elim _ _)))
    tabGlob := (by intro t g; exact g.elim)
    globale := (by intro g; exact g.elim)
    globalerRaum := (by intro g; exact g.elim) }

theorem layout_realizes : authority.Realizes layout := by
  intro span member
  change span ∈ [ram, device] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, by change 100 ≤ 100; omega, .inr (by change 100 + 8 ≤ 100 + 1 * 16; omega)⟩
  · exact ⟨rfl, by change 100 ≤ 108; omega, .inr (by change 108 + 8 ≤ 100 + 1 * 16; omega)⟩

def before : World D :=
  { slots := fun _ _ _ => ⟨0, by omega, by omega⟩
    globs := fun g => g.elim
    spur := [] }

def after : World D := before.storeSlot () 0 () ⟨1, by omega, by omega⟩

/-- A real existing carrier write; it is not a new low-level evaluator. -/
def write : ViewWrite authority writableResult.next layout before after :=
  { view := writableView
    live := List.mem_cons_self ..
    active := rfl
    valid := ram_view_preserves initial_valid writableResult
    writable := rfl
    index := 0
    field := ()
    extent := ⟨(by change (0 : Int) ≤ 0; omega), .inr (by change (0 : Int) < 1; omega)⟩
    bytes := (by
      intro byte h
      change byte.1 = 0 ∧ 100 + 0 * 16 + 0 ≤ byte.2 ∧
        byte.2 < 100 + 0 * 16 + 0 + 1 at h
      change byte.1 = 0 ∧ 100 ≤ byte.2 ∧ byte.2 < 100 + 4
      exact ⟨h.1, by omega, by omega⟩)
    value := ⟨1, by omega, by omega⟩
    store := rfl }

theorem real_write_zeuge :
    (before.slots () 0 ()).n = 0 ∧ (after.slots () 0 ()).n = 1 ∧
    writableView.Contains (0, 100) ∧ layout.inTabelle () (0, 100) := by
  have h := view_write_confined (D := D) layout_correct write
    (byte := (0, 100)) (show layout.inZelle () 0 () (0, 100) from
      ⟨rfl, by change 100 + 0 * 16 + 0 ≤ 100; omega,
        by change 100 < 100 + 0 * 16 + 0 + 1; omega⟩)
  exact ⟨rfl, rfl, h⟩

theorem ram_view_in_layout_zeuge :
    layout.inTabelle writableResult.view.span.table (0, 100) ∧
    layout.nominal 0 = D.tableSpace writableResult.view.span.table :=
  ram_view_in_layout (D := D) writableResult layout layout_correct layout_realizes
    (byte := (0, 100))
    ⟨rfl, by change 100 ≤ 100; omega, by change 100 < 100 + 4; omega⟩

end Gabbro.Grammatik.LowLevel.Witness
