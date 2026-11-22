module

public import Stage0.Senke.Bild.ImageGoal
public import Grammatik.Speichermodell.Adressen.Bereich
public import Stage0.Senke.Bild.Mehr.ImageTransition
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz
  Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Stage0.Senke
  Gabbro.Stage0.Senke.BildMehr Runner Runner.IR

variable {src : String} {K : Nat} {options : Profil.Options}

/-- Every actual instruction byte address is below all stack and world
    addresses. In particular its 64-bit address is exact. -/
theorem Emitted.code_byte_before_stacks [Kern] (output : Emitted src K options) {index : Nat}
    (inCode : index < (output.image.code.flatMap encII).length) :
    (BitVec.ofNat 64 (codeBase + index)).toNat < output.image.fp0 := by
  have below : codeBase + index < output.image.fp0 := by
    rw [← output.code_end]
    omega
  obtain ⟨stackBound, limit⟩ := output.stackReservation_bounds
  have frameFits : output.image.fp0 < 2 ^ 64 := by omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (below.trans frameFits)]
  exact below

/-- Writes confined to the emitted stacks and the area following them
    leave every instruction byte and its permissions unchanged. -/
theorem Emitted.code_survives_writes [Kern] (output : Emitted src K options) {saved current : Runner.Mem}
    {footprint : W → Prop} (writes : NurIn footprint saved current)
    (afterCode : ∀ byte, footprint byte → output.image.fp0 ≤ byte.toNat)
    (code : BytesAt saved codeBase (output.image.code.flatMap encII)) :
    BytesAt current codeBase (output.image.code.flatMap encII) := by
  intro index inCode
  have outside : ¬ footprint (BitVec.ofNat 64 (codeBase + index)) :=
    fun written => (Nat.not_le_of_lt (output.code_byte_before_stacks inCode)) (afterCode _ written)
  rw [writes.rd, writes.wr, writes.b _ outside]
  exact code index inCode

/-- Pending private stores are outside the emitted instruction extent,
    so an issuing thread fetches the same code as shared memory holds. -/
theorem Emitted.code_in_private_view [Kern] (output : Emitted src K options)
    (state : Runner.Beweis.TSt) (stores : PrivateBuffers (imageStackFootprint output) state)
    (code : BytesAt state.m codeBase (output.image.code.flatMap encII)) (thread : Nat) :
    BytesAt (state.view thread) codeBase (output.image.code.flatMap encII) := by
  intro index inCode
  let address := BitVec.ofNat 64 (codeBase + index)
  have unchanged := Runner.Beweis.foldl_far (state.buf thread) state.m (y := address) (by
    intro store queued offset inside overlap
    have touched : fenster store.1 address := overlap.symm ▸ fenster_add _ inside
    have privateByte := (stores thread store queued address touched).1
    have above := (Nat.le_add_right _ _).trans privateByte.2.1
    exact (Nat.not_le_of_lt (output.code_byte_before_stacks inCode)) above)
  obtain ⟨readable, writable, byte⟩ := code index inCode
  exact ⟨unchanged.2.trans readable, (congrFun (Runner.Beweis.foldl_wr _ _) address).trans writable,
    unchanged.1.trans byte⟩

/-- A real asynchronous flush writes only within its own emitted
    stack reservation and preserves the shared instruction bytes. -/
theorem Emitted.code_after_private_flush [Kern] (output : Emitted src K options)
    {state after : imageTSO.St} (stores : PrivateBuffers (imageStackFootprint output) state.1)
    (code : BytesAt state.1.m codeBase (output.image.code.flatMap encII))
    (flushed : imageTSO.tau state after) :
    BytesAt after.1.m codeBase (output.image.code.flatMap encII) := by
  obtain ⟨issuer, address, value, _, pending, updated⟩ := flushed
  have member : (address, value) ∈ state.1.buf issuer := by
    rw [pending]
    exact List.mem_cons_self
  rw [updated]
  apply output.code_survives_writes (write_nurIn state.1.m address value.toNat) _ code
  intro byte hit
  exact (Nat.le_add_right _ _).trans (stores issuer (address, value) member byte hit).1.2.1

/-- The concrete builder bounds every typed cell and separates its bytes
    from other cells. This is a property of the relocated image's layout. -/
theorem Emitted.layout_checked (output : Emitted src K options) :
    LayIn output.image.Y ∧ LayDis output.image.Y ∧ LaySync output.image.Y := by
  obtain ⟨_, _, _, layout, _⟩ :=
    bild_lage output.emission output.funktionen_voll
      (fun base bound => layU_in output.compiled.unit output.tor base bound)
      (fun base => layU_dis output.compiled.unit output.tor base)
      (fun base => by simp only [layU]; omega)
      (fun base => layU_sync output.compiled.unit output.tor base)
  exact ⟨layout.hlay, layout.hdis, layout.hsync⟩

/-- Physical base of the table's complete, consecutive columns. -/
def InitialLayout.tableBase {u : UProg} (L : Lay (declOf u)) (t : (declOf u).Tab) : Nat :=
  L.lo + globEnd (List.finRange u.globs.length) 0 (globSz u) (fun g => wordAlign (globAlign u g)) +
    (((List.finRange u.tabs.length).map (tabSz u)).take t.val).sum

/-- Every byte of a represented cell is in its actual table, accounting
    for the field's own stride and for all preceding columns. -/
theorem InitialLayout.cell_in_table {u : UProg} {L : Lay (declOf u)} (layout : InitialLayout u L)
    (t : (declOf u).Tab) (f : (declOf u).Feld t) (index : Nat)
    (bounded : (index : Int) < L.count t) :
    InitialLayout.tableBase L t ≤ L.elem t f index ∧
      L.elem t f index + 8 * valueWords ((declOf u).typ t f) ≤ InitialLayout.tableBase L t + tabSz u t := by
  have own := colSz_ge u t f index ((layout.count t) ▸ bounded)
  have column := take_sum_add ((List.finRange (fieldCount u t)).map (colSz u t)) f.val
    (by simpa only [List.length_map, List.length_finRange] using f.isLt)
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk] at column
  change (((List.finRange (fieldCount u t)).map (colSz u t)).take f.val).sum +
    colSz u t f ≤ tabSz u t at column
  rw [Lay.elem, layout.columns]
  unfold InitialLayout.tableBase
  omega

/-- The extent leg on the actual column layout. On a closed table,
    reachability supplies the physical index bound on its own. -/
theorem Emitted.changedCell_in_image (output : Emitted src K options)
    (Q : AxEns (declOf output.compiled.unit)) (O : Orakel (declOf output.compiled.unit))
    (foreignConfined : ImBereichO O.mitRuhe)
    {live : Faden → Bool} {state : FadenMaschine (declOf output.compiled.unit).mitRuhe}
    (reached : FadenErreichbarX (output.goalUnit Q).P.mitRuhe O.mitRuhe output.image.passes
      (GeteiltV (D := declOf output.compiled.unit) (output.goalUnit Q).P (output.goalUnit Q).ws)
      (output.goalStart Q live) state)
    (t : (declOf output.compiled.unit).Tab) (k : Int) (f : (declOf output.compiled.unit).Feld t)
    (changed : state.m.speicher.slots t k f ≠ (speicherR (output.goalUnit Q).sp0).slots t k f) :
    ImBereich (declOf output.compiled.unit) t k ∧
      (k < (declOf output.compiled.unit).count t →
        ∀ address, output.image.Y.elem t f k.toNat ≤ address →
          address < output.image.Y.elem t f k.toNat + 8 * valueWords ((declOf output.compiled.unit).typ t f) →
          InitialLayout.tableBase output.image.Y t ≤ address ∧
            address < InitialLayout.tableBase output.image.Y t + tabSz output.compiled.unit t) := by
  have outside := rufErreichbarGX_aussen (fun _ shared => by
    obtain ⟨_, impossible, _⟩ := shared.1.1
    cases impossible) foreignConfined (fadenErreichbarX_GX reached)
  have inExtent : ImBereich (declOf output.compiled.unit) t k :=
    Classical.byContradiction fun notIn => changed (outside t k f notIn)
  refine ⟨inExtent, ?_⟩
  intro bounded address lower upper
  have layout := initialLayout_bild output.emission
  have actual : (k.toNat : Int) < output.image.Y.count t := by
    rw [layout.count]
    have nonnegative := inExtent.1
    omega
  obtain ⟨base, last⟩ := InitialLayout.cell_in_table layout t f k.toNat actual
  exact ⟨Nat.le_trans base lower, Nat.lt_of_lt_of_le upper last⟩

/-- The row layout cannot name the exact column addresses and sizes for
    two fields at two indices. The contradiction is in the row stride,
    independently of relocation or of the particular table values. -/
theorem column_addresses_exclude_row_layout {D : Deklaration} (L : Lay D)
    (row : AdressLayout D) (valid : LayoutOk row)
    (t : D.Tab) (f other : D.Feld t) (distinct : f ≠ other)
    (first : row.adresse t 0 f = L.elem t f 0)
    (second : row.adresse t 1 f = L.elem t f 1)
    (size : row.groesse t f = 8 * valueWords (D.typ t f))
    (otherNonempty : 0 < row.groesse t other) : False := by
  have stride : row.breite t = row.groesse t f := by
    simp [AdressLayout.adresse, Lay.elem] at first second
    omega
  have room := valid.feld t f
  have otherRoom := valid.feld t other
  rcases valid.felder t f other distinct with left | right <;> omega

end Gabbro.Stage0
