module

public import Grammatik.Niedrig.Authority.SimGMachine
public import Grammatik.Kern.Syntax.Extensions.Extraktion.T6

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-!
R3, no bypass: the vocabulary and every way a world of machine G changes a table cell.

Authority bytes are the bytes of the finite reservations (`Span`) of an authority, placed by a
layout. A change of authority bytes is a changed cell `(t, k, f)` of which one byte lies in a span
(`AuthorityChange`). Machine G changes a table cell only through these world operations:

* `World.storeSlot` (untraced; G uses it only inside `schreibSlot`, the view receipt uses it as
  its store): it changes at most its own cell (`storeSlot_changed_table`, `storeSlot_changed_cell`);
* `World.schreibSlot`: the same cell plus one `zugriff t true` event (`schreibSlot_records`);
* `World.schreibBytes`: cells of its own table only, one `zugriff t true` per byte
  (`schreibBytes_changed_table`, `schreibBytes_records`);
* an oracle answer (`Orakel.wirkt`, every foreign call): under `GutO` only a declared write
  (`oracle_write_declared`), recorded as `axiomSpur` when the call's guards are held
  (`oracle_records`);
* `merke`, `lese`, `fragt`, `nimmt`, `gibt`, `storeGlob`, `schreibGlob` keep every table cell
  (`trace_operations_keep_slots`).

Call, return and scope steps of the machine move frames and traces, not cells; for every step
the frame theorem `rufSchrittG_aussen` (Speichermodell/Adressen/Bereich.lean) bounds all changed
cells to the declared extents, which is what NoBypassSaetze.lean uses.
-/

variable {D : Deklaration}

/-- A byte inside the finite reservation `span`: its backing identity, inside its range. -/
def Span.Covers (span : Span D) (byte : Adresse) : Prop :=
  byte.1 = span.space.backing ∧ span.base ≤ byte.2 ∧ byte.2 < span.base + span.length

/-- Some byte of cell `(t, k, f)` under `layout` lies in `span`. -/
def Span.Touches (span : Span D) (layout : AdressLayout D) (t : D.Tab) (k : Int)
    (f : D.Feld t) : Prop :=
  ∃ byte, layout.inZelle t k f byte ∧ span.Covers byte

/-- From memory `s` to memory `s'` the cell `(t, k, f)` changed, and one of its bytes is a byte
    of the authority `a`. -/
def AuthorityChange (a : Authority D) (layout : AdressLayout D) (s s' : Speicher D)
    (t : D.Tab) (k : Int) (f : D.Feld t) : Prop :=
  s'.slots t k f ≠ s.slots t k f ∧ ∃ span ∈ a.spans, span.Touches layout t k f

/-- A realized span lies in the region of its own table. `LayoutOk` is not needed. -/
theorem span_byte_table {span : Span D} {layout : AdressLayout D}
    (realizes : span.Realizes layout) {byte : Adresse} (covers : span.Covers byte) :
    layout.inTabelle span.table byte := by
  obtain ⟨backing, low, high⟩ := covers
  obtain ⟨space, base, extent⟩ := realizes
  refine ⟨backing.trans space, by omega, ?_⟩
  rcases extent with opened | finite
  · exact .inl opened
  · right
    omega

/-- A cell in its declared extent that touches a realized span is a cell of the span's table:
    under a correct layout two tables share no byte. -/
theorem touch_table {span : Span D} {layout : AdressLayout D} (correct : LayoutOk layout)
    (realizes : span.Realizes layout) {t : D.Tab} {k : Int} {f : D.Feld t}
    (extent : ImBereich D t k) (touch : span.Touches layout t k f) : span.table = t := by
  obtain ⟨byte, cell, covers⟩ := touch
  exact Classical.byContradiction fun different =>
    correct.tabellen span.table t byte different (span_byte_table realizes covers)
      (zelle_im_bereich correct extent f cell)

/-- **Every change of authority bytes is a change of a cell of a span's own table, in its
    declared extent**, for any two memories that agree outside the extents (every G and GX step,
    `rufSchrittG_aussen`, `rufSchrittGX_aussen`). A global, another table or an index outside the
    extent never reaches an authority byte. -/
theorem authority_change_cell {a : Authority D} {layout : AdressLayout D} {s s' : Speicher D}
    (outside : AussenGleich s s') (correct : LayoutOk layout) (realizes : a.Realizes layout)
    {t : D.Tab} {k : Int} {f : D.Feld t} (change : AuthorityChange a layout s s' t k f) :
    ∃ span ∈ a.spans, span.table = t ∧ ImBereich D t k ∧
      ∀ byte, layout.inZelle t k f byte → layout.inTabelle t byte := by
  obtain ⟨changed, span, member, touch⟩ := change
  have inside := geaendert_im_bereich outside correct changed
  exact ⟨span, member, touch_table correct (realizes span member) inside.1 touch, inside.1,
    inside.2⟩

/-! ## The world operations that change a table cell -/

theorem storeSlot_changed_table (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) {t' : D.Tab} {k' : Int} {f' : D.Feld t'}
    (changed : (σ.storeSlot t k f v).slots t' k' f' ≠ σ.slots t' k' f') : t' = t :=
  Classical.byContradiction fun other => changed (storeSlot_andere σ t k f v t' other k' f')

theorem storeSlot_changed_cell (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) {k' : Int} {f' : D.Feld t}
    (changed : (σ.storeSlot t k f v).slots t k' f' ≠ σ.slots t k' f') : k' = k ∧ f' = f := by
  by_cases index : k' = k
  · refine ⟨index, Classical.byContradiction fun field => changed ?_⟩
    simp only [World.storeSlot, ↓reduceDIte, index, ↓reduceIte, field]
  · exact (changed (by simp only [World.storeSlot, ↓reduceDIte, index, ↓reduceIte])).elim

/-- A traced slot write records exactly one write event on its table and stores like
    `storeSlot`. -/
theorem schreibSlot_records (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) :
    (σ.schreibSlot t Λ k f v).spur = Ereignis.zugriff t true Λ σ.haelt :: σ.spur ∧
    (σ.schreibSlot t Λ k f v).slots = (σ.storeSlot t k f v).slots :=
  ⟨rfl, rfl⟩

/-- A byte transfer changes cells of its own table only, and only when it writes a byte. -/
theorem schreibBytes_changed_table (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) {t' : D.Tab} {k' : Int} {f' : D.Feld t'} :
    ∀ (bytes : List Byte) (σ : World D) (k : Int),
      (σ.schreibBytes t f hf Λ k bytes).slots t' k' f' ≠ σ.slots t' k' f' →
        t' = t ∧ bytes ≠ []
  | [], _, _, changed => (changed rfl).elim
  | b :: bytes, σ, k, changed => by
      refine ⟨?_, List.cons_ne_nil b bytes⟩
      by_cases same : ((σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bytes).slots t' k' f' =
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).slots t' k' f'
      · have moved : (σ.storeSlot t k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).slots t' k' f' ≠
            σ.slots t' k' f' := fun equal => changed (same.trans equal)
        exact storeSlot_changed_table σ t k f _ moved
      · exact (schreibBytes_changed_table t f hf Λ bytes _ (k + 1) same).1

/-- A byte transfer that writes a byte records a write event on its table. -/
theorem schreibBytes_records (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bytes : List Byte)
    (written : bytes ≠ []) :
    Ereignis.zugriff t true Λ σ.haelt ∈ (σ.schreibBytes t f hf Λ k bytes).spur := by
  rw [Extraktion.schreibBytes_spur_eq]
  cases bytes with
  | nil => exact (written rfl).elim
  | cons b rest =>
    exact List.mem_append_left _ (List.mem_replicate.mpr ⟨Nat.succ_ne_zero _, rfl⟩)

/-- Under `GutO` an oracle answer changes a cell only of a table its axiom declares written. -/
theorem oracle_write_declared {O : Orakel D} (hO : GutO O) (q : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams q)) {t : D.Tab} {k : Int} {f : D.Feld t}
    (changed : (O.wirkt q σ ρ).1.slots t k f ≠ σ.slots t k f) : D.aschreibt q t = true := by
  cases written : D.aschreibt q t with
  | false => exact (changed ((hO q σ ρ).1.1 t written k f)).elim
  | true => rfl

/-- With the call's guards held (every real call site), the changed table's write event is in
    the oracle's trace (`axiomSpur`). -/
theorem oracle_records {O : Orakel D} (hO : GutO O) (q : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams q)) {t : D.Tab} {k : Int} {f : D.Feld t}
    (changed : (O.wirkt q σ ρ).1.slots t k f ≠ σ.slots t k f)
    (guards : ∀ t, D.aschreibt q t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt)
    (globalGuards : ∀ g, D.agschreibt q g = true → ∀ L, Sum.inl L ∈ D.gbraucht g →
      L ∈ σ.haelt) :
    ∃ Λ : List (Res D), Ereignis.zugriff t true Λ σ.haelt ∈ (O.wirkt q σ ρ).1.spur := by
  have written := oracle_write_declared hO q σ ρ changed
  obtain ⟨tabs, _, Λ, covered, _, _, _, _, _, trace⟩ := (hO q σ ρ).2.2 guards globalGuards
  refine ⟨Λ, ?_⟩
  rw [trace]
  refine List.mem_append_left _ ?_
  unfold axiomSpur
  exact List.mem_append_left _
    (List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨covered t written, written⟩, rfl⟩)

/-- Trace operations and global writes keep every table cell. -/
theorem trace_operations_keep_slots (σ : World D) (es : List (Ereignis D)) (Λ : List (Res D))
    (places : List (D.Tab ⊕ D.Glob)) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) (L : D.Lock) (g : D.Glob)
    (v : Wert D (D.gtyp g)) :
    (σ.merke es).slots = σ.slots ∧ (σ.lese Λ places).slots = σ.slots ∧
    (σ.fragt q).slots = σ.slots ∧ (σ.nimmt L).slots = σ.slots ∧ (σ.gibt L).slots = σ.slots ∧
    (σ.storeGlob g v).slots = σ.slots ∧ (σ.schreibGlob g Λ v).slots = σ.slots :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The named premise -/

/-- **NAMED PREMISE (not proved here): view-scoped authority writes.** For one transition of
    thread `u` from `M` to `M'` under the ghost context `c`: every changed cell of a span's own
    table, in its extent and touching that span, is covered by a live, active, writable view of
    that table, and the transition records the write event of that table.

    Machine G does not track views, so no G theorem can supply this. It must be supplied by the
    R2-B view checker `sichtB` (every write statement on a table that backs an authority span lies
    in a view scope whose receipt covers the written cell; axioms that declare writes to such a
    table and byte transfers into it are refused or scoped the same way), together with L3 (typed
    reference introduction from a live view, whose lowering is the receipt's single
    `schreibSlot`, `viewwrite_accessG`). It speaks only of the authority's own tables:
    that no other carrier, global or out-of-extent index reaches authority bytes is PROVED
    (`authority_change_cell`). -/
structure ViewScopedStep {P I : Type} (a : Authority D) (layout : AdressLayout D)
    (c : Context D P I) (M M' : RufMaschineG D) (u : Faden) : Prop where
  valid : c.Valid a
  confined : ∀ span ∈ a.spans, ∀ (t : D.Tab) (k : Int) (f : D.Feld t), span.table = t →
    ImBereich D t k → M'.speicher.slots t k f ≠ M.speicher.slots t k f →
    span.Touches layout t k f →
    ∃ view ∈ c.views, c.frame = view.borrower ∧ view.rights.write = true ∧
      view.span.table = t ∧ (∀ byte, layout.inZelle t k f byte → view.Contains byte) ∧
      (Sum.inl t, true) ∈ zugriffe M M' u

end Gabbro.Grammatik.LowLevel
