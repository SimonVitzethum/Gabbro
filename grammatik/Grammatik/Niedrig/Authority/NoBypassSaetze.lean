module

public import Grammatik.Niedrig.Authority.NoBypass
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T3

@[expose] public section

namespace Gabbro.Grammatik.LowLevel

/-!
R3, no bypass, as theorems about machine G.

* `location_inert`: an address expression and its location take no G step, record no access,
  write no carrier and change no authority byte; an address never yields a view
  (`view_required`) and a location outside every span is refused (`forged_location_refused`).
* `region_forgets_bounds`: a region (`View.region`, a `DataCapTy`) carries no bounds, and
  without a live view of that region it admits no write receipt and no authority-byte change.
* `storeSlot_only_via_view`: every G step (GX: `storeSlot_only_via_view_gx`) that changes an
  authority byte changes a cell of a span's table in its extent and carries the
  `Ereignis.zugriff t true` of a live, valid, active, writable view of that table which covers
  every byte of the cell. Its only premise beyond the machine is the named `ViewScopedStep`.
* `kein_umweg`: the same over a run, for every authority byte that differs between start and end.
* `authority_writer_declared` (no named premise): under `GutO`, every step that changes an
  authority byte belongs to a function whose signature declares a write to the span's table.
-/

variable {D : Deklaration}

/-! ## Locations are inert -/

/-- **An address location is world-inert**: evaluating an address expression is zero G steps,
    which access and write no carrier and change no byte of any authority. -/
theorem location_inert {space : Space D} (e : AddressExpr space) (M : RufMaschineG D)
    (u : Faden) :
    (evalAddress e (M.weltVon u)).2 = M.weltVon u ∧
    (∀ c, ¬ ZugriffG M M u c) ∧ (∀ c, ¬ SchreibG M M u c) ∧
    ∀ (a : Authority D) (layout : AdressLayout D) (t : D.Tab) (k : Int) (f : D.Feld t),
      ¬ AuthorityChange a layout M.speicher M.speicher t k f := by
  have silent : ∀ c w, (c, w) ∉ zugriffe M M u := by
    intro c w member
    rw [zugriffe_ereignisse, ereignisse_eq (M := M) (M' := M) (f := u) (X := []) rfl] at member
    exact absurd member List.not_mem_nil
  refine ⟨rfl, fun c access => ?_, fun c access => ?_, fun _ _ _ _ _ change => change.1 rfl⟩
  · rcases access with ⟨w, recorded⟩ | moved
    · exact silent c w recorded
    · exact moved (traegerGleich_refl _ c)
  · rcases access with recorded | moved
    · exact silent c true recorded
    · exact moved (traegerGleich_refl _ c)

/-- A write receipt exists only for a live view: a location or region alone gives none. -/
theorem view_required {P I : Type} {a : Authority D} {c : Context D P I}
    {layout : AdressLayout D} {before after : World D}
    (write : ViewWrite a c layout before after) : write.view ∈ c.views ∧ c.views ≠ [] := by
  refine ⟨write.live, fun empty => ?_⟩
  have live := write.live
  rw [empty] at live
  cases live

/-- A forged location, outside every span of the authority, is refused by the only producer. -/
theorem forged_location_refused {P I : Type} {space : Space D} (a : Authority D)
    (c : Context D P I) (start : Address space) (length : Nat) (rights : DataRights)
    (borrower : ArenaOwnership.Frame)
    (outside : ∀ span ∈ a.spans,
      ¬ (span.space = space ∧ span.base ≤ start.byte ∧ start.byte < span.base + span.length)) :
    ram_view a c start length rights borrower = .error .bounds := by
  unfold ram_view
  split
  · rfl
  · rename_i span selected
    have chosen := List.find?_some selected
    have member := List.mem_of_find?_eq_some selected
    exact absurd (by simpa only [decide_eq_true_eq] using chosen) (outside span member)

/-! ## Every authority write goes through a live view -/

/-- **The core of no-bypass**, for any transition whose memories agree outside the extents. -/
theorem storeSlot_only_via_view_core {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {M M' : RufMaschineG D} {u : Faden}
    (outside : AussenGleich M.speicher M'.speicher) (correct : LayoutOk layout)
    (realizes : a.Realizes layout) (scope : ViewScopedStep a layout c M M' u)
    {t : D.Tab} {k : Int} {f : D.Feld t}
    (change : AuthorityChange a layout M.speicher M'.speicher t k f) :
    ∃ view ∈ c.views, view.Valid a ∧ c.frame = view.borrower ∧ view.rights.write = true ∧
      view.span.table = t ∧ ImBereich D t k ∧
      (∃ (Λ : List (Res D)) (held : List D.Lock),
        Ereignis.zugriff t true Λ held ∈ ereignisse M M' u) ∧
      ZugriffG M M' u (.inl t) ∧ SchreibG M M' u (.inl t) ∧
      ∀ byte, layout.inZelle t k f byte → view.Contains byte ∧ layout.inTabelle t byte := by
  obtain ⟨_, _, _, extent, region⟩ := authority_change_cell outside correct realizes change
  obtain ⟨changed, span, member, touch⟩ := change
  have table := touch_table correct (realizes span member) extent touch
  obtain ⟨view, live, active, writable, viewTable, bytes, recorded⟩ :=
    scope.confined span member t k f table extent changed touch
  refine ⟨view, live, scope.valid.2.2.2.1 view live, active, writable, viewTable, extent,
    ?_, Or.inl ⟨true, recorded⟩, Or.inl recorded,
    fun byte cell => ⟨bytes byte cell, region byte cell⟩⟩
  rw [zugriffe_ereignisse, List.mem_filterMap] at recorded
  obtain ⟨event, occurs, access⟩ := recorded
  rcases zugriffVon_some access with ⟨t', Λ, held, rfl, same⟩ | ⟨g, Λ, held, rfl, same⟩
  · cases same
    exact ⟨Λ, held, occurs⟩
  · cases same

/-- **`storeSlot_only_via_view`**: every step of machine G that changes an authority byte. -/
theorem storeSlot_only_via_view {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {program : Programm D} {oracle : Orakel D} {passes : Nat}
    {M M' : RufMaschineG D} {u : Faden} (step : RufSchrittG program oracle passes M u M')
    (foreign : ImBereichO oracle) (correct : LayoutOk layout) (realizes : a.Realizes layout)
    (scope : ViewScopedStep a layout c M M' u) {t : D.Tab} {k : Int} {f : D.Feld t}
    (change : AuthorityChange a layout M.speicher M'.speicher t k f) :
    ∃ view ∈ c.views, view.Valid a ∧ c.frame = view.borrower ∧ view.rights.write = true ∧
      view.span.table = t ∧ ImBereich D t k ∧
      (∃ (Λ : List (Res D)) (held : List D.Lock),
        Ereignis.zugriff t true Λ held ∈ ereignisse M M' u) ∧
      ZugriffG M M' u (.inl t) ∧ SchreibG M M' u (.inl t) ∧
      ∀ byte, layout.inZelle t k f byte → view.Contains byte ∧ layout.inTabelle t byte :=
  storeSlot_only_via_view_core (rufSchrittG_aussen foreign step) correct realizes scope change

/-- The same for every step of machine GX (the machine of the goal statement). -/
theorem storeSlot_only_via_view_gx {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {program : Programm D} {oracle : Orakel D} {passes : Nat}
    {shared : D.Tab ⊕ D.Glob → Prop} (tables : ∀ t, ¬ shared (.inl t))
    {M M' : RufMaschineG D} {u : Faden} (step : RufSchrittGX program oracle passes shared M u M')
    (foreign : ImBereichO oracle) (correct : LayoutOk layout) (realizes : a.Realizes layout)
    (scope : ViewScopedStep a layout c M M' u) {t : D.Tab} {k : Int} {f : D.Feld t}
    (change : AuthorityChange a layout M.speicher M'.speicher t k f) :
    ∃ view ∈ c.views, view.Valid a ∧ view.rights.write = true ∧ view.span.table = t ∧
      ImBereich D t k ∧ SchreibG M M' u (.inl t) ∧
      ∀ byte, layout.inZelle t k f byte → view.Contains byte ∧ layout.inTabelle t byte := by
  obtain ⟨view, live, valid, _, writable, table, extent, _, _, written, bytes⟩ :=
    storeSlot_only_via_view_core (rufSchrittGX_aussen tables foreign step) correct realizes
      scope change
  exact ⟨view, live, valid, writable, table, extent, written, bytes⟩

/-! ## Regions -/

/-- **A region forgets bounds and admits no access without a live view.** The region of a view
    is independent of its bounds and loan; a write receipt needs a live view with that region;
    and every authority-byte change of a view-scoped step goes through a live writable view
    whose region is not a given unbacked region. -/
theorem region_forgets_bounds {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {M M' : RufMaschineG D} {u : Faden} (region : DataCapTy)
    (outside : AussenGleich M.speicher M'.speicher) (correct : LayoutOk layout)
    (realizes : a.Realizes layout) (scope : ViewScopedStep a layout c M M' u)
    (unbacked : ∀ view ∈ c.views, view.region ≠ region) :
    (∀ (view : View D) (base length : Nat) (lender borrower : ArenaOwnership.Frame),
      ({ view with
          base := base
          length := length
          lender := lender
          borrower := borrower } : View D).region = view.region) ∧
    (∀ (before after : World D) (write : ViewWrite a c layout before after),
      write.view.region ≠ region) ∧
    (∀ (t : D.Tab) (k : Int) (f : D.Feld t),
      AuthorityChange a layout M.speicher M'.speicher t k f →
        ∃ view ∈ c.views, view.region ≠ region ∧ view.rights.write = true ∧
          view.span.table = t) := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ write => unbacked write.view write.live, ?_⟩
  intro t k f change
  obtain ⟨view, live, _, _, writable, table, _⟩ :=
    storeSlot_only_via_view_core outside correct realizes scope change
  exact ⟨view, live, unbacked view live, writable, table⟩

/-- Without any live view a view-scoped step changes no authority byte. -/
theorem no_view_no_change {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {c : Context D P I} {M M' : RufMaschineG D} {u : Faden}
    (outside : AussenGleich M.speicher M'.speicher) (correct : LayoutOk layout)
    (realizes : a.Realizes layout) (scope : ViewScopedStep a layout c M M' u)
    (empty : c.views = []) {t : D.Tab} {k : Int} {f : D.Feld t} :
    ¬ AuthorityChange a layout M.speicher M'.speicher t k f := by
  intro change
  obtain ⟨view, live, _⟩ := storeSlot_only_via_view_core outside correct realizes scope change
  rw [empty] at live
  cases live

/-! ## Runs -/

/-- A value that differs between index `0` and `n` changes at some step below `n`. -/
theorem changed_at_some_step {α : Sort _} (x : Nat → α) :
    ∀ n, x n ≠ x 0 → ∃ i, i < n ∧ x (i + 1) ≠ x i := by
  intro n
  induction n with
  | zero => intro differs; exact (differs rfl).elim
  | succ n ih =>
    intro differs
    by_cases same : x (n + 1) = x n
    · obtain ⟨i, below, moved⟩ := ih (fun start => differs (same.trans start))
      exact ⟨i, Nat.lt_succ_of_lt below, moved⟩
    · exact ⟨n, Nat.lt_succ_self n, same⟩

/-- **`kein_umweg`: no detour over a run.** If an authority byte's cell differs between the start
    and the end of a G run, some step changed it, in its extent, and that step carries the write
    event of a live, valid, active, writable view of the span's table covering the whole cell. -/
theorem kein_umweg {P I : Type} {a : Authority D} {layout : AdressLayout D}
    {program : Programm D} {oracle : Orakel D} {passes : Nat}
    (foreign : ImBereichO oracle) (correct : LayoutOk layout) (realizes : a.Realizes layout)
    {machines : Nat → RufMaschineG D} {threads : Nat → Faden} {n : Nat}
    (run : ∀ i, i < n → RufSchrittG program oracle passes (machines i) (threads i)
      (machines (i + 1)))
    (contexts : Nat → Context D P I)
    (confinedSteps : ∀ i, i < n → ViewScopedStep a layout (contexts i) (machines i) (machines (i + 1))
      (threads i))
    {t : D.Tab} {k : Int} {f : D.Feld t}
    (change : AuthorityChange a layout (machines 0).speicher (machines n).speicher t k f) :
    ImBereich D t k ∧ ∃ i, i < n ∧
      AuthorityChange a layout (machines i).speicher (machines (i + 1)).speicher t k f ∧
      ∃ view ∈ (contexts i).views, view.Valid a ∧ (contexts i).frame = view.borrower ∧
        view.rights.write = true ∧ view.span.table = t ∧
        (∃ (Λ : List (Res D)) (held : List D.Lock),
          Ereignis.zugriff t true Λ held ∈ ereignisse (machines i) (machines (i + 1)) (threads i)) ∧
        ∀ byte, layout.inZelle t k f byte → view.Contains byte ∧ layout.inTabelle t byte := by
  obtain ⟨changed, span, member, touch⟩ := change
  obtain ⟨i, below, moved⟩ :=
    changed_at_some_step (fun j => (machines j).speicher.slots t k f) n changed
  have stepChange :
      AuthorityChange a layout (machines i).speicher (machines (i + 1)).speicher t k f :=
    ⟨moved, span, member, touch⟩
  obtain ⟨view, live, valid, active, writable, table, extent, event, _, _, bytes⟩ :=
    storeSlot_only_via_view (run i below) foreign correct realizes (confinedSteps i below) stepChange
  exact ⟨extent, i, below, stepChange, view, live, valid, active, writable, table, event, bytes⟩

/-! ## Declared writers -/

/-- **Only a declared writer reaches authority bytes** (no named premise): under `GutO`, a step of
    a run from a start machine that changes an authority byte belongs to a function whose
    signature declares a write to the span's table, and the cell is in its extent. -/
theorem authority_writer_declared {a : Authority D} {layout : AdressLayout D}
    {program : Programm D} {oracle : Orakel D} {passes : Nat} (good : GutO oracle)
    (foreign : ImBereichO oracle) (correct : LayoutOk layout) (realizes : a.Realizes layout)
    (memory : Speicher D) (init : Faden → Σ g : D.Fn, Env D (D.params g))
    {M M' : RufMaschineG D} {u : Faden}
    (reach : RufErreichbarG program oracle passes (RufStartG program memory init) M)
    (step : RufSchrittG program oracle passes M u M') {t : D.Tab} {k : Int} {f : D.Feld t}
    (change : AuthorityChange a layout M.speicher M'.speicher t k f) :
    ∃ span ∈ a.spans, span.table = t ∧ ImBereich D t k ∧
      TraegerSchreibt (M.faeden u).kopf.f (.inl t) = true := by
  obtain ⟨span, member, table, extent, _⟩ :=
    authority_change_cell (rufSchrittG_aussen foreign step) correct realizes change
  have moved : ¬ TraegerGleich M'.speicher M.speicher (.inl t) := fun same => by
    have slots : M'.speicher.slots t = M.speicher.slots t := same
    exact change.1 (congrFun (congrFun slots k) f)
  exact ⟨span, member, table, extent,
    (schritt_zugriffe good memory init reach step (.inl t)).2 (Or.inr moved)⟩

end Gabbro.Grammatik.LowLevel
