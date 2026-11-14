module

public import Grammatik.Niedrig.Authority.NoBypassSaetze
public import Grammatik.Niedrig.Witnesses.SimG

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Witness

/-!
Witnesses of R3 on the joint fixture: the transition `inertMachine` → `writtenMachine` of thread 0
(Witnesses/SimG.lean) changes cell `((), 0, ())` from 0 to 1, whose byte `(0, 100)` lies in the
`ram` span. These endpoints are not claimed to be an executable G step; the step and run forms
(`storeSlot_only_via_view`, `kein_umweg`, `authority_writer_declared`) add only that premise.
-/

/-- A location outside every span of the authority. -/
def forged : Address space := ⟨⟨50, by omega, by change (50 : Int) ≤ 2 ^ 8 - 1; omega⟩⟩

/-- A forged location used as the index of a view is refused, by evaluation. -/
theorem forged_location_zeuge :
    ram_view authority initial forged 1 readWriteRights OwnerWitness.child = .error .bounds :=
  rfl

/-- The same refusal from the general theorem, whose premise holds on the fixture. -/
theorem forged_location_refused_zeuge :
    ram_view authority initial forged 1 readWriteRights OwnerWitness.child = .error .bounds :=
  forged_location_refused authority initial forged 1 readWriteRights OwnerWitness.child (by
    intro span member
    change span ∈ [ram, device] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · intro inside
      have low : 100 ≤ 50 := inside.2.1
      omega
    · intro inside
      have low : 108 ≤ 50 := inside.2.1
      omega)

theorem location_inert_zeuge :
    (evalAddress (.offset (.literal 100) 4 : AddressExpr space) (inertMachine.weltVon 0)).2 =
      inertMachine.weltVon 0 ∧
    ¬ SchreibG inertMachine inertMachine 0 (.inl ()) ∧
    ¬ AuthorityChange authority layout inertMachine.speicher inertMachine.speicher () 0 () := by
  have inert := location_inert (.offset (.literal 100) 4 : AddressExpr space) inertMachine 0
  exact ⟨inert.1, inert.2.2.1 _, inert.2.2.2 authority layout () 0 ()⟩

/-- Without a live view there is no write receipt, whatever region is held. -/
theorem no_view_receipt_zeuge :
    ∀ (w0 w1 : World D), ViewWrite authority initial layout w0 w1 → False :=
  fun _ _ receipt => (view_required receipt).2 rfl

/-! ## The written transition -/

theorem written_outside : AussenGleich inertMachine.speicher writtenMachine.speicher :=
  storeSlot_aussen before () 0 () write.value
    ⟨(by change (0 : Int) ≤ 0; omega), .inr (by change (0 : Int) < 1; omega)⟩

theorem written_change :
    writtenMachine.speicher.slots () 0 () ≠ inertMachine.speicher.slots () 0 () := by
  intro same
  have values : (writtenMachine.speicher.slots () 0 ()).n =
      (inertMachine.speicher.slots () 0 ()).n := by
    rw [same]
  have one : (writtenMachine.speicher.slots () 0 ()).n = 1 := rfl
  have zero : (inertMachine.speicher.slots () 0 ()).n = 0 := rfl
  omega

theorem written_touches : ram.Touches layout () 0 () :=
  ⟨(0, 100),
    ⟨rfl, by change 100 + 0 * 16 + 0 ≤ 100; omega,
      by change 100 < 100 + 0 * 16 + 0 + 1; omega⟩,
    ⟨rfl, by change 100 ≤ 100; omega, by change 100 < 100 + 8; omega⟩⟩

theorem written_authority_change :
    AuthorityChange authority layout inertMachine.speicher writtenMachine.speicher () 0 () :=
  ⟨written_change, ram, List.mem_cons_self .., written_touches⟩

theorem written_records :
    ((Sum.inl () : D.Tab ⊕ D.Glob), true) ∈ zugriffe inertMachine writtenMachine 0 := by
  have delta : (writtenMachine.faeden 0).spur =
      [Ereignis.zugriff () true writeResources before.haelt] ++
        (inertMachine.faeden 0).spur := rfl
  rw [zugriffe_ereignisse, ereignisse_eq delta]
  exact List.mem_cons_self ..

/-- The named premise holds jointly with a real authority-byte change. -/
theorem written_scope :
    ViewScopedStep authority layout writableResult.next inertMachine writtenMachine 0 :=
  { valid := ram_view_preserves initial_valid writableResult
    confined := by
      intro span member t k f table extent changed touch
      cases t
      refine ⟨writableView, List.mem_cons_self .., rfl, rfl, rfl, ?_, written_records⟩
      intro byte cell
      obtain ⟨low, high⟩ := extent
      have bound : k < 1 := by
        rcases high with opened | finite
        · cases opened
        · exact finite
      change byte.1 = 0 ∧ 100 + k.toNat * 16 + 0 ≤ byte.2 ∧
        byte.2 < 100 + k.toNat * 16 + 0 + 1 at cell
      change byte.1 = 0 ∧ 100 ≤ byte.2 ∧ byte.2 < 100 + 4
      have zero : k.toNat = 0 := by omega
      rw [zero] at cell
      exact ⟨cell.1, by omega, by omega⟩ }

/-- A write outside every live view is impossible: the same real change admits no view-scoped
    reading under the context without views. -/
theorem outside_views_zeuge :
    ¬ ViewScopedStep authority layout initial inertMachine writtenMachine 0 := by
  intro scope
  obtain ⟨view, live, _⟩ := scope.confined ram (List.mem_cons_self ..) () 0 () rfl
    ⟨(by change (0 : Int) ≤ 0; omega), .inr (by change (0 : Int) < 1; omega)⟩
    written_change written_touches
  cases live

/-- The core theorem on the fixture: the change goes through the live writable view, in extent,
    with its write event, and the cell's byte lies in the view and in the table. -/
theorem no_bypass_zeuge :
    ∃ view ∈ writableResult.next.views, view.Valid authority ∧ view.rights.write = true ∧
      view.span.table = () ∧ ImBereich D () 0 ∧
      (∃ (Λ : List (Res D)) (held : List D.Lock),
        Ereignis.zugriff () true Λ held ∈ ereignisse inertMachine writtenMachine 0) ∧
      ∀ byte, layout.inZelle () 0 () byte → view.Contains byte ∧ layout.inTabelle () byte := by
  obtain ⟨view, live, valid, _, writable, table, extent, event, _, _, bytes⟩ :=
    storeSlot_only_via_view_core written_outside layout_correct layout_realizes written_scope
      written_authority_change
  exact ⟨view, live, valid, writable, table, extent, event, bytes⟩

/-! ## Regions -/

/-- A region the live view does not have (another nominal space). -/
def otherRegion : DataCapTy :=
  { space := 1
    rights := readWriteRights
    target := .table 0 }

theorem otherRegion_unbacked :
    ∀ view ∈ writableResult.next.views, view.region ≠ otherRegion := by
  intro view member same
  change view ∈ [writableView] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  have spaces : (0 : Nat) = 1 := congrArg DataCapTy.space same
  omega

theorem region_forgets_bounds_zeuge :
    ({ writableView with
        base := 104
        length := 4 } : View D).region = writableView.region ∧
    (∀ (w0 w1 : World D) (receipt : ViewWrite authority writableResult.next layout w0 w1),
      receipt.view.region ≠ otherRegion) ∧
    ∃ view ∈ writableResult.next.views, view.region ≠ otherRegion ∧
      view.rights.write = true ∧ view.span.table = () := by
  have result := region_forgets_bounds otherRegion written_outside layout_correct
    layout_realizes written_scope otherRegion_unbacked
  exact ⟨result.1 writableView 104 4 writableView.lender writableView.borrower, result.2.1,
    result.2.2 () 0 () written_authority_change⟩

end Gabbro.Grammatik.LowLevel.Witness
