module

public import Grammatik.Niedrig.Konstrukte.System.Basis
public import Grammatik.Niedrig.Uebersetzung.Tabelle

@[expose] public section

namespace Gabbro.Grammatik.LowLevel.Construct

open Niedrig

variable {D : Deklaration}

/-- Named hardware boundary: a translation unit answers according to the
    installed tables. Proving a table or synchronization protocol is software
    logic, not part of this assumption. The actual observation is a parameter. -/
def Mmu (regime : Uebersetzung.Regime) (tables : Uebersetzung.Tables)
    (observed : Nat → Nat → Option (Nat × Uebersetzung.Perm)) : Prop :=
  ∀ root address, observed root address = Uebersetzung.walk regime tables root address

structure NamedMmu (names : SystemAssumptions D) (item : D.Ax)
    (regime : Uebersetzung.Regime) (tables : Uebersetzung.Tables)
    (observed : Nat → Nat → Option (Nat × Uebersetzung.Perm)) : Prop where
  origin : CtxOriginOk item
  named : D.axBeleg item = some names.Mmu
  hardware : Mmu regime tables observed

/-- Installing/switching a root is the SAME target-binding operation. The
    root is an abstract table identity, never an integer-to-pointer cast.
    No views may survive a root switch. Kernel software proves root validity
    and cache synchronization before supplying their finite checked flags. -/
def MmuInstallOk (c : SystemContext D) (roots : List Nat) (root : Nat)
    (rootReady cacheSynchronized : Bool) : Prop :=
  c.privilege.priv = .kern ∧ c.views = [] ∧ root ∈ roots ∧
  rootReady = true ∧ cacheSynchronized = true

instance (c : SystemContext D) (roots : List Nat) (root : Nat) (ready sync : Bool) :
    Decidable (MmuInstallOk c roots root ready sync) := by
  unfold MmuInstallOk
  infer_instance

def mmuInstallB (c : SystemContext D) (roots : List Nat) (root : Nat) (ready sync : Bool) : Bool :=
  decide (MmuInstallOk c roots root ready sync)

theorem mmuInstallB_iff (c : SystemContext D) (roots : List Nat) (root : Nat) (ready sync : Bool) :
    mmuInstallB c roots root ready sync = true ↔ MmuInstallOk c roots root ready sync := by
  simp only [mmuInstallB, decide_eq_true_eq]

/-- The flags above are certificates, not arbitrary trusted booleans: the
    checked contract must establish the semantic predicates behind them. -/
structure MmuInstallDuty (ready sync : Bool) (rootValid synchronization : Prop) : Prop where
  readySound : ready = true → rootValid
  syncSound : sync = true → synchronization

def mmuInstallStep (c : SystemContext D) (roots : List Nat) (root : Nat) (ready sync : Bool)
    (_checked : MmuInstallOk c roots root ready sync) (world : World D) : SystemContext D × World D :=
  systemMetadataStep c { c.privilege with wurzel := root } c.interrupt world

theorem mmuInstallStep_arch (c : SystemContext D) (roots : List Nat) (root : Nat) (ready sync : Bool)
    (checked : MmuInstallOk c roots root ready sync) (world : World D) :
    Arch.ArchStep (.setRoot root) c.privilege (mmuInstallStep c roots root ready sync checked world).1.privilege :=
  .wurzel c.privilege root checked.1

theorem mmuInstallStep_root (c : SystemContext D) (roots : List Nat) (root : Nat) (ready sync : Bool)
    (checked : MmuInstallOk c roots root ready sync) (world : World D) :
    (mmuInstallStep c roots root ready sync checked world).1.privilege.wurzel = root ∧
    (mmuInstallStep c roots root ready sync checked world).1.privilege.kern = c.privilege.kern ∧
    (mmuInstallStep c roots root ready sync checked world).2 = world := ⟨rfl, rfl, rfl⟩

theorem mmuInstallStep_translation {c : SystemContext D} {roots : List Nat} {root : Nat}
    {ready sync : Bool} (checked : MmuInstallOk c roots root ready sync) (world : World D)
    {regime : Uebersetzung.Regime} {tables : Uebersetzung.Tables}
    {observed : Nat → Nat → Option (Nat × Uebersetzung.Perm)} (hardware : Mmu regime tables observed)
    (address : Nat) :
    observed (mmuInstallStep c roots root ready sync checked world).1.privilege.wurzel address =
      Uebersetzung.walk regime tables root address := hardware root address

theorem mmuInstallStep_sim {a : Authority D} {layout : AdressLayout D} {c : SystemContext D}
    {world : World D} (simulation : ClassSimRel a layout c world) (roots : List Nat)
    (root : Nat) (ready sync : Bool) (checked : MmuInstallOk c roots root ready sync) :
    ClassSimRel a layout (mmuInstallStep c roots root ready sync checked world).1
      (mmuInstallStep c roots root ready sync checked world).2 :=
  systemMetadataStep_sim simulation _ _

/-- Page-table changes are ordinary typed writes through RAM views. Root and
    entry indices describe the existing abstract Tables; no second store is
    substituted for G's store. Encoding/correspondence is a software obligation. -/
def pageTablePutStep (view : View D) (layout : AdressLayout D)
    (field : D.Feld view.span.table) (index : Int) (value : Wert D (D.typ view.span.table field))
    (resources : List (Res D)) (writes : D.Tab → Bool)
    (checked : ViewPutOk view layout field index resources writes)
    (_ram : view.span.memoryClass = .ordinaryRam) (world : World D) : World D :=
  viewPutStep view layout field index value resources writes checked world

/-- The user proves the encoding against the SAME store. This premise is
    deliberately exposed: setting a mathematical table alone changes no RAM. -/
def PageTableEncodingDuty (projection : World D → Uebersetzung.Tables)
    (before after : World D) (table index : Nat) (entry : Uebersetzung.Entry) : Prop :=
  projection after = Uebersetzung.setEntry (projection before) table index entry

theorem pageTablePutStep_hit {projection : World D → Uebersetzung.Tables}
    {before after : World D} {table index : Nat} {entry : Uebersetzung.Entry}
    (encoding : PageTableEncodingDuty projection before after table index entry) :
    projection after table index = entry := by
  rw [encoding]
  exact Uebersetzung.setEntry_hit _ _ _ _

theorem pageTablePutStep_other {projection : World D → Uebersetzung.Tables}
    {before after : World D} {table index : Nat} {entry : Uebersetzung.Entry}
    (encoding : PageTableEncodingDuty projection before after table index entry)
    (other slot : Nat) (different : other ≠ table) :
    projection after other slot = projection before other slot := by
  rw [encoding]
  exact Uebersetzung.setEntry_miss_table _ _ _ _ _ _ different

end Gabbro.Grammatik.LowLevel.Construct
