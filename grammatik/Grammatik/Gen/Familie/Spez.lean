/-
  File:      Grammatik/Gen/Familie/Spez.lean
  Subject:   The GENERATOR OF DECLARATIONS: a small specification (`Spez`, plain data: lists of tables with their
             fields, statics, locks with ranks, marks with stages, function signatures, functions, invariants,
             axioms, registers) and the declaration it denotes (`Spez.deklaration`), with the complete
             enumerations `Aufz` the program generator needs.

  Every field of `Deklaration` is read off the specification; the four PROOF fields of `Deklaration` hold BY
  CONSTRUCTION for every specification, so no specification is refused:
  * `eigner_nie_erzeugt` -- a function produces no mark that a table owns (the produced marks are filtered);
  * `geteilt_bewacht` / `ggeteilt_bewacht` -- a carrier is shared only if something guards it (the flag is
    conjoined with the guard);
  * `invarianten_gehalten` -- a function that writes a carrier of an invariant holds the locks of every carrier of
    that invariant (they are added to its held locks), the model's `U003` as an explanation.
-/
import Grammatik.Gen.Erzeuger.Gestuft

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

/-- The `n`-th element of a bounded index, if there is one. -/
def fin? (n i : Nat) : Option (Fin n) := if h : i < n then some ⟨i, h⟩ else none

theorem mem_fin? {n i : Nat} (h : i < n) : (⟨i, h⟩ : Fin n) ∈ (fin? n i).toList := by
  simp [fin?, h]

/-! ## The specification -/

/-- A field: its type and the transitions its `state` allows. -/
structure FeldZ where
  typ : Ty
  erlaubt : List (Int × Int) := []
  deriving DecidableEq, Repr

/-- A table: its `count`, its fields, the lock that `protects` it, the mark that `owner`s it. -/
structure TabZ where
  count : Int
  felder : List FeldZ
  sperre : Option Nat := none
  eigner : Option Nat := none
  geteilt : Bool := false
  geist : Bool := false
  /-- `table T open`: a region without an element ceiling (`Deklaration.offen`). -/
  offen : Bool := false
  deriving DecidableEq, Repr

/-- A static: its type, whether it is `atomic`, its guard (a lock or a mark with a stage), the payload it
    `publishes`. -/
structure GlobZ where
  typ : Ty
  atomar : Bool := false
  sperre : Option Nat := none
  marke : Option (Nat × Nat) := none
  nutzlast : List Nat := []
  geteilt : Bool := false
  geist : Bool := false
  deriving DecidableEq, Repr

/-- A lock: its rank and whether taking it masks interrupts. -/
structure LockZ where
  rang : Int
  maskiert : Bool := false
  deriving DecidableEq, Repr

/-- A function signature. -/
structure SigZ where
  params : List Ty := []
  erg : Option Ty := none
  gruende : Nat := 0
  haelt : List Nat := []
  schreibt : List Nat := []
  gschreibt : List Nat := []
  konsumiert : List (Nat × Nat) := []
  produziert : List (Nat × Nat) := []
  boden : Option Int := none
  deriving DecidableEq, Repr

/-- An invariant: the tables it ranges over. -/
structure InvZ where
  traeger : List Nat
  deriving DecidableEq, Repr

/-- A foreign body (`axiom`, `extern`, `syscall`, `asm`). -/
structure AxZ where
  params : List Ty := []
  erg : Option Ty := none
  gruende : Nat := 0
  schreibt : List Nat := []
  gschreibt : List Nat := []
  deriving DecidableEq, Repr

/-- A device register: its type, its class, the register it mirrors, the carriers its state lives in, the promise
    the device makes about the value read. -/
structure RegZ where
  typ : Ty
  klasse : Regklasse
  spiegel : Option Nat := none
  traeger : List Nat := []
  zusage : Bool := true
  deriving DecidableEq, Repr

/-- **The specification of a declaration.** -/
structure Spez where
  tabs : List TabZ := []
  globs : List GlobZ := []
  locks : List LockZ := []
  marken : List Nat := []
  sigs : List SigZ := [{}]
  fns : List Nat := [0]
  invs : List InvZ := []
  axs : List AxZ := []
  regs : List RegZ := []
  annahmen : Nat := 0
  deriving DecidableEq, Repr

namespace Spez

variable (z : Spez)

/-! ## The carriers of the declaration -/

/-- The lock that guards table `t`, and its owner mark. -/
def braucht (t : Fin z.tabs.length) : List (Fin z.locks.length ⊕ (Fin z.marken.length × Nat)) :=
  ((z.tabs.get t).sperre.bind (fin? z.locks.length)).toList.map Sum.inl ++
  ((z.tabs.get t).eigner.bind (fin? z.marken.length)).toList.map fun m => Sum.inr (m, 0)

/-- The owner marks of table `t`. -/
def eigner (t : Fin z.tabs.length) : List (Fin z.marken.length) :=
  ((z.tabs.get t).eigner.bind (fin? z.marken.length)).toList

/-- What an access to static `g` must hold. -/
def gbraucht (g : Fin z.globs.length) : List (Fin z.locks.length ⊕ (Fin z.marken.length × Nat)) :=
  ((z.globs.get g).sperre.bind (fin? z.locks.length)).toList.map Sum.inl ++
  ((z.globs.get g).marke.bind fun p => (fin? z.marken.length p.1).map fun m => (m, p.2)).toList.map Sum.inr

/-- A mark some table owns. -/
def istEigner (m : Fin z.marken.length) : Bool :=
  (List.finRange z.tabs.length).any fun t => decide (m ∈ z.eigner t)

/-- The tables of invariant `i`. -/
def traeger (i : Fin z.invs.length) : List (Fin z.tabs.length) :=
  ((z.invs.get i).traeger.filterMap (fin? z.tabs.length))

/-- The raw signature `n` (an empty signature for a number out of range). -/
def sigRoh (n : Nat) : SigZ := z.sigs.getD n {}

/-- Does signature `n` write table `t`? -/
def schreibt (n : Nat) (t : Fin z.tabs.length) : Bool := (z.sigRoh n).schreibt.contains t.val

/-- Does an access to table `t` need lock `L`? -/
def hatLock (t : Fin z.tabs.length) (L : Fin z.locks.length) : Bool :=
  (z.braucht t).any fun w => decide (w = Sum.inl L)

/-- Does signature `n` need lock `L` for an invariant it breaks (it writes a carrier of an invariant whose
    carriers `L` guards)? -/
def brauchtFuerInv (n : Nat) (L : Fin z.locks.length) : Bool :=
  (List.finRange z.invs.length).any fun i =>
    (z.traeger i).any (z.schreibt n) && (z.traeger i).any fun t => z.hatLock t L

/-- The locks signature `n` holds: the declared ones and those its invariants need. -/
def haelt (n : Nat) : List (Fin z.locks.length) :=
  (List.finRange z.locks.length).filter fun L => (z.sigRoh n).haelt.contains L.val || z.brauchtFuerInv n L

/-- The marks signature `n` produces: the declared ones, without those a table owns. -/
def produziert (n : Nat) : List (Fin z.marken.length × Nat) :=
  ((z.sigRoh n).produziert.filterMap fun p => (fin? z.marken.length p.1).map fun m => (m, p.2)).filter
    fun p => !(z.istEigner p.1)

/-- The signature `n` of the declaration. -/
def sigNr (n : Nat) : Signatur (Fin z.tabs.length) (Fin z.globs.length) (Fin z.locks.length)
    (Fin z.marken.length) where
  params := (z.sigRoh n).params
  erg := (z.sigRoh n).erg
  gruende := (z.sigRoh n).gruende
  haelt := z.haelt n
  schreibt := z.schreibt n
  gschreibt := fun g => (z.sigRoh n).gschreibt.contains g.val
  konsumiert := ((z.sigRoh n).konsumiert.filterMap fun p => (fin? z.marken.length p.1).map fun m => (m, p.2))
  produziert := z.produziert n
  boden := (z.sigRoh n).boden

theorem eigner_ok (n : Nat) (t : Fin z.tabs.length) (m : Fin z.marken.length) (s : Nat) (h : m ∈ z.eigner t) :
    (m, s) ∉ (z.sigNr n).produziert := by
  intro hm
  have hm' : (m, s) ∈ z.produziert n := hm
  unfold produziert at hm'
  have := (List.mem_filter.1 hm').2
  have hown : z.istEigner m = true := by
    unfold istEigner
    exact List.any_eq_true.2 ⟨t, List.mem_finRange t, decide_eq_true h⟩
  simp only [hown] at this
  exact absurd this (by simp)

theorem inv_ok (n : Nat) (i : Fin z.invs.length) (h : (z.traeger i).any (z.sigNr n).schreibt = true)
    (t : Fin z.tabs.length) (ht : t ∈ z.traeger i) (L : Fin z.locks.length) (hL : Sum.inl L ∈ z.braucht t) :
    L ∈ (z.sigNr n).haelt := by
  show L ∈ z.haelt n
  unfold haelt
  refine List.mem_filter.2 ⟨List.mem_finRange L, ?_⟩
  simp only [Bool.or_eq_true]
  right
  unfold brauchtFuerInv
  refine List.any_eq_true.2 ⟨i, List.mem_finRange i, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨h, List.any_eq_true.2 ⟨t, ht, ?_⟩⟩
  unfold hatLock
  exact List.any_eq_true.2 ⟨_, hL, decide_eq_true rfl⟩

/-- **The declaration of a specification.** -/
def deklaration : Deklaration where
  Tab := Fin z.tabs.length
  decTab := inferInstance
  count := fun t => (z.tabs.get t).count
  offen := fun t => (z.tabs.get t).offen
  Feld := fun t => Fin (z.tabs.get t).felder.length
  decFeld := fun _ => inferInstance
  typ := fun t f => ((z.tabs.get t).felder.get f).typ
  erlaubt := fun t f von nach => ((z.tabs.get t).felder.get f).erlaubt.contains (von, nach)
  tabNr := fun n => fin? z.tabs.length n
  Glob := Fin z.globs.length
  decGlob := inferInstance
  gtyp := fun g => (z.globs.get g).typ
  nutzlast := fun g => (z.globs.get g).nutzlast.filterMap (fin? z.globs.length)
  atomar := fun g => (z.globs.get g).atomar
  geteilt := fun t => (z.tabs.get t).geteilt && !(z.braucht t).isEmpty
  ggeteilt := fun g => (z.globs.get g).geteilt && (!(z.gbraucht g).isEmpty || (z.globs.get g).atomar)
  Lock := Fin z.locks.length
  decLock := inferInstance
  rang := fun L => (z.locks.get L).rang
  maskiert := fun L => (z.locks.get L).maskiert
  Marke := Fin z.marken.length
  decMarke := inferInstance
  stufen := fun m => z.marken.get m
  braucht := z.braucht
  gbraucht := z.gbraucht
  eigner := z.eigner
  Fn := Fin z.fns.length
  sig := fun f => z.fns.get f
  sigNr := z.sigNr
  eigner_nie_erzeugt := fun n t m s h => z.eigner_ok n t m s h
  Inv := Fin z.invs.length
  traeger := z.traeger
  invs := List.finRange z.invs.length
  Ax := Fin z.axs.length
  aparams := fun a => (z.axs.get a).params
  aerg := fun a => (z.axs.get a).erg
  aschreibt := fun a t => (z.axs.get a).schreibt.contains t.val
  agschreibt := fun a g => (z.axs.get a).gschreibt.contains g.val
  agruende := fun a => (z.axs.get a).gruende
  Reg := Fin z.regs.length
  rtyp := fun r => (z.regs.get r).typ
  rklasse := fun r => (z.regs.get r).klasse
  spiegel := fun r => ((z.regs.get r).spiegel.bind (fin? z.regs.length))
  rzusage := fun r _ => (z.regs.get r).zusage
  rtraeger := fun r => ((z.regs.get r).traeger.filterMap (fin? z.tabs.length)).map Sum.inl
  Annahme := Fin (z.annahmen + 1)
  a10 := 0
  geteilt_bewacht := fun t h => by
    intro hb
    simp only [hb, List.isEmpty_nil, Bool.not_true, Bool.and_false] at h
    exact absurd h (by simp)
  invarianten_gehalten := fun n i h t ht L hL => z.inv_ok n i h t ht L hL
  ggeteilt_bewacht := fun g h => by
    by_cases hb : z.gbraucht g = []
    · right
      simp only [hb, List.isEmpty_nil, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
      exact h.2
    · left; exact hb
  geist := fun t => (z.tabs.get t).geist
  ggeist := fun g => (z.globs.get g).geist

/-- **The complete enumerations of the declaration of a specification.** -/
instance aufz : Aufz z.deklaration where
  tab := List.finRange z.tabs.length
  tab_mem := fun t => List.mem_finRange t
  feld := fun t => List.finRange (z.tabs.get t).felder.length
  feld_mem := fun _ f => List.mem_finRange f
  glob := List.finRange z.globs.length
  glob_mem := fun g => List.mem_finRange g
  lock := List.finRange z.locks.length
  lock_mem := fun L => List.mem_finRange L
  marke := List.finRange z.marken.length
  marke_mem := fun m => List.mem_finRange m
  fn := List.finRange z.fns.length
  fn_mem := fun f => List.mem_finRange f
  inv := List.finRange z.invs.length
  inv_mem := fun i => List.mem_finRange i
  ax := List.finRange z.axs.length
  ax_mem := fun a => List.mem_finRange a
  reg := List.finRange z.regs.length
  reg_mem := fun r => List.mem_finRange r
  annahme := List.finRange (z.annahmen + 1)
  annahme_mem := fun a => List.mem_finRange a
  sigs := (List.finRange z.fns.length).map z.deklaration.sig
  sigs_mem := fun f n h => List.mem_map.2 ⟨f, List.mem_finRange f, of_decide_eq_true h⟩
  decFn := inferInstanceAs (DecidableEq (Fin z.fns.length))
  decInv := inferInstanceAs (DecidableEq (Fin z.invs.length))
  decAx := inferInstanceAs (DecidableEq (Fin z.axs.length))
  decReg := inferInstanceAs (DecidableEq (Fin z.regs.length))
  decAnnahme := inferInstanceAs (DecidableEq (Fin (z.annahmen + 1)))

end Spez

end Gabbro.Grammatik.Gen
