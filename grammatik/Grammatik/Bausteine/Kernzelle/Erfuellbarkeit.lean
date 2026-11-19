/-
  Subject: Satisfiability of the accumulator premises (stream E8, owner rule of 2026-11-19).

  `akku_erfuellbar`: a full program with one per-core `or` accumulator over two distinct cells is admitted
  (`AccumulatorAdmission`, connected core query), so the premises of the accumulator lemmas of `Kernzelle/` hold
  jointly on a non-degenerate declaration; `zMax_ok`/`zOr_ok` show `akkuOk` for a signed `max` and an unsigned
  `or` descriptor.
-/
module

public import Grammatik.Bausteine.Kernzelle.Zulassung

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

/-! ## 1. A concrete two-cell declaration -/

/-- The fixture declaration universe: ten globals, four locks, six functions. -/
def zD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => (nomatch t)
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun t _ => (nomatch t)
  erlaubt := fun t _ _ _ => (nomatch t)
  tabNr := fun _ => none
  Glob := Fin 10
  decGlob := inferInstance
  gtyp := fun g => if g.val < 2 then Ty.int (-100) 50
    else if g.val < 4 then Ty.int 0 255 else Ty.int 0 0
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => (nomatch t)
  ggeteilt := fun _ => false
  Lock := Fin 4
  decLock := inferInstance
  rang := fun l => (l.val : Int)
  maskiert := fun _ => true
  Marke := Unit
  decMarke := inferInstance
  stufen := fun _ => 0
  braucht := fun t => (nomatch t)
  gbraucht := fun g => [Sum.inl ⟨g.val % 4, Nat.mod_lt _ (by omega)⟩]
  eigner := fun _ => []
  Fn := Fin 6
  sig := fun f => f.val
  sigNr
    | 0 => { params := [], erg := some (Ty.int 0 1), gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => false, konsumiert := [], produziert := [], boden := none }
    | 1 => { params := [Ty.int (-100) 50], erg := none, gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => true, konsumiert := [], produziert := [], boden := none }
    | 2 => { params := [], erg := some (Ty.int (-100) 50), gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => false, konsumiert := [], produziert := [], boden := none }
    | 3 => { params := [], erg := some (Ty.int 0 1), gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => false, konsumiert := [], produziert := [], boden := none }
    | 4 => { params := [Ty.int 0 255], erg := none, gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => true, konsumiert := [], produziert := [], boden := none }
    | 5 => { params := [], erg := some (Ty.int 0 255), gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => false, konsumiert := [], produziert := [], boden := none }
    | _ => { params := [], erg := none, gruende := 0, haelt := [], schreibt := fun t => (nomatch t), gschreibt := fun _ => false, konsumiert := [], produziert := [], boden := none }
  eigner_nie_erzeugt := fun _ _ _ _ h => (nomatch h)
  Inv := Empty
  traeger := fun i => (nomatch i)
  invs := []
  Ax := Fin 1
  aparams := fun _ => []
  aerg := fun _ => some (Ty.int 0 1)
  aschreibt := fun _ t => nomatch t
  agschreibt := fun _ _ => false
  agruende := fun _ => 0
  Reg := Empty
  rtyp := fun e => (nomatch e)
  rklasse := fun e => (nomatch e)
  spiegel := fun e => (nomatch e)
  rzusage := fun e => (nomatch e)
  axHerkunft := fun _ => some .hardware
  axBeleg := fun _ => some ()
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => (nomatch t)
  invarianten_gehalten := fun _ i _ => (nomatch i)
  ggeteilt_bewacht := fun _ h => (nomatch h)

instance : DecidableEq zD.Fn := inferInstanceAs (DecidableEq (Fin 6))
instance : DecidableEq zD.Glob := inferInstanceAs (DecidableEq (Fin 10))
instance : DecidableEq zD.Lock := inferInstanceAs (DecidableEq (Fin 4))
instance : DecidableEq zD.Ax := inferInstanceAs (DecidableEq (Fin 1))

/-- A signed `max` accumulator over two cells. -/
def zMax : AccumulatorDecl zD where
  name := "hoechst"
  kernZahl := 2
  breite := 8
  vorzeichen := true
  lo := -100
  hi := 50
  op := .max
  zellen := fun i => ⟨i.val, by have := i.isLt; omega⟩
  sperren := fun i => ⟨i.val, by have := i.isLt; omega⟩
  kernAbfrage := ⟨0, by omega⟩
  aktualisiere := ⟨1, by omega⟩
  falte := ⟨2, by omega⟩

/-- An unsigned bitwise-`or` accumulator over two cells. -/
def zOr : AccumulatorDecl zD where
  name := "maske"
  kernZahl := 2
  breite := 8
  vorzeichen := false
  lo := 0
  hi := 255
  op := .or
  zellen := fun i => ⟨2 + i.val, by have := i.isLt; omega⟩
  sperren := fun i => ⟨2 + i.val, by have := i.isLt; omega⟩
  kernAbfrage := ⟨3, by omega⟩
  aktualisiere := ⟨4, by omega⟩
  falte := ⟨5, by omega⟩

/-- The signed `max` descriptor is valid, decided. -/
theorem zMax_okB : akkuOkB zMax = true := by decide +kernel

/-- The unsigned `or` descriptor is valid, decided. -/
theorem zOr_okB : akkuOkB zOr = true := by decide +kernel

/-- The descriptors are valid. -/
theorem zMax_ok : akkuOk zD zMax := (akkuOkB_iff).mp zMax_okB

theorem zOr_ok : akkuOk zD zOr := (akkuOkB_iff).mp zOr_okB

/-- The neutral elements: signed `max` starts at the floor, unsigned `or` at zero. -/
theorem zMax_neutral : neutralInt zMax.op zMax.lo zMax.hi zMax.breite = -100 := rfl

theorem zOr_neutral : neutralInt zOr.op zOr.lo zOr.hi zOr.breite = 0 := rfl

/-! ## 4. A full-program fixture: two `or` cells, admitted -/

/-- The three generated functions: query, update, reduction. -/
inductive ZAFn
  | q
  | u
  | f
  deriving DecidableEq, Repr

/-- One signature: parameters, result, no reasons, no locks, no writes, no floor. -/
def zASig (ps : List Ty) (e : Option Ty) : Signatur Empty (Fin 2) (Fin 2) Empty where
  params := ps
  erg := e
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []
  boden := none
  owner := {}

def zASigNr : Nat → Signatur Empty (Fin 2) (Fin 2) Empty
  | 0 => zASig [] (some (Ty.int 0 1))
  | 1 => zASig [Ty.int 0 255] none
  | 2 => zASig [] (some (Ty.int 0 255))
  | _ => zASig [] none

def zASigOf : ZAFn → Nat
  | .q => 0
  | .u => 1
  | .f => 2

/-- The fixture declaration: two `or` cells over `0 .. 255`, guarded 1:1. -/
def zAD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => nomatch t
  Feld := fun t => nomatch t
  decFeld := fun t => nomatch t
  typ := fun t => nomatch t
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Fin 2
  decGlob := inferInstance
  gtyp := fun _ => Ty.int 0 255
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => nomatch t
  ggeteilt := fun _ => false
  Lock := Fin 2
  decLock := inferInstance
  rang := fun l => (l.val : Int)
  maskiert := fun _ => true
  Marke := Empty
  decMarke := inferInstance
  stufen := fun _ => 0
  braucht := fun t => nomatch t
  gbraucht := fun g => [Sum.inl ⟨g.val, g.isLt⟩]
  eigner := fun _ => []
  Fn := ZAFn
  sig := zASigOf
  sigNr := zASigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Fin 1
  aparams := fun _ => []
  aerg := fun _ => some (Ty.int 0 1)
  aschreibt := fun _ t => nomatch t
  agschreibt := fun _ _ => false
  agruende := fun _ => 0
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by cases h
  axHerkunft := fun _ => some .hardware
  axBeleg := fun _ => some ()

instance : DecidableEq zAD.Fn := inferInstanceAs (DecidableEq ZAFn)
instance : DecidableEq zAD.Ax := inferInstanceAs (DecidableEq (Fin 1))

def zAQ : zAD.Fn := .q
def zAU : zAD.Fn := .u
def zAF : zAD.Fn := .f

/-- The hardware core-query axiom. -/
def zAX : zAD.Ax := ⟨0, by decide⟩

/-- Literal `0` in `0 .. 255`: the `or` neutral the reduction returns. -/
def zALitN {Γ : Ctx} {Λ : List (Res zAD)} : Expr zAD Γ Λ (Ty.int 0 255) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The query body: bind the hardware axiom, return its answer. -/
def zARumpfQ : Endblock zAD (vertragVon zAD zAQ) false [] [] :=
  .bindAxiom (τ := Ty.int 0 1) zAX Args.nil (by rfl)
    (fun t _ => nomatch t) (fun _ h => by cases h)
    (fun t _ => nomatch t) (fun _ h => by cases h)
    (.ret (.val (.var .here)) (List.Perm.refl _))

/-- The reduction body: return the neutral `0` (read-only, hence admitted;
    the sampled fold it should return is the quiescent leg, not admission). -/
def zARumpfF : Endblock zAD (vertragVon zAD zAF) false [] [] :=
  .ret (.val zALitN) (List.Perm.refl _)

/-- The update body: call the query, then return (no value). The call edge is
    what `reachB` needs; the callee writes nothing and takes no lock. -/
def zARumpfU : Endblock zAD (vertragVon zAD zAU) false [Ty.int 0 255] [] :=
  .bindCall (τ := Ty.int 0 1) zAQ Args.nil (by rfl)
    { hw := fun t _ => nomatch t
      hg := fun _ h => by cases h
      hk := ⟨[], List.Perm.refl _, List.nil_sublist _⟩
      hh := fun _ h => by cases h
      ownerReady := OwnerFlow.escrowReady_of_empty _ _ _ _ rfl } (by rfl)
    (.ret .empty (List.Perm.refl _))

/-- The fixture program: trivial bodies, no contracts. -/
def zAP : Programm zAD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf
    | .q => zARumpfQ
    | .u => zARumpfU
    | .f => zARumpfF

/-- The fixture accumulator: two unsigned `or` cells. -/
def zA : AccumulatorDecl zAD where
  name := "maske"
  kernZahl := 2
  breite := 8
  vorzeichen := false
  lo := 0
  hi := 255
  op := .or
  zellen := fun i => ⟨i.val, i.isLt⟩
  sperren := fun i => ⟨i.val, i.isLt⟩
  kernAbfrage := zAQ
  aktualisiere := zAU
  falte := zAF

def zAFs : List zAD.Fn := [zAQ, zAU, zAF]

def zATabs : List zAD.Tab := []

def zAGlobs : List zAD.Glob := [⟨0, by decide⟩, ⟨1, by decide⟩]

def zAQs : List zAD.Ax := [zAX]

theorem zAFs_voll : ∀ g : zAD.Fn, g ∈ zAFs := by
  intro g
  cases g <;> (simp only [zAFs, zAQ, zAU, zAF]; first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem zATabs_voll : ∀ t : zAD.Tab, t ∈ zATabs := fun t => nomatch t

theorem zAGlobs_voll : ∀ g : zAD.Glob, g ∈ zAGlobs := by
  intro ⟨n, hn⟩
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with rfl | rfl <;> (simp only [zAGlobs]; first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ List.mem_cons_self | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The fixture descriptor is valid, decided. -/
theorem zA_okB : akkuOkB zA = true := by decide +kernel

/-- The fixture descriptor is valid. -/
theorem zA_ok : akkuOk zAD zA := (akkuOkB_iff).mp zA_okB

/-- The two cells are distinct and the neutral is `0`: non-degenerate. -/
theorem zA_nichtEntartet : zA.zellen ⟨0, by decide⟩ ≠ zA.zellen ⟨1, by decide⟩ ∧
    neutralInt zA.op zA.lo zA.hi zA.breite = 0 := by
  refine ⟨by decide, rfl⟩

/-- **The full-program admission, decided**: every clause of `akkuZulaessig`
    plus global cell/lock distinctness holds on the fixture, with the
    connected hardware query listed. -/
theorem zA_akkuB : accumulatorB zAP zAFs zATabs zAGlobs zAQs [zA] = true := by decide +kernel

/-- **Satisfiability of the accumulator premises**: the fixture's accumulator is admitted, its core query is
    connected, and its two cells are distinct. -/
theorem akku_erfuellbar : AccumulatorAdmission zAP zAFs [zA] ∧
    (∀ a ∈ [zA], ∃ q ∈ zAQs, KernAbfrageVerbunden zAP a q) ∧
    zA.zellen ⟨0, by decide⟩ ≠ zA.zellen ⟨1, by decide⟩ :=
  have h := (accumulatorB_iff zAFs_voll zATabs_voll zAGlobs_voll).mp zA_akkuB
  ⟨h.1, h.2, zA_nichtEntartet.1⟩

end Gabbro.Grammatik.Kernzelle
