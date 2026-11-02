module

public import Grammatik.Bausteine.Kernzelle.Zulassung

@[expose] public section



namespace Gabbro.Grammatik.Kernzelle

open Gabbro.Grammatik Gabbro.Grammatik.Isabelle.AccumulatesMonoid

/-! ## 1. A concrete two-cell declaration -/

/-- The witness declaration universe: ten globals, four locks, six functions. -/
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
  Ax := Empty
  aparams := fun e => (nomatch e)
  aerg := fun e => (nomatch e)
  aschreibt := fun e => (nomatch e)
  agschreibt := fun e => (nomatch e)
  Reg := Empty
  rtyp := fun e => (nomatch e)
  rklasse := fun e => (nomatch e)
  spiegel := fun e => (nomatch e)
  rzusage := fun e => (nomatch e)
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => (nomatch t)
  invarianten_gehalten := fun _ i _ => (nomatch i)
  ggeteilt_bewacht := fun _ h => (nomatch h)

instance : DecidableEq zD.Fn := inferInstanceAs (DecidableEq (Fin 6))
instance : DecidableEq zD.Glob := inferInstanceAs (DecidableEq (Fin 10))
instance : DecidableEq zD.Lock := inferInstanceAs (DecidableEq (Fin 4))

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
theorem zMax_okB : akkuOkB zMax = true := by decide

/-- The unsigned `or` descriptor is valid, decided. -/
theorem zOr_okB : akkuOkB zOr = true := by decide

/-- The descriptors are valid. -/
theorem zMax_ok : akkuOk zD zMax := (akkuOkB_iff).mpr zMax_okB

theorem zOr_ok : akkuOk zD zOr := (akkuOkB_iff).mpr zOr_okB

/-- The neutral elements: signed `max` starts at the floor, unsigned `or` at zero. -/
theorem zMax_neutral : neutralInt zMax.op zMax.lo zMax.hi zMax.breite = -100 := rfl

theorem zOr_neutral : neutralInt zOr.op zOr.lo zOr.hi zOr.breite = 0 := rfl

/-! ## 2. Folds on two cells -/

/-- Folding two signed `max` cells. -/
theorem maxFalte_zeuge :
    (faltet (maxZahlMonoid (-100) 50 (by omega))
      [⟨30, by omega, by omega⟩, ⟨70, by omega, by omega⟩]).n = 70 := rfl

/-- Folding two signed `min` cells, from the ceiling. -/
theorem minFalte_zeuge :
    (faltet (minZahlMonoid (-100) 100 (by omega))
      [⟨30, by omega, by omega⟩, ⟨70, by omega, by omega⟩]).n = 30 := rfl

/-- The checked-addition chain on `[3, -1, 5]`. -/
theorem addKette_zeuge : rmwKette addIntMonoid 0 [3, -1, 5] = 7 := rfl

/-- Folding two `or` patterns. -/
theorem orFalte_zeuge : faltet orNatMonoid [5, 3] = 7 := rfl

/-- Folding two `and` patterns below `2 ^ 8`. -/
theorem andFalte_zeuge :
    (faltet (andMaskMonoid 8 (by omega)) [⟨12, by omega⟩, ⟨10, by omega⟩]).val = 8 := rfl

/-- Under quiescence the sampled `max` fold is the contribution fold and the RMW chain. -/
theorem ruhigMax_zeuge :
    faltet (maxZahlMonoid (-100) 100 (by omega))
        [faltet (maxZahlMonoid (-100) 100 (by omega)) [⟨30, by omega, by omega⟩, ⟨70, by omega, by omega⟩],
         faltet (maxZahlMonoid (-100) 100 (by omega)) [⟨-10, by omega, by omega⟩]] =
      faltet (maxZahlMonoid (-100) 100 (by omega))
        [⟨30, by omega, by omega⟩, ⟨70, by omega, by omega⟩, ⟨-10, by omega, by omega⟩] ∧
    faltet (maxZahlMonoid (-100) 100 (by omega))
        [faltet (maxZahlMonoid (-100) 100 (by omega)) [⟨30, by omega, by omega⟩, ⟨70, by omega, by omega⟩],
         faltet (maxZahlMonoid (-100) 100 (by omega)) [⟨-10, by omega, by omega⟩]] =
      rmwKette (maxZahlMonoid (-100) 100 (by omega))
        (maxZahlMonoid (-100) 100 (by omega)).neutral
        [⟨30, by omega, by omega⟩, ⟨70, by omega, by omega⟩, ⟨-10, by omega, by omega⟩] := by
  have hM := maxZahlMonoid (-100) 100 (by omega)
  exact ruhigFalte hM _ _ rfl

/-- Permuting `[1, 2, 3]` preserves the checked-addition outcome under the prefix duty. -/
theorem addVertauschung_zeuge :
    rmwKette addIntMonoid 0 [1, 2, 3] = rmwKette addIntMonoid 0 [3, 2, 1] := by
  have hp : IsPerm [1, 2, 3] [3, 2, 1] :=
    (.swap 1 2 [3]).trans ((.cons 2 (.swap 1 3 [])).trans (.swap 2 3 [1]))
  have hx : addKetteOk (-100) 100 0 [1, 2, 3] :=
    ⟨by omega, by omega, by omega, by omega,
     ⟨by omega, by omega, by omega, by omega,
      ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩⟩⟩⟩
  have hy : addKetteOk (-100) 100 0 [3, 2, 1] :=
    ⟨by omega, by omega, by omega, by omega,
     ⟨by omega, by omega, by omega, by omega,
      ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩⟩⟩⟩
  exact addVertauschungImBereich hp hx hy

/-! ## 3. Negative twins: what the schema refuses -/

/-- `N = 0` is refused. -/
def zN0 : AccumulatorDecl zD where
  name := "leer"
  kernZahl := 0
  breite := 8
  vorzeichen := true
  lo := -100
  hi := 50
  op := .max
  zellen := fun _ => ⟨0, by omega⟩
  sperren := fun _ => ⟨0, by omega⟩
  kernAbfrage := ⟨0, by omega⟩
  aktualisiere := ⟨1, by omega⟩
  falte := ⟨2, by omega⟩

theorem zN0_abgelehnt : akkuOkB zN0 = false := by decide

/-- A range too wide for the width is refused. -/
theorem zBreit_abgelehnt : akkuBreitePasstB true 0 200 8 = false := by decide

/-- An `and` range lacking the all-ones neutral is refused. -/
theorem zUndNeutral_abgelehnt : akkuGueltigB .and 0 100 8 = false := by decide

/-- The named trap: `min` started at `0` drags every result to `0`. -/
theorem minFalle_zeuge : min (50 : Int) 0 = 0 := minStartBeiNullFalle 50 (by decide)

/-- The named trap: `and` started at `0` drags every result to `0`. -/
theorem andFalle_zeuge : 12 &&& 0 = 0 := andStartBeiNullFalle 12

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
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => nomatch t
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

instance : DecidableEq zAD.Fn := inferInstanceAs (DecidableEq ZAFn)

def zAQ : zAD.Fn := .q
def zAU : zAD.Fn := .u
def zAF : zAD.Fn := .f

/-- Literal `0` in `0 .. 1`: the query answer. -/
def zALitQ {Γ : Ctx} {Λ : List (Res zAD)} : Expr zAD Γ Λ (Ty.int 0 1) :=
  .widen (by decide) (by decide) (.lit 0)

/-- Literal `0` in `0 .. 255`: the `or` neutral the reduction returns. -/
def zALitN {Γ : Ctx} {Λ : List (Res zAD)} : Expr zAD Γ Λ (Ty.int 0 255) :=
  .widen (by decide) (by decide) (.lit 0)

/-- The query body: return `0`. -/
def zARumpfQ : Endblock zAD (vertragVon zAD zAQ) false [] [] :=
  .ret (.val zALitQ) (List.Perm.refl _)

/-- The reduction body: return the neutral `0` (read-only, hence admitted;
    the sampled fold it should return is the quiescent leg, not admission). -/
def zARumpfF : Endblock zAD (vertragVon zAD zAF) false [] [] :=
  .ret (.val zALitN) (List.Perm.refl _)

/-- The update body: call the query, then return (no value). The call edge is
    what `reachB` needs; the callee writes nothing and takes no lock. -/
def zARumpfU : Endblock zAD (vertragVon zAD zAU) false [Ty.int 0 255] [] :=
  .bindCall zAQ Args.nil rfl
    { hw := fun t _ => nomatch t, hg := fun g h => by simp at h, hk := ⟨[], List.Perm.refl _, by simp only [List.nil_sublist]⟩, hh := fun L h => absurd h (List.not_mem_nil _) } rfl
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

def zACs : List (zAD.Tab ⊕ zAD.Glob) := [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩]

theorem zAFs_voll : ∀ g : zAD.Fn, g ∈ zAFs := fun g => by cases g <;> simp only [zAFs, List.mem_cons,
  List.not_mem_nil, List.mem_singleton]

theorem zACs_voll : ∀ c : zAD.Tab ⊕ zAD.Glob, c ∈ zACs := fun c => by
  cases c with
  | inl t => exact nomatch t
  | inr g => fin_cases g <;> simp only [zACs, List.mem_cons, List.not_mem_nil, List.mem_singleton]

/-- The fixture descriptor is valid, decided. -/
theorem zA_okB : akkuOkB zA = true := by decide

/-- The fixture descriptor is valid. -/
theorem zA_ok : akkuOk zAD zA := (akkuOkB_iff).mpr zA_okB

/-- The two cells are distinct and the neutral is `0`: non-degenerate. -/
theorem zA_nichtEntartet : zA.zellen ⟨0, by decide⟩ ≠ zA.zellen ⟨1, by decide⟩ ∧
    neutralInt zA.op zA.lo zA.hi zA.breite = 0 := by
  refine ⟨by decide, rfl⟩

/-- **The full-program admission, decided**: every clause of `akkuZulaessig`
    plus global cell/lock distinctness holds on the fixture. -/
theorem zA_akkuB : accumulatorB zAP zAFs zACs [zA] = true := by decide

/-- **The full-program admission `_zeuge`**: the fixture's accumulator is
    admitted (non-degenerate: two distinct cells, `or` with neutral `0`). -/
theorem akkuProgramm_zeuge : AccumulatorAdmission zAP zAFs [zA] :=
  (accumulatorB_iff zAFs_voll zACs_voll).mp zA_akkuB

#print axioms Gabbro.Grammatik.Kernzelle.zA_ok
#print axioms Gabbro.Grammatik.Kernzelle.zA_nichtEntartet
#print axioms Gabbro.Grammatik.Kernzelle.akkuProgramm_zeuge

#print axioms Gabbro.Grammatik.Kernzelle.zMax_ok
#print axioms Gabbro.Grammatik.Kernzelle.zOr_ok
#print axioms Gabbro.Grammatik.Kernzelle.maxFalte_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.minFalte_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.addKette_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.orFalte_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.andFalte_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.ruhigMax_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.addVertauschung_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.zN0_abgelehnt
#print axioms Gabbro.Grammatik.Kernzelle.zBreit_abgelehnt
#print axioms Gabbro.Grammatik.Kernzelle.zUndNeutral_abgelehnt
#print axioms Gabbro.Grammatik.Kernzelle.minFalle_zeuge
#print axioms Gabbro.Grammatik.Kernzelle.andFalle_zeuge

end Gabbro.Grammatik.Kernzelle
