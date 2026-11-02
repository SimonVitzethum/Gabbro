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
theorem minFalle_zeuge : min (50 : Int) 0 = 0 := minStartBeiNullFalle 50

/-- The named trap: `and` started at `0` drags every result to `0`. -/
theorem andFalle_zeuge : 12 &&& 0 = 0 := andStartBeiNullFalle 12

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
