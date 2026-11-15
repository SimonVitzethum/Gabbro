module

public import Grammatik.Logik.Vertraege.Pruefer.Goal
public import Grammatik.Logik.Invarianten.Frag.Witness

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.Witness

open Invarianten.Frag Zielsatz

/-- One real function, an input whose upper endpoint is excluded by requires,
    a non-singleton result, and ordinary memory in the declaration. -/
abbrev declaration : Deklaration :=
  { Invarianten.Frag.Witness.declaration with
    Fn := Unit
    sig := fun _ => 0
    sigNr := fun _ =>
      { params := [.int 0 10], erg := some (.int 1 11), gruende := 0
        haelt := [], schreibt := fun _ => false, gschreibt := fun _ => false
        konsumiert := [], produziert := [] }
    passt := fun _ _ => false
    passt_ok := fun _ _ impossible => by cases impossible
    rzusage := fun item => nomatch item
    Inv := Empty
    traeger := fun item => nomatch item
    invs := []
    invarianten_gehalten := fun _ item => nomatch item }

abbrev contract := vertragVon declaration ()

def increment : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .lt (.var .here) (.lit 10)
  ensures := fun _ => .eq (.var .here) (.add (.var (.there .here)) (.lit 1))
  rumpf := fun _ => .ret (.val (.add (.var .here) (.lit 1))) (List.Perm.refl _)

def falseEnsures : Programm declaration :=
  { increment with ensures := fun _ => .eq (.var .here) (.add (.var (.there .here)) (.lit 2)) }

def world : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def arguments : Env declaration (declaration.params ()) := .cons ⟨4, by decide, by decide⟩ .nil

def unit : Einheit declaration where
  P := increment
  S := SperrInv.leer declaration
  Q := fun item => nomatch item
  starts := [⟨(), arguments⟩]
  sp0 := world.speicher
  axiomSources := some
    { items := []
      complete := fun item => nomatch item
      resources := fun item => nomatch item
      expression := fun item => nomatch item
      correct := fun item => nomatch item }
  pointerSignatures := some
    { count := 0, outside := fun _ _ _ => rfl }

def falseUnit : Einheit declaration := { unit with P := falseEnsures }

end Gabbro.Grammatik.Vertraege.Pruefer.Witness
