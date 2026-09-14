/-
  File:      Grammatik/Nichtinterferenz/Korpus.lean
  Subject:   THE FLOW CONDITION ON THE CORPUS PROGRAMS THAT EXIST IN LEAN --
             a measurement, by `decide`, of what the plain rule admits and
             refuses under a natural two-domain split.

  Four corpus programs have a Lean form: the mechanical exports of
  `beispiele/104-referenz.gab` (`Export104.lean`),
  `beispiele/108-disjoint-start-locks.gab` (`Export108.lean`),
  `beispiele/118-sperrinvariante-erhaltung.gab` (`ExportSperre.lean`), and
  the hand model of `beispiele/124-two-threads-private.gab`
  (`MehrfadenZeuge.lean`, the same tables and functions). The split is the
  natural one: each root function its own tenant domain (`A`, `B`), each
  carrier labelled with the tenant that owns it, a carrier touched by both
  labelled every way there is.

  Result: 108 (two readers of disjoint tables) is ADMITTED. 104, 118 and 124
  are REFUSED under EVERY label of their shared carrier: in each, both roots
  WRITE one shared carrier (or one writes what the other reads). That is
  interference in the sense of the theorem -- one root's activity is
  visible to the other through the shared state -- even where no tenant
  data flows (124 writes constants). The plain rule cannot tell the two
  apart; a declassification point or a shared-domain helper can
  (`dokumente/NICHTINTERFERENZ.md`, §9).
-/
import Grammatik.Nichtinterferenz.Zeuge
import Grammatik.Export104
import Grammatik.Export108
import Grammatik.ExportSperre
import Grammatik.MehrfadenZeuge

namespace Gabbro.Grammatik

open NIZeuge

/-! ## 108: two readers of disjoint tables -- admitted -/

instance : DecidableEq G108_disjoint_start_locks.gD.Fn :=
  inferInstanceAs (DecidableEq G108_disjoint_start_locks.GFn)

def k108L : FlussEtiketten G108_disjoint_start_locks.gD NDom where
  lab
    | .inl .T => .A
    | .inl .U => .B
  labAx := fun a => nomatch a
  wurzel
    | .read_a => some .A
    | .read_c => some .B

def k108Cs : List (G108_disjoint_start_locks.gD.Tab ⊕ G108_disjoint_start_locks.gD.Glob) :=
  [.inl .T, .inl .U]

/-- **108 is admitted** under the split `read_a, T : A` / `read_c, U : B`. -/
theorem k108_fluss :
    flussB nπ G108_disjoint_start_locks.gP G108_disjoint_start_locks.gFs k108Cs k108L = true := by
  decide

/-- The crossed split (`read_a` reads `T`, labelled `B`) is refused: the
    check reads the labels. -/
theorem k108_gekreuzt :
    flussB nπ G108_disjoint_start_locks.gP G108_disjoint_start_locks.gFs k108Cs
      { k108L with lab := fun | .inl .T => .B | .inl .U => .A } = false := by
  decide

/-! ## 104: a writer and a reader of one account -- refused for every label -/

instance : DecidableEq G104_referenz.gD.Fn := inferInstanceAs (DecidableEq G104_referenz.GFn)

def k104L (d : NDom) : FlussEtiketten G104_referenz.gD NDom where
  lab
    | .inl .Konto => d
  labAx := fun a => nomatch a
  wurzel
    | .einzahlen => some .A
    | .lies => some .B

/-- **104 is refused for every label of the account** when the writer and
    the reader are different tenants. -/
theorem k104_abgelehnt :
    ∀ d, flussB nπ G104_referenz.gP G104_referenz.gFs [.inl .Konto] (k104L d) = false := by
  intro d
  cases d <;> decide

/-! ## 118: two writers of two tables -- refused for every labelling -/

instance : DecidableEq G118_sperrinvariante_erhaltung.gD.Fn :=
  inferInstanceAs (DecidableEq G118_sperrinvariante_erhaltung.GFn)

def k118L (da db : NDom) : FlussEtiketten G118_sperrinvariante_erhaltung.gD NDom where
  lab
    | .inl .A => da
    | .inl .B => db
  labAx := fun a => nomatch a
  wurzel
    | .gib => some .A
    | .nimm => some .B

/-- **118 is refused for every labelling of its two tables**: `gib` (A)
    and `nimm` (B) both write both. -/
theorem k118_abgelehnt : ∀ da db, flussB nπ G118_sperrinvariante_erhaltung.gP
    G118_sperrinvariante_erhaltung.gFs [.inl .A, .inl .B] (k118L da db) = false := by
  intro da db
  cases da <;> cases db <;> decide

/-! ## 124: private tables and one shared account -- refused for every label -/

def k124L (d : NDom) : FlussEtiketten mD NDom where
  lab
    | .inl .konto => d
    | .inl .privA => .A
    | .inl .privB => .B
  labAx := fun a => nomatch a
  wurzel
    | .hauptA => some .A
    | .hauptB => some .B
    | .ruhe => some .K
    | _ => none

/-- **124 is refused for every label of the shared account**: both
    tenants' call graphs reach `setze`, whose signature writes `konto`, so
    `konto` would need a label both `A` and `B` may flow to -- there is none
    below both. -/
theorem k124_abgelehnt :
    ∀ d, flussB nπ mP mFs [.inl .konto, .inl .privA, .inl .privB] (k124L d) = false := by
  intro d
  cases d <;> decide

end Gabbro.Grammatik
