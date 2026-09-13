/-
  File:      Grammatik/Export104.lean
  Subject:   the mechanical export of `beispiele/104-referenz.gab` held
             against its hand translation (`Referenz104.lean`, `r4P`).

  The `namespace G104_referenz` block below is pasted verbatim from the
  output of `gabbro lean-g beispiele/104-referenz.gab` (only its `import`
  line is left out; this file imports instead). What follows it is the
  correspondence: the decidable checks on the export, the same checks on
  the hand translation, and the declaration data both agree on.

  Equality `exported = r4P` is not statable: the two programs live over
  different declaration types (`GTab`/`GLock`/`GFn` here, `Unit`/`R4Fn`
  there), so `=` between them does not typecheck. The correspondence
  below is the honest maximum: every decidable check and every piece of
  declaration data, proved to agree. The remaining differences are listed
  in the CUTS block, each with its cause.
-/
import Grammatik.Referenz104
import Grammatik.Referenz104Rahmen

namespace Gabbro.Grammatik

namespace G104_referenz

inductive GTab where
  | Konto
  deriving DecidableEq

inductive GLock where
  | M
  deriving DecidableEq

inductive GKontoFeld where
  | stand
  deriving DecidableEq

inductive GFn where
  | einzahlen
  | lies
  deriving DecidableEq

def gSig_einzahlen : Signatur GTab Empty GLock Empty where
  params := [.ptr 0 true, .index 2, .int 0 10]
  erg := none
  gruende := 0
  haelt := [GLock.M]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def gSig_lies : Signatur GTab Empty GLock Empty where
  params := [.ptr 0 false, .index 2]
  erg := some (.int 0 100)
  gruende := 0
  haelt := [GLock.M]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

abbrev gD : Deklaration where
  Tab := GTab
  decTab := inferInstance
  count := fun | .Konto => 2
  Feld := fun | .Konto => GKontoFeld
  decFeld := fun | .Konto => inferInstance
  typ := fun | .Konto, .stand => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some GTab.Konto | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun | .Konto => true
  ggeteilt := fun e => nomatch e
  Lock := GLock
  decLock := inferInstance
  rang := fun | .M => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun | .Konto => [.inl GLock.M]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := GFn
  sig := fun | .einzahlen => 0 | .lies => 1
  sigNr := fun | 0 => gSig_einzahlen | 1 => gSig_lies | _ => gSig_lies
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  geteilt_bewacht := fun t => by cases t <;> decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

abbrev gCtx_einzahlen : Ctx := [.ptr 0 true, .index 2, .int 0 10]
abbrev gL_einzahlen : List (Res gD) := [Res.held (D := gD) GLock.M]
def g_einzahlen : gD.Fn := GFn.einzahlen
theorem gDarf_einzahlen_Konto : darf gD GTab.Konto gL_einzahlen := by unfold darf; decide

abbrev gCtx_lies : Ctx := [.ptr 0 false, .index 2]
abbrev gL_lies : List (Res gD) := [Res.held (D := gD) GLock.M]
def g_lies : gD.Fn := GFn.lies
theorem gDarf_lies_Konto : darf gD GTab.Konto gL_lies := by unfold darf; decide

theorem gHp_einzahlen_lies : RufPasst gD (vertragVon gD g_einzahlen) (gD.signatur g_lies) gL_einzahlen where
  hw := fun t => by cases t <;> decide
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von (fun L => by cases L <;> decide)
  hx := RufPasst.hx_von (fun L => by cases L <;> decide)

def gEns_einzahlen : Expr gD (ErgCtx (gD.params g_einzahlen) (gD.erg g_einzahlen)) (vertragVon gD g_einzahlen).ende .bool :=
  (.le (Expr.altSlot (D := gD) GTab.Konto GKontoFeld.stand ((.var (.dort .hier))) gDarf_einzahlen_Konto) (Expr.durch (D := gD) (.var .hier) GTab.Konto rfl GKontoFeld.stand ((.var (.dort .hier))) gDarf_einzahlen_Konto))

def gEns_lies : Expr gD (ErgCtx (gD.params g_lies) (gD.erg g_lies)) (vertragVon gD g_lies).ende .bool :=
  (.eq (.var .hier) (Expr.durch (D := gD) (.var (.dort .hier)) GTab.Konto rfl GKontoFeld.stand ((.var (.dort (.dort .hier)))) gDarf_lies_Konto))

def gBody_einzahlen : Endblock gD (vertragVon gD g_einzahlen) false gCtx_einzahlen gL_einzahlen :=
  (.cons (.assignDurch (.var .hier) GTab.Konto rfl GKontoFeld.stand ((.var (.dort .hier))) (.weiter (by decide) (by decide) (.lit 100)) (by decide) gDarf_einzahlen_Konto) (.cons (.call g_lies (.cons (.ptrOf GTab.Konto 0 rfl false) (.cons (.var (.dort .hier)) .nil)) gHp_einzahlen_lies rfl) (.ret .keine (List.Perm.refl _))))

def gBody_lies : Endblock gD (vertragVon gD g_lies) false gCtx_lies gL_lies :=
  (.ret (.wert (Expr.durch (D := gD) (.var .hier) GTab.Konto rfl GKontoFeld.stand ((.var (.dort .hier))) gDarf_lies_Konto)) (List.Perm.refl _))

def gP : Programm gD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .einzahlen => gEns_einzahlen
    | .lies => gEns_lies
  rumpf
    | .einzahlen => gBody_einzahlen
    | .lies => gBody_lies

def gFs : List gD.Fn := [g_einzahlen, g_lies]

example : programmImFragmentG gP gFs = true := by decide

example : fussOrtGB gP gFs = true := by decide

end G104_referenz

/-! ## Correspondence with the hand translation -/

/-- The export's own checks, as theorems (the generated file states them as
    `example`s, which cannot be named). -/
theorem export104_fragment : programmImFragmentG G104_referenz.gP G104_referenz.gFs = true := by decide

theorem export104_fuss : fussOrtGB G104_referenz.gP G104_referenz.gFs = true := by decide

/-- Joint checks: the mechanical export and the hand translation both pass
    the widened fragment and footprint checks (the hand side by
    `r4P_fragmentG`/`r4P_fussG`). -/
theorem export104_checks :
    programmImFragmentG G104_referenz.gP G104_referenz.gFs = true ∧
    fussOrtGB G104_referenz.gP G104_referenz.gFs = true ∧
    programmImFragmentG r4P r4Fs = true ∧
    fussOrtGB r4P r4Fs = true :=
  ⟨export104_fragment, export104_fuss, r4P_fragmentG, r4P_fussG⟩

/-- Declaration data agreement, construct by construct: table count and
    field range, lock rank, parameter lists, signature-held locks and write
    rights coincide between the export and `r4D`. -/
theorem export104_data :
    G104_referenz.gD.count G104_referenz.GTab.Konto = 2 ∧
    r4D.count () = 2 ∧
    G104_referenz.gD.typ G104_referenz.GTab.Konto G104_referenz.GKontoFeld.stand = .int 0 100 ∧
    r4D.typ () () = .int 0 100 ∧
    G104_referenz.gD.rang G104_referenz.GLock.M = 0 ∧
    r4D.rang () = 0 ∧
    G104_referenz.gD.params G104_referenz.g_einzahlen = [.ptr 0 true, .index 2, .int 0 10] ∧
    r4D.params r4Ein = [.ptr 0 true, .index 2, .int 0 10] ∧
    G104_referenz.gD.haelt G104_referenz.g_einzahlen = [G104_referenz.GLock.M] ∧
    r4D.haelt r4Ein = [()] ∧
    G104_referenz.gD.schreibt G104_referenz.g_einzahlen G104_referenz.GTab.Konto = true ∧
    r4D.schreibt r4Ein () = true ∧
    G104_referenz.gD.schreibt G104_referenz.g_lies G104_referenz.GTab.Konto = false ∧
    r4D.schreibt r4Lies () = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## CUTS:

  What is proved: the mechanical export of `beispiele/104-referenz.gab`
  checks (`export104_fragment`, `export104_fuss`); it passes the same two
  decidable checks as the hand translation (`export104_checks`); every
  piece of declaration data agrees (`export104_data`); the `ensures` and
  bodies have the same term shapes (`altSlot`/`durch`/`call`/`ptrOf`/fall-off
  `ret .keine`), including the `rw`-to-`r` pointer passed as `ptrOf` of the
  same table.

  What is NOT proved -- every difference between the two, precisely:

  1. Carrier TYPES differ by construction: `Unit`/`Empty`/`R4Fn` (hand)
     vs `GTab`/`GLock`/`GKontoFeld`/`GFn` (export). Same shapes (one table,
     one lock, one field), different names, so `exported = r4P` is not even
     statable -- `=` needs one type. Up-to-naming equality across different
     inductives is not a Lean proposition.
  2. FUNCTIONS differ: the export has exactly the surface `impl fn`s
     (`einzahlen`, `lies`); the hand translation adds the flagged driver
     `treiber` and the idle function `ruhe` (G starts every thread in some
     function). The exporter emits no driver and no idle function.
  3. NO-FORM ledger (both sides agree): the module wrapper, the inlined
     `const NKONTO`, carrier widths, address spaces, lock hold budgets,
     `reads` effects and `costs` have no G form and travel nowhere.
  4. `KoerperGutR`/`KoerperGutV`, the reached run `r4Lauf` and the goal
     theorem stay on the hand side: user obligations and runs are proved
     about `r4P`, not re-proved about the export.
-/

#print axioms Gabbro.Grammatik.export104_fragment
#print axioms Gabbro.Grammatik.export104_fuss
#print axioms Gabbro.Grammatik.export104_checks
#print axioms Gabbro.Grammatik.export104_data

end Gabbro.Grammatik
