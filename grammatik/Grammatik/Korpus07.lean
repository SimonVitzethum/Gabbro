/-
  File:      Grammatik/Korpus07.lean
  Subject:   THE ATTEMPTED G PROGRAM OF `beispiele/07-eintritt-und-boot.gab`,
             with the exact reason no non-degenerate witness exists.

  The source declares: a `walk` page table with `mappings of` quantifiers, a
  `format` bit layout with `reserved` fields, two `entry` items (register
  files, preserves/clobbers, stacks, dispatch), a `boot` item (ordered
  steps), five `linear ghost` marks, four `axiom`s, `raw`/`prim`/`extern`/
  `divergent` functions, constants -- and NO table, NO lock, NO `impl`
  function with a block body, NO `concurrent`. The faithful declaration is
  therefore `Tab := Empty`, `Lock := Empty`, `Fn := Empty`, `starts := []`:
  exactly the shape the exporter refuses, twice over
  (`crates/gabbro-check/src/lean_g.rs`, `check` on the model):
  `refuse("LG001", "a G declaration needs at least one table")` (no tables
  and no globals) and, had tables existed,
  `refuse("LG001", "a G program needs at least one function")`. The entry
  dispatches (`syscall_verteiler`, `nmi_verteiler`, `rust_eintritt`) are all
  `extern`, hence `refuse("LG001", "function {} is not `impl`")`; the
  `entry`/`boot` hardware around them (vectors, registers, steps) travels
  nowhere. `walk`/`format` types, linear marks as values, axioms and `prim`
  bodies have no `Ty`/`Stmt` form (LG001/LG002 family).

  What this file contains: the attempted declaration `kD`, the attempted
  program `kP` and Einheit `kE` (all vacuous), the VACUOUS premise group
  `korpus07_nutzer_leer` (honestly named -- it is NOT `korpus07_nutzer`),
  the checker verdict on the empty program, and the blockage: rule 13 needs
  a table some function writes, and 07 declares none, so no non-degenerate
  witness exists. That the SOURCE declares none is a reading of the source
  text (above), not a theorem; `offen07_kein_zeuge` only restates the
  modelling choice `Tab := Empty` (see the note in CUTS). Named gap
  `offen07`: G forms for entry/boot/walk (language extension), not a model
  repair.
-/
import Grammatik.Zielsatz.Proben

namespace Gabbro.Grammatik

namespace K07

/-- The attempted declaration: no tables, no globals, no locks, no
    functions -- everything 07 declares has no G form. -/
def kSigLeer : Signatur Empty Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun e => nomatch e
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def kD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun e => nomatch e
  Feld := fun e => nomatch e
  decFeld := fun e => nomatch e
  typ := fun e => nomatch e
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun e => nomatch e
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun e => nomatch e
  gbraucht := fun e => nomatch e
  eigner := fun e => nomatch e
  Fn := Empty
  sig := fun e => nomatch e
  sigNr := fun _ => kSigLeer
  eigner_nie_erzeugt := fun _ t _ _ _ => nomatch t
  Inv := Empty
  traeger := fun i => nomatch i
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
  geteilt_bewacht := fun e => nomatch e
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

instance : DecidableEq kD.Fn := inferInstanceAs (DecidableEq Empty)
instance : DecidableEq kD.Lock := inferInstanceAs (DecidableEq Empty)

/-- The attempted program: no functions, so no bodies and no contracts. -/
def kP : Programm kD where
  invariante := fun i => nomatch i
  requires := fun f => nomatch f
  ensures := fun f => nomatch f
  rumpf := fun f => nomatch f

/-- The attempted lock family: no locks, trivially true. -/
def kSI : SperrInv kD where
  orte := fun e => nomatch e
  inv := fun _ _ => true

def kSlotsLeer : ∀ t : kD.Tab, Int → ∀ f : kD.Feld t, Wert kD (kD.typ t f) :=
  fun t => nomatch t

def kSp : Speicher kD :=
  ⟨kSlotsLeer, fun e => nomatch e⟩

/-- The attempted Einheit: empty program, empty starts. -/
def kE : Zielsatz.Einheit kD := ⟨kP, kSI, axWahr kD, [], kSp, []⟩

/-- The VACUOUS premise group on the empty program -- honestly named, never
    `korpus07_nutzer`. -/
theorem korpus07_nutzer_leer : Zielsatz.NutzerPflicht kE := by
  refine ⟨⟨?_, ?_, axEnsLokal_wahr⟩, ⟨?_, ?_⟩⟩
  · intro _ f
    exact nomatch f
  · intro _ _ _ _
    rfl
  · intro e
    exact nomatch e
  · intro a ha
    cases ha

/-- The checker verdict on the empty program. -/
theorem kP_akzeptiert : Akzeptiert kP kSI [] [] [] [] = true := by decide

/-! ## The blockage, restated on the model (the source side is a reading) -/

/-- Rule 13 needs a table some function writes; the model declares no
    tables (a reading of the source: 07 declares none), so the
    non-degeneracy clause is unsatisfiable on this declaration:
    WHICH premise fails on WHICH term -- the existential over `Q07.Tab`
    fails on every `t`, because there is none. -/
theorem offen07_kein_zeuge : ¬ ∃ _t : kD.Tab, True :=
  fun ⟨t, _⟩ => nomatch t

/-- No function exists, so none writes anything: the second half of the
    non-degeneracy clause is vacuous too. -/
theorem offen07_kein_schreiber (f : kD.Fn) : False := nomatch f

/-- Named open premise: G forms for `entry`/`boot` hardware, `walk` types
    and `format` layouts (language extension). No model repair can close
    this; only new G forms -- or a source restricted to them -- can. -/
def offen07 : String :=
  "07 needs G forms for entry/boot/walk/format; exporter refuses LG001 (no table, no function) and LG001 (extern dispatch is not impl)"

/-
  CUTS: everything of substance. There is NO `korpus07_nutzer` and no
  `korpus07_nutzer_zeuge`: the faithful program is empty, so the
  non-degenerate premise group of rule 13 is unstatable
  (`offen07_kein_zeuge`). The vacuous group `korpus07_nutzer_leer` and the
  empty checker verdict are exhibited beside the blockage, not instead of a
  witness. What is NOT claimed: anything about the `.gab` source beyond the
  LG001/LG002 refusal shapes quoted in the header.

  SCOPE OF THE "PROOF" (review 2026-09-21, G02): `offen07_kein_zeuge` and
  `offen07_kein_schreiber` are true because `kD` sets `Tab := Empty` and
  `Fn := Empty`; they restate that modelling choice and prove nothing about
  the source. The blockage itself is argued in the header, from the source
  text: 07 declares no table, no global, no lock, and every function is
  `raw`/`prim`/`divergent`/`extern` or has no body (`boot_ende` ends in
  `;`). That argument was re-read against `beispiele/07` and holds; it is
  a reading, not a theorem.
-/
#print axioms K07.korpus07_nutzer_leer
#print axioms K07.offen07_kein_zeuge
#print axioms K07.kP_akzeptiert

end K07

end Gabbro.Grammatik
