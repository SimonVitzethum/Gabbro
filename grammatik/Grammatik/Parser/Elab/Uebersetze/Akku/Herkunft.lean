/-
  File:      Grammatik/Parser/Elab/Uebersetze/Akku/Herkunft.lean
  Subject:   C15: the hardware provenance of the generated core-query axiom,
              end to end. An `assume` item, an `accumulates` item naming it,
              an update use and a read use elaborate; the declaration carries
              the hardware origin with its named witness (`D.axHerkunft`,
              `D.axBeleg`). FINDING: the core checker `Akzeptiert` refuses the
              lowered program, because the admission keeps the cells out of
              every write set but the update's, and the calling user function
              inherits them (`herkunft_akku_abgelehnt`). The twins are refused
              too: without `assume` the query is unwitnessed, and an unknown
              `assume` name is a named elaboration error.
-/
module

public import Grammatik.Parser.Elab.Uebersetze.Akku.Expand
public import Grammatik.Parser.Elab.Uebersetze.Akku.Proben
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil13
public import Grammatik.Parser.Elab.UebersetzePipeline
public import Grammatik.Parser.Elab.UebersetzeAllg2
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Zielsatz.Kern.Akzeptiert
public import Grammatik.Bausteine.Kernzelle.KernAbfrage
public import Grammatik.Bausteine.Kernzelle.Zulassung
-- Proof-only access to the canonical phase equations; production visibility is unchanged.
import all Grammatik.Parser.Elab.Uebersetze.Akku.Proben
import all Grammatik.Parser.Elab.Uebersetze.Akku.ProbenPhases
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil4
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil5
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg.Teil5
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Stufe
import all Grammatik.Parser.Elab.UebersetzeAllg3.Seq
import all Grammatik.Parser.Elab.UebersetzeAllg3.Struct
import all Init.Data.Int.Repr
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

set_option maxRecDepth 100000

-- The same reader, scanner and callback equations as the accumulator-use witnesses.
-- In particular, select the actual fuel before dispatch instead of reducing the
-- mutual implementation or a complete 100000-level lowering record in the kernel.
attribute [local cbv_opaque] Nat.toDigitsCore uFloatLimit
attribute [local cbv_eval] digits_select Nat.log2_def generated_range_text generated_range
  strEq_apply_eq_decide

attribute [local cbv_opaque] uAnwReihe uAnwReiheCore
attribute [local cbv_eval] row_nil row_cons core_bind core_trim core_locks
  core_call core_set core_cond

attribute [local cbv_opaque] uAkkuBinder uZeigerAnw uStartNamen elabKlauseln
  expandReturnCall expandFoldEnd uSondenFns uTorHuellen
attribute [local cbv_eval] bound_names_select pointer_source_select start_source_select
  clauses_nil clauses_effect clauses_cost clauses_effect_cost
  return_none return_empty return_variable fold_end_none fold_end_empty fold_end_variable
  sonden_nil wrappers_nil

attribute [local cbv_eval] uRechne.eq_def uSichert.eq_def uZSeite.eq_def
  seiteAltErg.eq_def ensAltErg.eq_def
  UebersetzeAllg.lowWertE.eq_def UebersetzeAllg.lowEns.eq_def
  UebersetzeAllg.lowCmp.eq_def UebersetzeAllg.lowArrayValue.eq_def
  UebersetzeAllg.lowCountE.eq_def UebersetzeAllg.lowSeiteZ.eq_def

private theorem herkunft_seq_select (u : UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (UebersetzeAllg.declOf u)))
    (pe : UebersetzeAllg2.AtTop u caller Λ) (ss : List UStmt) :
    UebersetzeAllg2.lowSeqL (l := l) u caller Γ fn n Λ pe ss = match n with
      | 0 => .error "lower: blocks nested too deep"
      | k + 1 => UebersetzeAllg2.lowSeqStep (l := l) u caller
          (UebersetzeAllg2.lowStufe u caller k) Γ fn Λ pe ss := by
  cases n <;> rfl

private theorem herkunft_struct_select (u : UProg) (caller : Fin u.fns.length) (n : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (UebersetzeAllg.declOf u)))
    (pe : UebersetzeAllg2.AtTop u caller Λ) (s : UStmt) (ss : List UStmt) :
    UebersetzeAllg2.lowStructL (l := l) u caller Γ fn n Λ pe s ss = match n with
      | 0 => .error "lower: blocks nested too deep"
      | k + 1 => UebersetzeAllg2.lowStructStep (l := l) u caller
          (UebersetzeAllg2.lowStufe u caller k) Γ fn Λ pe s ss := by
  cases n <;> rfl

attribute [local cbv_opaque] UebersetzeAllg2.lowStufe UebersetzeAllg2.lowSeqL
  UebersetzeAllg2.lowStructL
attribute [local cbv_eval] herkunft_seq_select herkunft_struct_select
  UebersetzeAllg2.lowStufe_seq UebersetzeAllg2.lowStufe_struct

section Metadata

-- Names, signatures and provenance do not inspect the post-pass call floors.
attribute [local cbv_opaque] floorOf

/-! ## The fixture: `assume` plus `accumulates` with an origin -/

/-- The named hardware assumption witnessing the core query. -/
def herkunftAnnahme : SItemTief :=
  .assumT "kern_antwort" none "the core query answers the running core"
    (.trust "silicon")

/-- The accumulator with its origin: two unsigned `add` cells. -/
def herkunftAccT : SItemTief :=
  .accT "s" (.atom "u32") "add" (some (.lit 2)) (some "kern_antwort")

/-- The probe update use: merge the argument. -/
def herkunftMelde : SItemTief :=
  .fnT { art := "impl", name := "melde", params := [("t", .atom "u32")],
         res := none, fehler := none,
         klauseln := [.effs [.writes (.variable "s")]] }
    (.block [.set (.variable "s") "=" (.variable "t")] none)

/-- The probe read use: return the sampled fold. -/
def herkunftLies : SItemTief :=
  .fnT { art := "impl", name := "lies", params := [],
         res := some (.atom "u32"), fehler := none, klauseln := [] }
    (.block [] (some (.ret (some (.variable "s")))))

/-- The fixture items. -/
def herkunftItems : List SItemTief :=
  [herkunftAnnahme, herkunftAccT, herkunftMelde, herkunftLies]

/-- The fixture elaborates. -/
theorem herkunft_elab : (elabU herkunftItems).toOption.isSome = true := by
  cbv

/-- The elaborated fixture. -/
def herkunftU : UProg :=
  (elabU herkunftItems).toOption.get herkunft_elab

/-- The generated query travels as the only foreign body. -/
theorem herkunft_frage_namen : herkunftU.axs.map (·.name) = ["s#kern"] := by cbv

/-- The generated functions travel after the user functions. -/
theorem herkunft_funktionen_namen :
    herkunftU.fns.map (·.name) =
      ["melde", "lies", "s#aktualisiere", "s#falte", "s#query"] := by cbv

/-- The unit knows its assumption. -/
theorem herkunft_annahmen : herkunftU.annahmen = ["kern_antwort"] := by cbv

/-! ## Name resolution inside the elaborated unit -/

/-- The index of the first entry named `n` (`h0`: the list is not empty;
    every name below is present, so the fallback is dead). -/
def finName {α : Type} (nm : α → String) (xs : List α) (n : String)
    (h0 : 0 < xs.length) : Fin xs.length :=
  match xs.findIdx? (fun x => strEq (nm x) n) with
  | some j => if hj : j < xs.length then ⟨j, hj⟩ else ⟨0, h0⟩
  | none => ⟨0, h0⟩

theorem herkunft_globs_nichtleer : 0 < herkunftU.globs.length := by cbv

theorem herkunft_locks_nichtleer : 0 < herkunftU.locks.length := by cbv

theorem herkunft_fns_nichtleer : 0 < herkunftU.fns.length := by cbv

theorem herkunft_axs_nichtleer : 0 < herkunftU.axs.length := by cbv

/-- The query axiom. -/
def herkunftQax : Fin herkunftU.axs.length :=
  finName UAx.name herkunftU.axs "s#kern" herkunft_axs_nichtleer

/-- The query axioms of the unit, by name. -/
def herkunftQs : List (UebersetzeAllg.declOf herkunftU).Ax :=
  (List.finRange herkunftU.axs.length).filter fun a =>
    strEq ((herkunftU.axs.get a).name) "s#kern"

/-! ## The descriptor and its provenance -/

/-- The source descriptor over the elaborated carriers. -/
theorem herkunft_decl_ok :
    (uAkkuDecl (D := UebersetzeAllg.declOf herkunftU) [] [] herkunftAccT
      (fun _ i => finName UGlob.name herkunftU.globs
        ("s#zelle" ++ toString i.val) herkunft_globs_nichtleer)
      (fun _ i => finName ULock.name herkunftU.locks
        ("s#sperre" ++ toString i.val) herkunft_locks_nichtleer)
      (finName UFn.name herkunftU.fns "s#query" herkunft_fns_nichtleer)
      (finName UFn.name herkunftU.fns "s#aktualisiere" herkunft_fns_nichtleer)
      (finName UFn.name herkunftU.fns "s#falte" herkunft_fns_nichtleer)).toOption.isSome = true := by
  cbv

/-- The accumulator declaration of the fixture. -/
def herkunftDecl : Kernzelle.AccumulatorDecl (UebersetzeAllg.declOf herkunftU) :=
  (uAkkuDecl (D := UebersetzeAllg.declOf herkunftU) [] [] herkunftAccT
    (fun _ i => finName UGlob.name herkunftU.globs
      ("s#zelle" ++ toString i.val) herkunft_globs_nichtleer)
    (fun _ i => finName ULock.name herkunftU.locks
      ("s#sperre" ++ toString i.val) herkunft_locks_nichtleer)
    (finName UFn.name herkunftU.fns "s#query" herkunft_fns_nichtleer)
    (finName UFn.name herkunftU.fns "s#aktualisiere" herkunft_fns_nichtleer)
    (finName UFn.name herkunftU.fns "s#falte" herkunft_fns_nichtleer)).toOption.get
    herkunft_decl_ok

/-- The query shape holds on the elaborated query, decided. -/
theorem herkunft_frage_gestaltB :
    Kernzelle.kernAbfrageGestaltB (UebersetzeAllg.declOf herkunftU)
      herkunftQax 2 [] (List.finRange herkunftU.globs.length) = true := by
  cbv

/-- The provenance holds on the elaborated query, decided. -/
theorem herkunft_frage_herkunftB :
    Kernzelle.kernAbfrageHerkunftB (UebersetzeAllg.declOf herkunftU)
      herkunftQax = true := by
  cbv

/-- The provenance holds: hardware origin with the named witness. -/
theorem herkunft_frage_herkunft :
    Kernzelle.KernAbfrageHerkunft (UebersetzeAllg.declOf herkunftU)
      herkunftQax :=
  Kernzelle.kernAbfrageHerkunftB_iff.mp herkunft_frage_herkunftB

/-- The declaration field reads `hardware`. -/
theorem herkunft_frage_feld :
    (UebersetzeAllg.declOf herkunftU).axHerkunft herkunftQax =
      some .hardware := by
  cbv

/-- The declaration carries a named witness. -/
theorem herkunft_beleg_vorhanden :
    ((UebersetzeAllg.declOf herkunftU).axBeleg herkunftQax).isSome = true := by
  cbv

/-! ## The checker with the query list -/

/-- **The checker on an elaborated accumulator unit**: the lowered program,
    the lock family of `Differenz`, every lock and every carrier enumerated,
    the user functions as the starts, the descriptor and the query list. -/
def akzeptiertMit (u : UProg)
    (decl : Kernzelle.AccumulatorDecl (UebersetzeAllg.declOf u))
    (qs : List (UebersetzeAllg.declOf u).Ax) : Except String Bool :=
  match UebersetzeAllg2.lowerAllg u with
  | .error e => .error e
  | .ok (P, fs) =>
    if !Cover.Differenz.sperrInvsOk u then .error "lock invariant without G form"
    else
      let ws : List (UebersetzeAllg.declOf u).Fn :=
        (List.finRange u.fns.length).filter fun f =>
          strEq (((u.fns.get f).name)) "melde" ||
          strEq (((u.fns.get f).name)) "lies"
      let ls : List (UebersetzeAllg.declOf u).Lock :=
        List.finRange u.locks.length
      let cs : List ((UebersetzeAllg.declOf u).Tab ⊕
        (UebersetzeAllg.declOf u).Glob) :=
        (List.finRange u.tabs.length).map Sum.inl ++
          (List.finRange u.globs.length).map Sum.inr
      .ok (Akzeptiert P (Cover.Differenz.sperrFamilie u) fs ls cs ws
        [decl] [] qs)

/-- The user function `melde` carries the first cell in its write set: the
    expansion of `effects { writes s }`, which the call of the generated
    update requires (`RufPasst.hg`). -/
theorem herkunft_melde_schreibt_zelle :
    TraegerSchreibt (D := UebersetzeAllg.declOf herkunftU)
      (finName UFn.name herkunftU.fns "melde" herkunft_fns_nichtleer)
      (.inr (finName UGlob.name herkunftU.globs "s#zelle0" herkunft_globs_nichtleer)) = true := by
  cbv

end Metadata

-- A failed accumulator conjunct already determines the full checker result.
-- Reuse that certificate instead of evaluating unrelated graph and cost checks.
private theorem akzeptiertMit_of_accumulator_refusal (u : UProg)
    (decl : Kernzelle.AccumulatorDecl (UebersetzeAllg.declOf u))
    (qs : List (UebersetzeAllg.declOf u).Ax)
    (noTables : u.tabs = []) (invariants : Cover.Differenz.sperrInvsOk u = true)
    (refused : (match UebersetzeAllg2.lowerAllg u with
      | .ok (P, fs) => Kernzelle.accumulatorB P fs []
          (List.finRange u.globs.length) qs [decl]
      | .error _ => true) = false) :
    akzeptiertMit u decl qs = .ok false := by
  cases lowered : UebersetzeAllg2.lowerAllg u with
  | error error => rw [lowered] at refused; cases refused
  | ok result =>
    rcases result with ⟨P, fs⟩
    rw [lowered] at refused
    have tables : List.finRange u.tabs.length = [] := by rw [noTables]; rfl
    have carrierTables : tabsOf
        ((List.finRange u.globs.length).map
          (Sum.inr : (UebersetzeAllg.declOf u).Glob →
            (UebersetzeAllg.declOf u).Tab ⊕ (UebersetzeAllg.declOf u).Glob)) = [] := by
      simp [tabsOf]
    have carrierGlobals : globsOf
        ((List.finRange u.globs.length).map
          (Sum.inr : (UebersetzeAllg.declOf u).Glob →
            (UebersetzeAllg.declOf u).Tab ⊕ (UebersetzeAllg.declOf u).Glob)) =
        List.finRange u.globs.length := by
      simp [globsOf, Function.comp_def]
    simp only [akzeptiertMit, lowered, invariants, Bool.not_true,
      Bool.false_eq_true, ite_false]
    apply congrArg Except.ok
    simp only [Akzeptiert, tables, List.map_nil, List.nil_append, carrierTables,
      carrierGlobals, refused, Bool.and_false, Bool.false_and]

/-- **FINDING (C15, open): the accumulator component refuses a unit
    whose user function calls the generated update.** `akkuZulaessig` demands
    that no function besides the update and the fold has a cell in its write
    set; a call demands the callee's write set inside the caller's. `melde`
    therefore carries the cells (`herkunft_melde_schreibt_zelle`) and the
    descriptor is refused. The provenance witnesses above are unaffected. -/
theorem herkunft_akku_abgelehnt :
    (match UebersetzeAllg2.lowerAllg herkunftU with
    | .ok (P, fs) => Kernzelle.accumulatorB P fs []
        (List.finRange herkunftU.globs.length)
        herkunftQs [herkunftDecl]
    | .error _ => true) = false := by
  cbv

/-- The same finding on the core checker with the query list. -/
theorem herkunft_nicht_akzeptiert :
    akzeptiertMit herkunftU herkunftDecl herkunftQs = .ok false := by
  exact akzeptiertMit_of_accumulator_refusal _ _ _ (by cbv) (by cbv)
    herkunft_akku_abgelehnt

/-! ## The twins: refused -/

section WithoutOriginMetadata

attribute [local cbv_opaque] floorOf

/-- Without `assume` the unit still elaborates. -/
theorem ohne_elab : (elabU [probenAccT, probenMelde, probenLies]).isOk = true := by
  exact akkuVerwendung_zeuge

/-- Without `assume` the unit still elaborates (the `.toOption` form). -/
theorem ohne_elab_some :
    (elabU [probenAccT, probenMelde, probenLies]).toOption.isSome = true := by
  have made := ohne_elab
  cases result : elabU [probenAccT, probenMelde, probenLies] with
  | error error => rw [result] at made; cases made
  | ok unit => rfl

/-- The elaborated unit without an origin. -/
def ohneU : UProg :=
  (elabU [probenAccT, probenMelde, probenLies]).toOption.get ohne_elab_some

theorem ohne_globs_nichtleer : 0 < ohneU.globs.length := by cbv

theorem ohne_locks_nichtleer : 0 < ohneU.locks.length := by cbv

theorem ohne_fns_nichtleer : 0 < ohneU.fns.length := by cbv

/-- The descriptor over the unit without an origin. -/
theorem ohne_decl_ok :
    (uAkkuDecl (D := UebersetzeAllg.declOf ohneU) [] [] probenAccT
      (fun _ i => finName UGlob.name ohneU.globs
        ("s#zelle" ++ toString i.val) ohne_globs_nichtleer)
      (fun _ i => finName ULock.name ohneU.locks
        ("s#sperre" ++ toString i.val) ohne_locks_nichtleer)
      (finName UFn.name ohneU.fns "s#query" ohne_fns_nichtleer)
      (finName UFn.name ohneU.fns "s#aktualisiere" ohne_fns_nichtleer)
      (finName UFn.name ohneU.fns "s#falte" ohne_fns_nichtleer)).toOption.isSome = true := by
  cbv

/-- The accumulator declaration without an origin. -/
def ohneDecl : Kernzelle.AccumulatorDecl (UebersetzeAllg.declOf ohneU) :=
  (uAkkuDecl (D := UebersetzeAllg.declOf ohneU) [] [] probenAccT
    (fun _ i => finName UGlob.name ohneU.globs
      ("s#zelle" ++ toString i.val) ohne_globs_nichtleer)
    (fun _ i => finName ULock.name ohneU.locks
      ("s#sperre" ++ toString i.val) ohne_locks_nichtleer)
    (finName UFn.name ohneU.fns "s#query" ohne_fns_nichtleer)
    (finName UFn.name ohneU.fns "s#aktualisiere" ohne_fns_nichtleer)
    (finName UFn.name ohneU.fns "s#falte" ohne_fns_nichtleer)).toOption.get
    ohne_decl_ok

end WithoutOriginMetadata

/-- Without an origin the accumulator component refuses, even with its
    descriptor listed: no query list admits an unwitnessed query. -/
theorem ohne_akku_abgelehnt :
    (match UebersetzeAllg2.lowerAllg ohneU with
    | .ok (P, fs) => Kernzelle.accumulatorB P fs []
        (List.finRange ohneU.globs.length)
        [] [ohneDecl]
    | .error _ => true) = false := by
  cbv

/-- Without an origin the core checker refuses the unit. -/
theorem ohne_abgelehnt :
    akzeptiertMit ohneU ohneDecl [] = .ok false := by
  exact akzeptiertMit_of_accumulator_refusal _ _ _ (by cbv) (by cbv)
    ohne_akku_abgelehnt

/-- An unknown `assume` name is a named elaboration error. -/
theorem fremd_annahme_abgelehnt :
    (match elabU [.accT "s" (.atom "u32") "add" (some (.lit 2))
        (some "sonde"), probenMelde, probenLies] with
    | .error e => e == "core query assumption unknown: sonde"
    | .ok _ => false) = true := by
  cbv

end Gabbro.Grammatik.Parser.Uebersetze
