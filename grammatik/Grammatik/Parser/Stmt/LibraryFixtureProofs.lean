module

public import Grammatik.Logik.Vertraege.Uebersetzung
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert

public section

namespace Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- Facts of the actual typed image at its first function. All fields are
    proved from phase results; none is an admission premise for source code. -/
structure DeclarationData (library : ULibrary) (unit : UProg)
    (image : Programm (declOf unit) × List (declOf unit).Fn) (schema : IntegerSchema)
    (reorder : Wert (declOf unit) schema.ty → Wert (declOf unit) schema.ty) : Prop where
  positive : 0 < unit.fns.length
  name : (fnAt unit ⟨0, positive⟩).name = library.translator.name
  parameters : (declOf unit).params ⟨0, positive⟩ = [schema.ty]
  result : (declOf unit).erg ⟨0, positive⟩ = some schema.ty
  noCalls : (befund image.1 ⟨0, positive⟩).rufe = []
  noIndirectCalls : (befund image.1 ⟨0, positive⟩).sigs = []
  bounded : (befund image.1 ⟨0, positive⟩).ewig = false
  noCycle : ∀ callee, zykS image.1 image.2 ⟨0, positive⟩ callee = false
  execution : ∀ oracle passes world (input : Wert (declOf unit) schema.ty),
    rufAt image.1 oracle passes 1 ⟨0, positive⟩ world
      (parameters.symm ▸ (Env.cons input Env.nil : Env (declOf unit) [schema.ty])) =
      .ok world (result.symm ▸ (reorder input : ErgVal (declOf unit) (some schema.ty)))

/-- Substitute complete selected library/unit values before touching their
    dependent program pair. Success proofs may differ only proof-irrelevantly. -/
theorem certifyData (members : List SItemTief) (call : SLibraryCall)
    (present : (libraryDecl members call).toOption.isSome = true)
    (Q : (library : ULibrary) → (unit : UProg) →
      (Programm (declOf unit) × List (declOf unit).Fn) → Prop)
    (library : ULibrary) (unit : UProg)
    (found : libraryDecl members call = .ok library)
    (elaborated : elabU (pre108 (translatorItems members library)) = .ok unit)
    (lowered : (lowerAllg unit).toOption.isSome = true)
    (facts : Q library unit ((lowerAllg unit).toOption.get lowered)) :
    let selected := (libraryDecl members call).toOption.get present
    let exported := (elabU (pre108 (translatorItems members selected))).toOption.getD
      { tabs := [], locks := [], fns := [] }
    ∀ checked : (lowerAllg exported).toOption.isSome = true,
      elabU (pre108 (translatorItems members selected)) = .ok exported ∧
        Q selected exported ((lowerAllg exported).toOption.get checked) := by
  dsimp only
  intro checked
  have selected : library = (libraryDecl members call).toOption.get present :=
    Except.ok.inj (found.symm.trans (except_ok_get present))
  subst library
  have selected : unit =
      (elabU (pre108 (translatorItems members
        ((libraryDecl members call).toOption.get present)))).toOption.getD
          { tabs := [], locks := [], fns := [] } := by
    rw [elaborated]
    rfl
  subst unit
  exact ⟨elaborated, facts⟩

/-- Retain concrete complete producer results before constructing any indexed
    fact. Their equality proofs transport the whole typed image back to the
    canonical success-dependent selections only after all facts are proved. -/
theorem certifyResults (members : List SItemTief) (call : SLibraryCall)
    (Q : (library : ULibrary) → (unit : UProg) →
      (Programm (declOf unit) × List (declOf unit).Fn) → Prop)
    (certificate : ∃ library, libraryDecl members call = .ok library ∧
      ∃ unit, elabU (pre108 (translatorItems members library)) = .ok unit ∧
      ∃ image, lowerAllg unit = .ok image ∧ Q library unit image) :
    ∀ present : (libraryDecl members call).toOption.isSome = true,
      let library := (libraryDecl members call).toOption.get present
      ∀ ready : (elabU (pre108 (translatorItems members library))).toOption.isSome = true,
        let unit := (elabU (pre108 (translatorItems members library))).toOption.get ready
        ∀ lowered : (lowerAllg unit).toOption.isSome = true,
          Q library unit ((lowerAllg unit).toOption.get lowered) := by
  obtain ⟨library, found, unit, made, image, emitted, facts⟩ := certificate
  intro present
  dsimp only
  intro ready
  intro lowered
  have selected : library = (libraryDecl members call).toOption.get present :=
    Except.ok.inj (found.symm.trans (except_ok_get present))
  subst library
  have selected : unit =
      (elabU (pre108 (translatorItems members
        ((libraryDecl members call).toOption.get present)))).toOption.get ready :=
    Except.ok.inj (made.symm.trans (except_ok_get ready))
  subst unit
  have selected : image = _ := Except.ok.inj (emitted.symm.trans (except_ok_get lowered))
  subst image
  exact facts

/-- Recover the first function from its actual lowering equation. The image is
    the canonical selected result, never a second concrete program assembly. -/
theorem declarationData_of_function
    {library : ULibrary} {unit : UProg}
    {lowered : (lowerAllg unit).toOption.isSome = true}
    {schema : IntegerSchema}
    {reorder : Wert (declOf unit) schema.ty → Wert (declOf unit) schema.ty}
    (positive : 0 < unit.fns.length)
    (named : (fnAt unit ⟨0, positive⟩).name = library.translator.name)
    (parameters : (declOf unit).params ⟨0, positive⟩ = [schema.ty])
    (result : (declOf unit).erg ⟨0, positive⟩ = some schema.ty)
    (needs : (fnAt unit ⟨0, positive⟩).needs = [])
    (invariants : (declOf unit).invs = [])
    {body : RumpTy unit ⟨0, positive⟩}
    (functionLowered : lowerFnAt unit ⟨0, positive⟩ = .ok (.tru, body, .tru))
    (calls : (befE false false body).rufe = [])
    (indirect : (befE false false body).sigs = [])
    (bounded : (befE false false body).ewig = false)
    (callFree : ∀ callee, mE
      ⟨fun h => !(decide (h = callee)), fun n => !((declOf unit).passt callee n),
        fun _ => true⟩ body = true)
    (run : ∀ oracle passes
      (handler : ∀ f : (declOf unit).Fn,
        World (declOf unit) → Env (declOf unit) ((declOf unit).params f) → RufAusgang f)
      world (input : Wert (declOf unit) schema.ty),
      execEnd oracle passes handler body world
        (parameters.symm ▸ (Env.cons input Env.nil : Env (declOf unit) [schema.ty])) =
        .zurueck world
          ((result.symm ▸ (reorder input : ErgVal (declOf unit) (some schema.ty))) :
            ErgVal (declOf unit) ((declOf unit).erg ⟨0, positive⟩))) :
    DeclarationData library unit ((lowerAllg unit).toOption.get lowered) schema reorder := by
  let image := (lowerAllg unit).toOption.get lowered
  have fields := lowerAllg_fields unit image.1 image.2 (except_ok_get lowered) ⟨0, positive⟩
  obtain ⟨value, origin, ensuresEq, bodyEq, _⟩ := fields
  rw [functionLowered] at origin
  cases origin
  have requiresEq : image.1.requires ⟨0, positive⟩ = .tru := by
    have required := lowerAllg_requires unit image.1 image.2
      (except_ok_get lowered) ⟨0, positive⟩ functionLowered
    simpa only [needs, reduceIte] using required
  have absent (callee : (declOf unit).Fn) :
      ruftB image.1 ⟨0, positive⟩ callee = false := by
    simp only [ruftB, bodyEq, callFree callee, Bool.not_true]
  refine {
    positive := positive
    name := named
    parameters := parameters
    result := result
    noCalls := ?_
    noIndirectCalls := ?_
    bounded := ?_
    noCycle := ?_
    execution := ?_ }
  · change (befE false false (image.1.rumpf ⟨0, positive⟩)).rufe = []
    rw [bodyEq]
    exact calls
  · change (befE false false (image.1.rumpf ⟨0, positive⟩)).sigs = []
    rw [bodyEq]
    exact indirect
  · change (befE false false (image.1.rumpf ⟨0, positive⟩)).ewig = false
    rw [bodyEq]
    exact bounded
  · intro callee
    have empty : (image.2.any fun h =>
        ruftB image.1 ⟨0, positive⟩ h && reachB image.1 image.2 h ⟨0, positive⟩) = false := by
      rw [List.any_eq_false]
      intro h _
      simp only [absent h, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
    unfold zykS
    rw [empty]
    exact Bool.and_false _
  · intro oracle passes world input
    rw [rufAt.eq_def, requiresEq]
    simp only [Expr.orte, lese_nil, eval, wahr?, Bool.true_eq_false, reduceIte]
    rw [bodyEq, run oracle passes (rufAt image.1 oracle passes 0) world input]
    simp only [ensuresEq, Expr.orte, lese_nil, eval, wahr?, Bool.true_eq_false,
      reduceIte, invariants, List.filter_nil, List.foldl_nil, List.find?_nil]

-- Only the concrete single-function producer and its small body are evaluated.
-- The full dependent image remains behind the generic projection certificates.
macro "library_data_fields" : tactic => `(tactic| (
  refine declarationData_of_function
    (positive := by decide) (named := by cbv)
    (parameters := by cbv) (result := by cbv)
    (needs := by cbv) (invariants := by cbv)
    (functionLowered := ?functionLowered) (calls := ?calls)
    (indirect := ?indirect) (bounded := ?bounded)
    (callFree := ?callFree) (run := ?run)
  case functionLowered => cbv <;> exact Eq.refl _
  case calls => cbv
  case indirect => cbv
  case bounded => cbv
  case callFree => intro callee; cbv
  case run =>
    intro oracle passes handler world input
    cbv
    all_goals first
      | rfl
      | apply congrArg (EndAusgang.zurueck world)
        funext index
        rcases index with ⟨position, bound⟩
        have choices : position = 0 ∨ position = 1 := by
          change position < 2 at bound
          omega
        rcases choices with rfl | rfl <;> rfl))

/-- Equality of answers may be cancelled without reducing a concrete unit
    beneath its dependent result type. -/
theorem answer_injective {source : LibrarySource} {unit : UProg}
    (decl : TranslationDecl source unit) : Function.Injective decl.answer := by
  intro first second same
  have cancel {left right : Option Ty} (equal : left = right)
      (a b : ErgVal (declOf unit) left) (h : (equal ▸ a) = (equal ▸ b)) : a = b := by
    cases equal
    exact h
  exact cancel decl.result.symm first second same

-- Each computed phase supplies the next phase's concrete canonical input. The
-- public getD definitions are retained, but success never follows from a default.
theorem certifyPhases (characters : List Char) (call : SLibraryCall)
    (retained : List SItemTief → Prop)
    (phases : ∃ tokens items members library unit,
      lexL characters = .ok tokens ∧ parseTopTief tokens = .ok items ∧
      Aufloesung.loeseL (Aufloesung.quelle items) [] items = members ∧ retained members ∧
      libraryDecl members call = .ok library ∧
      elabU (pre108 (translatorItems members library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true) :
    let tokens := (lexL characters).toOption.getD []
    let items := (parseTopTief tokens).toOption.getD []
    let members := Aufloesung.loeseL (Aufloesung.quelle items) [] items
    lexL characters = .ok tokens ∧ parseTopTief tokens = .ok items ∧ retained members ∧
      ∃ library unit, libraryDecl members call = .ok library ∧
        elabU (pre108 (translatorItems members library)) = .ok unit ∧
        (lowerAllg unit).toOption.isSome = true := by
  obtain ⟨tokens, items, members, library, unit, lexed, parsed, resolved, kept,
    found, elaborated, lowered⟩ := phases
  dsimp only
  have tokenEq : (lexL characters).toOption.getD [] = tokens := by rw [lexed]; rfl
  rw [tokenEq]
  have itemEq : (parseTopTief tokens).toOption.getD [] = items := by rw [parsed]; rfl
  rw [itemEq, resolved]
  exact ⟨lexed, parsed, kept, library, unit, found, elaborated, lowered⟩

theorem lowerFromPhases (members : List SItemTief) (call : SLibraryCall)
    (present : (libraryDecl members call).toOption.isSome = true)
    (phases : ∃ library unit, libraryDecl members call = .ok library ∧
      elabU (pre108 (translatorItems members library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true) :
    (lowerAllg ((elabU (pre108 (translatorItems members
      ((libraryDecl members call).toOption.get present)))).toOption.getD
        { tabs := [], locks := [], fns := [] })).toOption.isSome = true := by
  obtain ⟨library, unit, found, elaborated, lowered⟩ := phases
  have selected : (libraryDecl members call).toOption.get present = library := by
    exact (Except.ok.inj (found.symm.trans (except_ok_get present))).symm
  rw [selected, elaborated]
  exact lowered

/-- Assemble the actual per-function successes through the existing list producer. -/
private theorem lowerEach_certified (u : Uebersetze.UProg) :
    ∀ fs : List (Fin u.fns.length),
      (∀ f ∈ fs, (lowerFnAt u f).toOption.isSome = true) → lowerEach u fs = .ok ()
  | [], _ => rfl
  | f :: fs, success => by
    rw [lowerEach, Gabbro.Grammatik.except_ok_get (ε := String)
      (α := EnsTy u f × RumpTy u f × ReqTy u f) (x := lowerFnAt u f)
      (success f (List.mem_cons_self ..))]
    exact lowerEach_certified u fs (fun g hg => success g (List.mem_cons_of_mem _ hg))

/-- Success follows the canonical dependent collector without reducing a concrete unit
    underneath its indexed motive. Every entry is supplied by its actual producer. -/
private theorem collect_certified : ∀ (n : Nat) (T : Fin n → Type)
    (get : (i : Fin n) → Except String (T i)),
    (∀ i, (get i).toOption.isSome = true) →
      (Measures.collect n T get).toOption.isSome = true
  | 0, _, _, _ => rfl
  | n + 1, T, get, success => by
    have head := Gabbro.Grammatik.except_ok_get (ε := String) (α := T 0)
      (x := get 0) (success 0)
    have tail := collect_certified n (fun i => T i.succ) (fun i => get i.succ)
      (fun i => success i.succ)
    have tailValue := Gabbro.Grammatik.except_ok_get (ε := String)
      (α := (i : Fin n) → T i.succ)
      (x := Measures.collect n (fun i => T i.succ) (fun i => get i.succ)) tail
    rw [Measures.collect, head]
    dsimp only [bind, Except.bind]
    rw [tailValue]
    rfl

private theorem absent_measures (u : Uebersetze.UProg)
    (absent : ∀ f : Fin u.fns.length, (fnAt u f).decreases = none) :
    (Measures.lowerMeasures u).toOption.isSome = true := by
  have entries := collect_certified u.fns.length (fun f => Measures.At u f)
    (fun f => Measures.lowerAt u f) (fun f => by
      unfold Measures.lowerAt
      split
      · rfl
      · rename_i source selected
        rw [absent f] at selected
        cases selected)
  have collected := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := (f : Fin u.fns.length) → Measures.At u f)
    (x := Measures.collect u.fns.length (Measures.At u) (Measures.lowerAt u)) entries
  unfold Measures.lowerMeasures
  rw [collected]
  rfl

/-- Assemble the unchanged lowering from its actual component certificates. The
    measure gate sees empty tuples at every function, including recursive edges. -/
theorem lowering_ok (u : UProg) (noInvs : u.invs = []) (contracts : contractGate u = true)
    (functions : ∀ f : Fin u.fns.length,
      (lowerFnAt u f).toOption.isSome = true ∧ (fnAt u f).decreases = none) :
    (lowerAllg u).toOption.isSome = true := by
  have measures := absent_measures u (fun f => (functions f).2)
  let exported : Measures.Export u := (Measures.lowerMeasures u).toOption.get measures
  have measured : Measures.lowerMeasures u = .ok exported :=
    Gabbro.Grammatik.except_ok_get (ε := String) (α := Measures.Export u)
      (x := Measures.lowerMeasures u) measures
  have empty : ∀ f, exported.mass f = [] :=
    fun f => Measures.lowerMeasures_absent u exported f ((functions f).2)
  have checked : ∀ P : Programm (declOf u),
      (Measures.checkedProgram u P).toOption.isSome = true := by
    intro P
    have lengths : Measures.cycleLengths u P exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      rw [empty f, empty g]
      change (!zykS P (List.finRange u.fns.length) f g || true) = true
      exact Bool.or_true _
    unfold Measures.checkedProgram
    rw [measured]
    dsimp only
    split
    · rfl
    · contradiction
  have invs : lowerInvs u (List.finRange u.invs.length) = .ok () := by
    cases enumeration : List.finRange u.invs.length with
    | nil => rfl
    | cons i rest =>
      have length : u.invs.length = 0 := congrArg List.length noInvs
      have bound := i.isLt
      omega
  have each := lowerEach_certified u (List.finRange u.fns.length) (fun f _ => (functions f).1)
  have lowered : (lowerAllg u).toOption.isSome = true := by
    unfold lowerAllg
    split
    · rename_i error failed
      rw [invs] at failed
      cases failed
    · split
      · rename_i error failed
        rw [each] at failed
        cases failed
      · split
        · exact checked _
        · contradiction
  exact lowered

-- The image witness is the existing success-dependent selection. In particular,
-- this never unfolds `progOfFn`, its dependent collector, or checkedProgram.
macro "library_emitted" : tactic => `(tactic| (
  apply except_ok_get
  apply lowering_ok
  · rfl
  · cbv
  · rintro ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv))

/-- Transport the complete metadata certificate before introducing any function
    index of the extracted unit. The concrete assembler is never evaluated here. -/
theorem lowering_from_elaboration (source : Except String UProg)
    (success : source.toOption.isSome = true)
    (certificate : ∃ unit, source = .ok unit ∧ unit.invs = [] ∧
      contractGate unit = true ∧ ∀ f : Fin unit.fns.length,
        (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none) :
    (lowerAllg (source.toOption.get success)).toOption.isSome = true := by
  obtain ⟨unit, elaborated, noInvs, contracts, functions⟩ := certificate
  have same : unit = source.toOption.get success :=
    Except.ok.inj (elaborated.symm.trans (except_ok_get success))
  rw [← same]
  exact lowering_ok unit noInvs contracts functions

end Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs
