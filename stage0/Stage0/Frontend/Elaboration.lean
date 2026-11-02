module
public import Stage0.Frontend.Source
public import Stage0.Frontend.Tables
public import Grammatik.Parser.Elab.Konst.ErsetzungTor
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


namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The frozen canonical elaborator's phase body, parameterized only by checked declaration
    scopes. Every check and canonical elaborator is retained. elabU_scopes below makes drift a
    kernel error; factoring here is necessary while the grammar package cannot be rebuilt. -/
def elabWithScopes (items : List SItemTief) (consts : List (String × Int))
    (typeEnv : List (String × (Int × Int)))
    (functions : List UKonstFn := uKonstFns (uOhneSenken (uMembers items)))
    (tableLowering : List String → SItemTief → Except String UTab := uTabelle consts typeEnv) : Except String UProg :=
  let ms0 := uMembers items
  match uRestFehler ms0 with
  | .error e => .error e
  | .ok _ =>
  match ExportMetadata.checkConstants ms0 with
  | .error error => .error error
  | .ok () =>
  let ms := uOhneSenken ms0
  match uGlobs consts typeEnv ms with
  | .error e => .error e
  | .ok globs0 =>
  let tnames := ms.filterMap (fun | .tableT n _ _ _ _ _ _ => some n | _ => none)
  match uSeq ((ms.filter (fun
      | .tableT _ _ _ _ _ _ _ => true | _ => false)).map (tableLowering tnames)) with
  | .error e => .error e
  | .ok tabs0 =>
  match uArenen consts typeEnv ms with
  | .error e => .error e
  | .ok (arTabs, arGlobs) =>
  let tabs := uIdxTabs (tabs0 ++ arTabs ++ uArrayCarriers typeEnv ms0)
  match uOptGlobs tabs (globs0 ++ arGlobs) with
  | .error e => .error e
  | .ok globs =>
  match uSeq ((ms.filter (fun
      | .lockT _ _ _ _ _ _ _ => true | _ => false)).map (fun item => uSperre globs tabs item consts)) with
  | .error e => .error e
  | .ok locks0 =>
  match uSperrInvs consts typeEnv globs tabs ms locks0 with
  | .error e => .error e
  | .ok locks =>
  let bewacht : String → Bool := fun c => locks.any (fun l => l.guard.any (strEq · c))
  if !tabs.all (fun t => !t.shared || bewacht t.name) then .error "shared table without a guard" else
  if !globs.all (fun g => !g.shared || g.atomic || bewacht g.name) then .error "shared static without a guard" else
  if !globs.all (fun g => g.nutzlast.all (fun n => globs.any (fun h => strEq h.name n))) then
    .error "payload names no static" else
  -- C17: Stage 0 consumes the same certified call-site substitution,
  -- after the checked scopes and BEFORE `fnItems`/runtime elaboration.
  match Gabbro.Grammatik.Parser.Konst.konstErsetzePipeline ms with
  | .error e => .error e
  | .ok msSub =>
  let fnItems := msSub.filterMap (fun
    | .fnT sig koerper => if strEq sig.art "const" then none else some (sig, koerper)
    | _ => none)
  match uWhys ms with
  | .error e => .error e
  | .ok whys =>
  match uSums typeEnv ms with
  | .error e => .error e
  | .ok sums =>
  match uSumGlobs consts sums ms globs with
  | .error e => .error e
  | .ok globs =>
  match uSumTabs sums tabs with
  | .error e => .error e
  | .ok tabs =>
  match uRegs typeEnv consts tabs globs ms with
  | .error e => .error e
  | .ok regs =>
  match uInvs consts typeEnv tabs locks globs ms with
  | .error e => .error e
  | .ok invs =>
  let transitionCtx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held := [],
                                res := none, fname := "transition", alias := typeEnv, lits := consts, globs }
  match uSeq (ms.filterMap (fun | .stateT n ts => some (uZustand n ts transitionCtx) | _ => none)) with
  | .error e => .error e
  | .ok zustaende =>
  if (uEindeutig (zustaende.map (·.name))).length != zustaende.length then
    .error "duplicate state identity" else
  match uGenerateTransitions tabs globs zustaende with
  | .error e => .error e
  | .ok transitionFns =>
  if transitionFns.any (fun g => fnItems.any (fun (s, _) => strEq s.name g.name)) then
    .error "generated transition function conflicts with an explicit function" else
  let devs := ms.filterMap (fun | .devT n _ _ _ => some n | _ => none)
  let zeiger := uOhneDoppelte (fnItems.flatMap (fun (s, b) => uZeigerTexte (s.params.map (·.2)) ++ uZeigerAnw 100000 b))
  let zb := fnItems.length + transitionFns.length
  match uSeq ((List.range zeiger.length).zip zeiger |>.map (fun (j, r) =>
      elabZeigerTyp consts typeEnv tabs locks globs whys sums zeiger zb j r)) with
  | .error e => .error e
  | .ok zeigerPaare =>
  match uSeq (fnItems.map (fun (s, _) => elabKopf consts typeEnv tabs locks globs whys sums s devs zeiger zb)) with
  | .error e => .error e
  | .ok [] => .error "unit without a fn"
  | .ok kopfPaare =>
  match uSeq ((ms.filterMap uFremdSig).map (fun (sig, asm) => elabAxKopf typeEnv tabs whys globs asm sig)) with
  | .error e => .error e
  | .ok axKoepfe0 =>
  match uSeq ((ms.filterMap (fun | .callT sc => some sc | _ => none)).map (elabGateKopf typeEnv tabs whys globs)) with
  | .error e => .error e
  | .ok gateKoepfe =>
  let axKoepfe := axKoepfe0 ++ gateKoepfe
  let koepfe := kopfPaare.map (·.1) ++ axKoepfe ++ zeigerPaare.map (·.1)
  let annahmen := ms.filterMap (fun | .assumT n _ _ _ => some n | _ => none)
  match uSeq (fnItems.map (fun (s, b) =>
      elabUFunktion consts typeEnv tabs locks globs koepfe s b annahmen whys sums devs regs zustaende zeiger zb
        (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none))
        (uKonstArrays typeEnv functions consts ms))) with
  | .error e => .error e
  | .ok fns =>
  let fns := fns ++ transitionFns
  match uWurzeln tabs fns ms with
  | .error e => .error e
  | .ok roots =>
  match uSeq ((uOhneDoppelte (fnItems.flatMap (fun (_, b) => uStartNamen 100000 b))).map
      (fun d => uStart fns "start" d)) with
  | .error e => .error e
  | .ok gestartet =>
    if !uU003 locks (fns ++ zeigerPaare.map (·.2)) invs then .error "a writer of an invariant's carrier does not hold all its locks" else
    match uRegiert fns zustaende with
    | .error e => .error e
    | .ok regiert =>
    let u : UProg :=
      { tabs := tabs, locks := locks, fns := fns, roots := roots, hands := uHandler ms, globs := globs,
        gestartet := gestartet,
        axs := axKoepfe.map (fun k => { name := k.name, params := k.types, kinds := k.kinds, res := k.axErg,
                                        gruende := (k.kanal.map (·.2)).getD 0, puts := k.puts, gputs := k.gputs }),
        annahmen := annahmen, whys := whys, sums := sums, regs := regs, invs := invs,
        zustaende := zustaende, regiert := regiert, ptrs := zeigerPaare.map (·.2), ptrKeys := zeiger,
        exportGate := Gabbro.Grammatik.Parser.Konst.checkErsetzt ms0 msSub }
    .ok (uMitBoden u)

/-- Conservative equality for every original input, including all error branches. No visibility,
    rest, permission, layout, invariant or declaration checks are removed from the phase body. -/
theorem elabU_scopes (items : List SItemTief) :
    elabU items = elabWithScopes items
      (uConstsRech (uKonstFns (uMembers items)) (uMembers items) [])
      (uAliase (uConstsRech (uKonstFns (uMembers items)) (uMembers items) []) (uMembers items) ++
        (uConstsRech (uKonstFns (uMembers items)) (uMembers items) []).map
          (fun c => (c.1, (c.2, c.2)))) := by
  rfl

/-- The actual canonical consumer sees identical complete scopes on every input admitted by
    the former collector comparison, including all error branches of runtime elaboration. -/
theorem elabWithScopes_collector_redundant (original runtime : List SItemTief)
    (h : EnvironmentCompatible original (normalizeAliases original))
    (result : DerivedScopes original) (hr : deriveScopes original = .ok result) :
    elabWithScopes runtime result.scope.values result.scope.types result.scope.functions
      (tableWithEmpty result.scope.values result.scope.types) =
      elabWithScopes runtime
        (scopes original (normalizeAliases original) (normalize_environments original h)).values
        (scopes original (normalizeAliases original) (normalize_environments original h)).types
        (scopes original (normalizeAliases original) (normalize_environments original h)).functions
        (tableWithEmpty
          (scopes original (normalizeAliases original) (normalize_environments original h)).values
          (scopes original (normalizeAliases original) (normalize_environments original h)).types) := by
  obtain ⟨old, he, hs⟩ := deriveScopes_of_compatible original h
  have same : result = old := Except.ok.inj (hr.symm.trans he)
  subst result
  rw [hs]

/-- The canonical array evaluator accepts the source-derived alias signature; the old builtin-only
    extractor cannot evaluate this same leaf. No array semantics is duplicated by the adapter. -/
theorem canonical_array_functions_zeuge :
    let items := [SItemTief.fnT
        ⟨"const", "identity", [("x", .atom "Small")], some (.atom "Small"), none, []⟩
        (.block [] (some (.ret (some (.variable "x"))))),
      .constT "VALUES" (.array (.atom "Small") (.lit 1)) (.rows [.one (.call "identity" [.lit 42])])]
    uKonstArrays [("Small", (0, 100))] (constantFunctions [("Small", (0, 100))] items) [] items =
      [("VALUES", .typed (.arr (.int 0 100) 1) (.arrCons (.lit 42) .arrNil))] ∧
    uKonstArrays [("Small", (0, 100))] (uKonstFns items) [] items = [] := by
  decide +kernel

end Gabbro.Stage0.Frontend
