module
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Elaboration
public import Grammatik.Parser.Elab.Uebersetze.Kontext.FunctionMemo
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- The same unit elaboration, sharing one head index across all ordinary functions. -/
def elabExpandedWithScopesFast (msE : List SItemTief) (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (functions : List UKonstFn)
    (tableLowering : List String → SItemTief → Except String UTab)
    (staticRequirements : List (STyp × String) := []) (ort : Bool := false) (narrow : Bool := false) :
    Except String UProg :=
  match guestSources msE with
  | .error e => .error e
  | .ok (guests, msE) =>
  match uRestFehler msE with
  | .error e => .error e
  | .ok _ =>
  match Gabbro.Grammatik.Parser.Konst.checkSourceConstants msE with
  | .error error => .error error
  | .ok () =>
  let ms := uOhneSenken msE
  match uGlobs consts alias ms with
  | .error e => .error e
  | .ok globs0 =>
  -- Nominal space binders and linear owner marks have independent namespaces.
  let spaces := uSpaces ms
  let eigner := uOhneDoppelte (uEignerMs ms)
  let linear := uLinearNamen ms
  match uMarkOrders ms with
  | .error error => .error error
  | .ok markOrders =>
  match uSeq ((ms.filterMap (fun | .tableT _ _ _ _ o _ _ _ => o | _ => none)).map (uPruefEigner linear)) with
  | .error e => .error e
  | .ok _ =>
  let tnames := ms.filterMap (fun | .tableT n _ _ _ _ _ _ _ => some n | _ => none)
  match uSeq ((ms.filter (fun
      | .tableT _ _ _ _ _ _ _ _ => true | _ => false)).map
        (uTabelleMitRaum spaces (tableLowering tnames))) with
  | .error e => .error e
  | .ok tabs0 =>
  match uArenen consts alias ms with
  | .error e => .error e
  | .ok (arTabs, arGlobs) =>
  let tabs := uIdxTabs (tabs0 ++ arTabs ++ uArrayCarriers alias msE)
  match uOptGlobs tabs (globs0 ++ arGlobs) with
  | .error e => .error e
  | .ok globs =>
  match uTypes consts alias tabs msE eigner spaces with
  | .error e => .error e
  | .ok valueScope =>
  let constants := uKonstArrays alias functions consts ms
    (uRecordConstantTypes valueScope.records) (uRecordConstant valueScope.records alias functions consts) true
  -- C16: every `check` item elaborates now, with its generated probe below.
  match uChecks tabs globs ms with
  | .error e => .error e
  | .ok checks =>
  match uSeq ((ms.filter (fun
      | .lockT _ _ _ _ _ _ _ => true | _ => false)).map (fun item => uSperre globs tabs item consts)) with
  | .error e => .error e
  | .ok locks0 =>
  match uSperrInvs consts alias globs tabs ms locks0 with
  | .error e => .error e
  | .ok locks =>
  match uAkkuErweiterung consts alias ((locks.map (fun l => l.rank)).foldl max 0 + 1) ms with
  | .error e => .error e
  | .ok (akkuGlobs, akkuLocks) =>
  let globs := globs ++ akkuGlobs
  let locks := locks ++ akkuLocks
  let bewacht : String → Bool := fun c => locks.any (fun l => l.guard.any (strEq · c))
  if !tabs.all (fun t => !t.shared || bewacht t.name) then .error "shared table without a guard" else
  if !globs.all (fun g => !g.shared || g.atomic || bewacht g.name) then .error "shared static without a guard" else
  if !globs.all (fun g => g.nutzlast.all (fun n => globs.any (fun h => strEq h.name n))) then
    .error "payload names no static" else
  -- C17: certified call-site substitution runs here, after the checked
  -- const/type views and BEFORE `fnItems`/`elabUFunktion` and the export
  -- metadata gate. Failing substitutions keep their refusal.
  match Gabbro.Grammatik.Parser.Konst.konstErsetzePipeline ms with
  | .error e => .error e
  | .ok msSub =>
  let fnItems := msSub.filterMap (fun
    | .fnT sig koerper => if strEq sig.art "const" then none else some (sig, koerper)
    | _ => none)
  let annahmen := ms.filterMap (fun | .assumT n _ _ _ => some n | _ => none)
  -- C15 use export: query/update/fold per accumulator, then expand uses.
  match uAkkuVorlauf consts alias ms fnItems with
  | .error e => .error e
  | .ok (fnItems, akkuFrage, fremdPaare) =>
  match uWhys ms alias with
  | .error e => .error e
  | .ok whys =>
  match uSums alias ms tabs spaces eigner with
  | .error e => .error e
  | .ok sums =>
  match uSumGlobs consts sums ms globs with
  | .error e => .error e
  | .ok globs =>
  match uSumTabs sums (uRecordTabs valueScope.records tabs) with
  | .error e => .error e
  | .ok tabs =>
  match uRegs alias consts tabs globs ms with
  | .error e => .error e
  | .ok regs =>
  match uInvs consts alias tabs locks globs ms with
  | .error e => .error e
  | .ok invs =>
  let transitionCtx : UCtx :=
    { names := []
      kinds := []
      types := []
      tabs := tabs
      locks := locks
      held := []
      res := none
      fname := "transition"
      alias := alias
      lits := consts
      globs := globs
      spaces := spaces
      records := valueScope.records
      namedTypes := valueScope.types
      eigner := eigner }
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
  -- Preserve both predicate syntax and its declared parameter types until typed elaboration.
  let specFns := ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none)
  let specTypen := ms.filterMap (fun | .specT sg _ => some (sg.name, sg.params.map (·.2)) | _ => none)
  let zeiger := uOhneDoppelte (fnItems.flatMap (fun (s, b) => uZeigerTexte (s.params.map (·.2)) ++ uZeigerAnw 100000 b))
  let zb := fnItems.length + transitionFns.length
  match uSeq ((List.range zeiger.length).zip zeiger |>.map (fun (j, r) =>
      elabZeigerTyp consts alias tabs locks globs whys sums zeiger zb j r spaces valueScope.types eigner specFns specTypen)) with
  | .error e => .error e
  | .ok zeigerPaare =>
  match uSeq (fnItems.map (fun (s, _) => mitOrt ort s.name (elabKopf consts alias tabs locks globs whys sums s devs zeiger zb spaces valueScope.types eigner))) with
  | .error e => .error e
  | .ok [] => .error "unit without a fn"
  | .ok kopfPaare =>
  match uSeq (fremdPaare.map (fun (sig, asm) => elabAxKopf alias tabs whys globs asm (eigner := eigner) (spaces := spaces) sig)) with
  | .error e => .error e
  | .ok axKoepfe0 =>
  match uSeq ((ms.filterMap (fun | .callT sc => some sc | _ => none)).map (fun sc => elabGateKopf alias tabs whys globs sc (eigner := eigner) (spaces := spaces))) with
  | .error e => .error e
  | .ok gateKoepfe =>
  let axKoepfe := axKoepfe0 ++ gateKoepfe ++ akkuFrage
  match uSeq (axKoepfe.map (fun k => guestForeign alias consts tabs globs whys annahmen guests k (eigner := eigner) (spaces := spaces))) with
  | .error e => .error e
  | .ok axs =>
  let koepfe := kopfPaare.map (·.1) ++ axKoepfe ++ zeigerPaare.map (·.1)
  let headMemo := UHeadMemo.von koepfe
  -- C16: every `can_fail` body elaborates into its generated Boolean producer now.
  match uProbeFns consts alias tabs locks globs koepfe whys sums devs regs zustaende specFns constants zeiger zb (fnItems.map (fun (s, _) => s.name) ++ axKoepfe.map (·.name) ++ zeigerPaare.map (fun p => p.1.name)) (ms.filterMap (fun | .checkT c => some c | _ => none)) spaces eigner specTypen with
  | .error e => .error e
  | .ok probeFns =>
  match uSeq (fnItems.map (fun (s, b) =>
      mitOrt ort s.name <| elabUFunktionMemo headMemo (spaces := spaces) (valueScope := valueScope) (eigner := eigner) (specTypen := specTypen) (narrow := narrow) consts alias tabs locks globs koepfe s b annahmen whys sums devs regs zustaende zeiger zb
        specFns
        constants)) with
  | .error e => .error e
  | .ok fns =>
  let fns := fns ++ transitionFns ++ probeFns
  match uSondenFns fns axKoepfe checks with
  | .error e => .error e
  | .ok sondeFns =>
  let fns := fns ++ sondeFns
  -- C16: every gate of every check derives its Duty-threading wrapper, over a
  -- unit function or a C08 foreign body (the elaborated foreign heads).
  match uTorHuellen fns axKoepfe checks with
  | .error e => .error e
  | .ok torFns =>
  let marken := uMarken ms checks
  match uMarkenPruef marken (fns ++ torFns ++ zeigerPaare.map (·.2)) with
  | .error e => .error e
  | .ok _ =>
  match uGibtPruef (ms.filterMap (fun | .tableT _ _ _ _ o _ _ _ => o | _ => none)) (fns ++ torFns ++ zeigerPaare.map (·.2)) with
  | .error e => .error e
  | .ok _ =>
  match uLeihtPruef (ms.filterMap (fun | .tableT _ _ _ _ o _ _ _ => o | _ => none)) (fns ++ torFns ++ zeigerPaare.map (·.2)) with
  | .error e => .error e
  | .ok _ =>
  match uBewegtPruef (ms.filterMap (fun | .tableT _ _ _ _ o _ _ _ => o | _ => none)) (fns ++ torFns ++ zeigerPaare.map (·.2)) with
  | .error e => .error e
  | .ok _ =>
  match uMintPruef (ms.filterMap (fun | .tableT _ _ _ _ o _ _ _ => o | _ => none)) (fns ++ torFns ++ zeigerPaare.map (·.2)) with
  | .error e => .error e
  | .ok _ =>
  match uWurzeln spaces tabs fns ms with
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
      { tabs := tabs
        locks := locks
        fns := fns ++ torFns
        roots := roots
        hands := uHandler ms
        globs := globs
        gestartet := gestartet
        axs := axs
        guests := guests
        annahmen := annahmen
        whys := whys
        sums := sums
        regs := regs
        invs := invs
        zustaende := zustaende
        regiert := regiert
        ptrs := zeigerPaare.map (·.2)
        ptrKeys := zeiger
        exportGate := Gabbro.Grammatik.Parser.Konst.checkErsetzt msE msSub
        checks := checks
        marken := marken
        markOrders := markOrders
        spaces := spaces
        records := valueScope.records
        eigner := eigner }
    let u := uMitBoden u
    match Generic.checkStaticConformance consts alias u staticRequirements valueScope.types specFns specTypen with
    | .error error => .error error
    | .ok () => .ok u

@[csimp] theorem elabExpandedWithScopes_eq_fast :
    @elabExpandedWithScopes = @elabExpandedWithScopesFast := by
  funext items consts alias functions tableLowering requirements ort narrow
  unfold elabExpandedWithScopes elabExpandedWithScopesFast
  simp only [elabUFunktionMemo_eq] <;> rfl

end Gabbro.Grammatik.Parser.Uebersetze
