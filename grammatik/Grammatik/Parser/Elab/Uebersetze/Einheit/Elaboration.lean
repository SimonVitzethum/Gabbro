module
public import Grammatik.Parser.Elab.Uebersetze.Einheit.Signatures
public import Grammatik.Parser.Elab.Uebersetze.Akku.Expand
public import Grammatik.Parser.Elab.Generic.StaticConformance
public import Grammatik.Parser.Elab.Uebersetze.Guest.Source
@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze
set_option maxRecDepth 100000

/-- One shared phase body over expanded declarations. Stage 0 supplies certified source scopes
    and its checked empty-table adapter; canonical export supplies its ordinary collectors.
    Runtime checks, declaration expansion and G elaboration are never copied into Stage 0. -/
def elabExpandedWithScopes (msE : List SItemTief) (consts : List (String × Int))
    (alias : List (String × (Int × Int))) (functions : List UKonstFn)
    (tableLowering : List String → SItemTief → Except String UTab)
    (staticRequirements : List (STyp × String) := []) : Except String UProg :=
  match guestSources msE with
  | .error e => .error e
  | .ok (guests, msE) =>
  match uRestFehler msE with
  | .error e => .error e
  | .ok _ =>
  match ExportMetadata.checkConstants msE with
  | .error error => .error error
  | .ok () =>
  let ms := uOhneSenken msE
  match uGlobs consts alias ms with
  | .error e => .error e
  | .ok globs0 =>
  let spaces := ["normal"] ++ uOhneDoppelte ((ms.filterMap (fun | .tableT _ _ _ _ space _ _ => space | _ => none)).filter (fun n => !strEq n "normal"))
  let tnames := ms.filterMap (fun | .tableT n _ _ _ _ _ _ => some n | _ => none)
  match uSeq ((ms.filter (fun
      | .tableT _ _ _ _ _ _ _ => true | _ => false)).map (tableLowering tnames)) with
  | .error e => .error e
  | .ok tabs0 =>
  match uArenen consts alias ms with
  | .error e => .error e
  | .ok (arTabs, arGlobs) =>
  let tabs := uIdxTabs ((tabs0.map (fun t => { t with space := ((ms.find? (fun | .tableT n .. => strEq n t.name | _ => false)).bind (fun | .tableT _ _ _ _ s _ _ => s | _ => none)).map (fun n => (spaces.zipIdx.find? (fun p => strEq p.1 n)).map (·.2) |>.getD 0) |>.getD 0 })) ++ arTabs ++ uArrayCarriers alias msE)
  match uOptGlobs tabs (globs0 ++ arGlobs) with
  | .error e => .error e
  | .ok globs =>
  match uTypes consts alias tabs msE with
  | .error e => .error e
  | .ok valueScope =>
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
  match uSums alias ms tabs spaces with
  | .error e => .error e
  | .ok sums =>
  match uSumGlobs consts sums ms globs with
  | .error e => .error e
  | .ok globs =>
  match uSumTabs sums tabs with
  | .error e => .error e
  | .ok tabs =>
  match uRegs alias consts tabs globs ms with
  | .error e => .error e
  | .ok regs =>
  match uInvs consts alias tabs locks globs ms with
  | .error e => .error e
  | .ok invs =>
  let transitionCtx : UCtx := { names := [], kinds := [], types := [], tabs, locks, held := [], res := none, fname := "transition", alias, lits := consts, globs, records := valueScope.records, namedTypes := valueScope.types }
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
      elabZeigerTyp consts alias tabs locks globs whys sums zeiger zb j r spaces valueScope.types)) with
  | .error e => .error e
  | .ok zeigerPaare =>
  match uSeq (fnItems.map (fun (s, _) => elabKopf consts alias tabs locks globs whys sums s devs zeiger zb spaces valueScope.types)) with
  | .error e => .error e
  | .ok [] => .error "unit without a fn"
  | .ok kopfPaare =>
  match uSeq (fremdPaare.map (fun (sig, asm) => elabAxKopf alias tabs whys globs asm sig)) with
  | .error e => .error e
  | .ok axKoepfe0 =>
  match uSeq ((ms.filterMap (fun | .callT sc => some sc | _ => none)).map (elabGateKopf alias tabs whys globs)) with
  | .error e => .error e
  | .ok gateKoepfe =>
  let axKoepfe := axKoepfe0 ++ gateKoepfe ++ akkuFrage
  match uSeq (axKoepfe.map (guestForeign alias consts tabs globs whys annahmen guests)) with
  | .error e => .error e
  | .ok axs =>
  let koepfe := kopfPaare.map (·.1) ++ axKoepfe ++ zeigerPaare.map (·.1)
  -- C16: every `can_fail` body elaborates into its generated Boolean producer now.
  match uProbeFns consts alias tabs locks globs koepfe whys sums devs regs zustaende (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none)) (uKonstArrays alias functions consts ms) zeiger zb (fnItems.map (fun (s, _) => s.name) ++ axKoepfe.map (·.name) ++ zeigerPaare.map (fun p => p.1.name)) (ms.filterMap (fun | .checkT c => some c | _ => none)) with
  | .error e => .error e
  | .ok probeFns =>
  match uSeq (fnItems.map (fun (s, b) =>
      elabUFunktion (spaces := spaces) (valueScope := valueScope) consts alias tabs locks globs koepfe s b annahmen whys sums devs regs zustaende zeiger zb
        (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none))
        (uKonstArrays alias functions consts ms))) with
  | .error e => .error e
  | .ok fns =>
  let fns := fns ++ transitionFns ++ probeFns
  match uTorHuellen fns checks with
  | .error e => .error e
  | .ok torFns =>
  let marken := uMarken ms checks
  match uMarkenPruef marken (fns ++ torFns) with
  | .error e => .error e
  | .ok _ =>
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
      { tabs := tabs, locks := locks, fns := fns ++ torFns, roots := roots, hands := uHandler ms, globs := globs, gestartet := gestartet, axs := axs, guests := guests, annahmen := annahmen, whys := whys, sums := sums, regs := regs, invs := invs, zustaende := zustaende, regiert := regiert, ptrs := zeigerPaare.map (·.2), ptrKeys := zeiger, exportGate := Gabbro.Grammatik.Parser.Konst.checkErsetzt msE msSub, checks := checks, marken := marken, spaces := spaces, records := valueScope.records }
    let u := uMitBoden u
    match Generic.checkStaticConformance consts alias u staticRequirements valueScope.types with
    | .error error => .error error
    | .ok () => .ok u

end Gabbro.Grammatik.Parser.Uebersetze
