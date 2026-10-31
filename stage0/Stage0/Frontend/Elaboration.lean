import Stage0.Frontend.Source

namespace Gabbro.Stage0.Frontend
open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- The frozen canonical elaborator's phase body, parameterized only by checked declaration
    scopes. Every check and canonical elaborator is retained. elabU_scopes below makes drift a
    kernel error; factoring here is necessary while the grammar package cannot be rebuilt. -/
def elabWithScopes (items : List SItemTief) (consts : List (String × Int))
    (alias : List (String × (Int × Int))) : Except String UProg :=
  let ms0 := uMembers items
  match uRestFehler ms0 with
  | .error e => .error e
  | .ok _ =>
  let ms := uOhneSenken ms0
  match uGlobs consts alias ms with
  | .error e => .error e
  | .ok globs0 =>
  let tnames := ms.filterMap (fun | .tableT n _ _ _ _ _ _ => some n | _ => none)
  match uSeq ((ms.filter (fun
      | .tableT _ _ _ _ _ _ _ => true | _ => false)).map (uTabelle consts alias tnames)) with
  | .error e => .error e
  | .ok tabs0 =>
  match uArenen consts alias ms with
  | .error e => .error e
  | .ok (arTabs, arGlobs) =>
  let tabs := uIdxTabs (tabs0 ++ arTabs)
  match uOptGlobs tabs (globs0 ++ arGlobs) with
  | .error e => .error e
  | .ok globs =>
  match uSeq ((ms.filter (fun
      | .lockT _ _ _ _ _ _ _ => true | _ => false)).map (uSperre globs tabs)) with
  | .error e => .error e
  | .ok locks0 =>
  match uSperrInvs consts alias globs tabs ms locks0 with
  | .error e => .error e
  | .ok locks =>
  let bewacht : String → Bool := fun c => locks.any (fun l => l.guard.any (strEq · c))
  if !tabs.all (fun t => !t.shared || bewacht t.name) then .error "shared table without a guard" else
  if !globs.all (fun g => !g.shared || g.atomic || bewacht g.name) then .error "shared static without a guard" else
  if !globs.all (fun g => g.nutzlast.all (fun n => globs.any (fun h => strEq h.name n))) then
    .error "payload names no static" else
  let fnItems := ms.filterMap (fun
    | .fnT sig koerper => if strEq sig.art "const" then none else some (sig, koerper)
    | _ => none)
  match uWhys ms with
  | .error e => .error e
  | .ok whys =>
  match uSums alias ms with
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
  match uSeq (ms.filterMap (fun | .stateT n ts => some (uZustand n ts) | _ => none)) with
  | .error e => .error e
  | .ok zustaende =>
  let devs := ms.filterMap (fun | .devT n _ _ _ => some n | _ => none)
  let zeiger := uOhneDoppelte (fnItems.flatMap (fun (s, b) => uZeigerTexte (s.params.map (·.2)) ++ uZeigerAnw 100000 b))
  let zb := fnItems.length
  match uSeq ((List.range zeiger.length).zip zeiger |>.map (fun (j, r) =>
      elabZeigerTyp consts alias tabs locks globs whys sums zeiger zb j r)) with
  | .error e => .error e
  | .ok zeigerPaare =>
  match uSeq (fnItems.map (fun (s, _) => elabKopf consts alias tabs locks globs whys sums s devs zeiger zb)) with
  | .error e => .error e
  | .ok [] => .error "unit without a fn"
  | .ok kopfPaare =>
  match uSeq ((ms.filterMap uFremdSig).map (fun (sig, asm) => elabAxKopf alias tabs whys globs asm sig)) with
  | .error e => .error e
  | .ok axKoepfe0 =>
  match uSeq ((ms.filterMap (fun | .callT sc => some sc | _ => none)).map (elabGateKopf alias tabs whys globs)) with
  | .error e => .error e
  | .ok gateKoepfe =>
  let axKoepfe := axKoepfe0 ++ gateKoepfe
  let koepfe := kopfPaare.map (·.1) ++ axKoepfe ++ zeigerPaare.map (·.1)
  let annahmen := ms.filterMap (fun | .assumT n _ _ _ => some n | _ => none)
  match uSeq (fnItems.map (fun (s, b) =>
      elabUFunktion consts alias tabs locks globs koepfe s b annahmen whys sums devs regs zustaende zeiger zb
        (ms.filterMap (fun | .specT sg body => some (sg.name, sg.params.map (·.1), body) | _ => none))
        (uKonstArrays alias (uKonstFns ms) consts ms))) with
  | .error e => .error e
  | .ok fns =>
  match uWurzeln tabs fns ms with
  | .error e => .error e
  | .ok roots =>
  match uSeq ((uOhneDoppelte (fnItems.flatMap (fun (_, b) => uStartNamen 100000 b))).map
      (fun d => uStart fns "start" d)) with
  | .error e => .error e
  | .ok gestartet =>
    if !uU003 locks (fns ++ zeigerPaare.map (·.2)) invs then .error "a writer of an invariant's carrier does not hold all its locks" else
    match uRegiert fns with
    | .error e => .error e
    | .ok regiert =>
    let u : UProg :=
      { tabs := tabs, locks := locks, fns := fns, roots := roots, hands := uHandler ms, globs := globs,
        gestartet := gestartet,
        axs := axKoepfe.map (fun k => { name := k.name, params := k.types, kinds := k.kinds, res := k.axErg,
                                        gruende := (k.kanal.map (·.2)).getD 0, puts := k.puts, gputs := k.gputs }),
        annahmen := annahmen, whys := whys, sums := sums, regs := regs, invs := invs,
        zustaende := zustaende, regiert := regiert, ptrs := zeigerPaare.map (·.2), ptrKeys := zeiger }
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
    elabWithScopes runtime result.scope.values result.scope.types =
      elabWithScopes runtime
        (scopes original (normalizeAliases original) (normalize_environments original h)).values
        (scopes original (normalizeAliases original) (normalize_environments original h)).types := by
  obtain ⟨old, he, hs⟩ := deriveScopes_of_compatible original h
  have same : result = old := Except.ok.inj (hr.symm.trans he)
  subst result
  rw [hs]

end Gabbro.Stage0.Frontend
