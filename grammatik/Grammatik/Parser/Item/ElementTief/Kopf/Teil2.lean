module

public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Kopf.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

def beqSEingang : SEingang → SEingang → Bool
  | a, b => strEq a.name b.name && beqOptExpr a.vektor b.vektor &&
    beqOptWort a.via b.via && strEq a.arch b.arch &&
    beqSRegBindList a.regIn b.regIn &&
    beqSRegBindList a.regOut b.regOut &&
    beqWorte a.erhaelt b.erhaelt && beqWorte a.kills b.kills &&
    strEq a.stapel b.stapel && (a.perCpu == b.perCpu) &&
    beqOptExpr a.ist b.ist && beqOptWort a.nest b.nest &&
    beqWorte a.dispatch b.dispatch

/- A `check` declaration: SYNTAX.md section 13. The `can_fail`
    body rides `SAnw` (via `parseBlock`); `sonde` is the
    `counterprobe ... expects ...` pair. -/
structure SCheck where
  cname : String
  claim : String
  misst : List SExpr
  gates : List String
  canFail : SAnw
  boden : List SExpr
  sonde : Option (String × String)
  deriving Repr

def beqSCheck : SCheck → SCheck → Bool
  | a, b => strEq a.cname b.cname && strEq a.claim b.claim &&
    beqSExprList a.misst b.misst && beqWorte a.gates b.gates &&
    beqSAnw a.canFail b.canFail &&
    beqSExprList a.boden b.boden && beqOptPaarWort a.sonde b.sonde

/- Where a `syscall` rests: SYNTAX.md section 12.1 (a named
    assumption with its falsifier, or a `kernel` dispatch path). -/
inductive SHerkunft
  | assum : String → SAnKlasse → SHerkunft
  | core : List String → SHerkunft
  deriving Repr

def beqSHerkunft : SHerkunft → SHerkunft → Bool
  | .assum a b, .assum c d =>
    strEq a c && beqSAnKlasse b d
  | .core a, .core b => beqWorte a b
  | _, _ => false

/- The binding of a gate to one kernel ABI: SYNTAX.md section 12.1 `sysbind`. `codes` is the
    `errors` map (`errno [= n] => Ground`), `stack` the handed-stack registers. -/
structure SBind where
  id : SExpr
  ins : List SRegBind
  outs : List SRegBind
  stack : List String
  dirty : List String
  codes : List (String × Option SExpr × String)
  deriving Repr

def beqErrsList : List (String × Option SExpr × String) →
    List (String × Option SExpr × String) → Bool
  | [], [] => true
  | (a, n, b) :: xs, (c, m, d) :: ys =>
    strEq a c && beqOptExpr n m && strEq b d && beqErrsList xs ys
  | _, _ => false

def beqSBind : SBind → SBind → Bool
  | a, b => beqSExpr a.id b.id && beqSRegBindList a.ins b.ins &&
    beqSRegBindList a.outs b.outs && beqWorte a.stack b.stack &&
    beqWorte a.dirty b.dirty && beqErrsList a.codes b.codes

/- The contract of a gate: SYNTAX.md section 12.1 `syscontract`. -/
structure SGate where
  pre : List SExpr
  post : List SExpr
  uses : List SEffekt
  cost : Option SExpr
  deriving Repr

def beqSGate : SGate → SGate → Bool
  | a, b => beqSExprList a.pre b.pre && beqSExprList a.post b.post &&
    beqSEffektList a.uses b.uses && beqOptExpr a.cost b.cost

/- How a gate is bound: literally (`abi A arch X <sysbind> <pair>`) or through a variable
    (`via V`, SYNTAX.md section 12.3). -/
inductive SWay
  | lit : String → String → SBind → SHerkunft → SWay
  | via : String → SWay
  deriving Repr

def beqSWay : SWay → SWay → Bool
  | .lit a x b h, .lit c y d k => strEq a c && strEq x y && beqSBind b d && beqSHerkunft h k
  | .via a, .via b => strEq a b
  | _, _ => false

/- A `syscall` gate: SYNTAX.md section 12.1 `syscalldecl`. -/
structure SSyscall where
  name : String
  params : List (String × STyp)
  res : Option STyp
  fail : Option String
  way : SWay
  gate : SGate
  deriving Repr

def beqSSyscall : SSyscall → SSyscall → Bool
  | a, b => strEq a.name b.name &&
    beqParamList a.params b.params &&
    beqSTypOpt a.res b.res && beqOptWort a.fail b.fail &&
    beqSWay a.way b.way && beqSGate a.gate b.gate

def beqGoalBinds : List (String × SBind × SHerkunft) → List (String × SBind × SHerkunft) → Bool
  | [], [] => true
  | (a, b, h) :: xs, (c, d, k) :: ys =>
    strEq a c && beqSBind b d && beqSHerkunft h k && beqGoalBinds xs ys
  | _, _ => false

def beqGoalOpt : Option (String × String × List (String × SBind × SHerkunft)) →
    Option (String × String × List (String × SBind × SHerkunft)) → Bool
  | none, none => true
  | some (a, x, bs), some (b, y, cs) => strEq a b && strEq x y && beqGoalBinds bs cs
  | _, _ => false

def beqOptExprList : Option (List SExpr) → Option (List SExpr) → Bool
  | none, none => true
  | some a, some b => beqSExprList a b
  | _, _ => false

def beqGrundFallList : List (String × SExpr × String) → List (String × SExpr × String) → Bool
  | [], [] => true
  | (a, b, c) :: xs, (d, e, f) :: ys =>
    strEq a d && beqSExpr b e && strEq c f && beqGrundFallList xs ys
  | _, _ => false

/- A surface item in depth: SYNTAX.md section 1 `item`. Against
    `ast.rs` `ItemArt` (see also `SItem` in `Element.lean`, which
    shares the shape but skips every body): `modT` = `Modul`,
    `useT` = `Use`, `typeT` = `Typ`, `constT` = `Konst`, `globT` =
    `Statisch`, `fnT` = `Funktion`, `protoT` = a bodiless
    declaration (`fn …;`), `specT` = `spec fn … = pred;`,
    `asmT` = `= asm {…};`, `formatT` = `Format`, `tableT` =
    `Tabelle`, `arenaT` = `Arena`, `whyT` = `Reason`,
    `stateT` = `State`, `devT` = `Device`, `assumT` =
    `Assume`, `axiomT` = `Axiom`, `checkT` = `Check`,
    `atomT` = `Atomic`, `lockT` = `Lock`, `rcuT` = `Rcu`,
    `groupT` = `Gruppe`, `concT` = `Concurrent`, `accT` =
    `Accumulates`, `walkT` = `Walk`, `entryT` = `Entry`,
    `trustT` = `Entrust`, `startT` = `Boot`, `callT` =
    `Syscall`, `transT` = `Translator`, `profT` =
    `Profil` / `ProfilBedarf` (`bedarf` flag), `gateT` = the `when
    TESTBUILD` gate. -/
inductive SItemTief
  | modT : String → List SItemTief → SItemTief
  | useT : List String → SItemTief
  | typeT : List String → String → List STyp → List String → Option STyp → SItemTief
  | constT : String → STyp → SKonstWert → SItemTief
  | globT : Bool → String → STyp → SKonstWert → Option SExpr → Option String → Bool → SItemTief
  | fnT : FnSig → SAnw → SItemTief
  | protoT : FnSig → SItemTief
  | specT : FnSig → SExpr → SItemTief
  | asmT : FnSig → String → SItemTief
  | formatT : String → Option SExpr → Option String → List SFeld → SItemTief
  | tableT : String → Option String → Option SExpr → Option String → Option String → Bool → List STabTeil → SItemTief
  | arenaT : String → SExpr → SExpr → Option SExpr → STyp → Option (List String × SExpr) → SItemTief
  | whyT : String → List (String × SExpr × String) → Bool → SItemTief
  | stateT : String → List STrans → SItemTief
  | devT : String → List (String × STyp) → String → List SGerTeil → SItemTief
  | assumT : String → Option String → String → SAnKlasse → SItemTief
  | axiomT : String → List (String × STyp) → Option STyp → Option SExpr → List SEffekt → SAnKlasse → SItemTief
  | checkT : SCheck → SItemTief
  | atomT : String → STyp → Option (List SExpr) → Option String → Option String → SItemTief
  | lockT : String → List SExpr → SExpr → Option SExpr → Option SExpr → Option String → Option SExpr → SItemTief
  | rcuT : String → List SExpr → Option SExpr → SItemTief
  | groupT : String → List String → List SGruppenInv → SItemTief
  /-- `concurrent { m::f, m::g(a, b) }`: each start's path and its arguments (none: a function without parameters). -/
  | concT : List (List String × List SExpr) → SItemTief
  | accT : String → STyp → String → Option SExpr → SItemTief
  | walkT : SWeg → SItemTief
  | entryT : SEingang → SItemTief
  | trustT : String → String → String → List SRegBind → String → String → SItemTief
  | bootT : String → String → List SBootSchritt → List String → SItemTief
  | callT : SSyscall → SItemTief
  /-- `syscall V;`: a system call as a named variable (SYNTAX.md 12.3). -/
  | varT : String → SItemTief
  /-- `target T;` (the selection) or `target T abi A arch X { V = … }` (the bindings). -/
  | goalT : String → Option (String × String × List (String × SBind × SHerkunft)) → SItemTief
  | transT : String → FnSig → SAnw → SItemTief
  | profT : Bool → List SProfEintrag → SItemTief
  | gateT : SItemTief → SItemTief
  /-- `pub item`: the item crosses the boundary of its project (its name is visible to a dependent
      project, its signature may name only what crosses too -- `Parser/Namen/Oeffentlich.lean`). -/
  | pubT : SItemTief → SItemTief
  /-- An adapter `fn g(adaptparams) [-> T] [or R] from f [=> a [else (e) block]] clauses [prelude]
      body` (`ABSTRACTION-SYNTAX-PLAN.md` §4.1): `sig` carries the name, result, channel and
      clauses, the parameter list the raw adapter parameters, and the body is `some` block or
      `none` for the short `;` form. The desugarer (`Uebersetze/Teil18`) expands it to an
      ordinary `fnT` before elaboration. -/
  | adaptT : FnSig → List SAdaptParam → SAdapt → Option SAnw → SItemTief
  deriving Repr

def beqOptPathExpr : Option (List String × SExpr) → Option (List String × SExpr) → Bool
  | none, none => true
  | some (a, x), some (b, y) => beqWorte a b && beqSExpr x y
  | _, _ => false

mutual
def beqSItemTief : SItemTief → SItemTief → Bool
  | .modT a b, .modT c d => strEq a c && beqSItemTiefList b d
  | .useT a, .useT b => beqWorte a b
  | .typeT f1 a t1 o1 r1, .typeT f2 b t2 o2 r2 =>
    beqWorte f1 f2 && strEq a b && beqSTypList t1 t2 &&
    beqWorte o1 o2 && beqSTypOpt r1 r2
  | .constT a t v, .constT b u w =>
    strEq a b && beqSTyp t u && beqSKonstWert v w
  | .globT m1 a t v l1 s1 g1, .globT m2 b u w l2 s2 g2 =>
    (m1 == m2) && strEq a b && beqSTyp t u && beqSKonstWert v w &&
    beqOptExpr l1 l2 && beqOptWort s1 s2 && (g1 == g2)
  | .fnT s b, .fnT t d => beqFnSig s t && beqSAnw b d
  | .protoT s, .protoT t => beqFnSig s t
  | .specT s p, .specT t q => beqFnSig s t && beqSExpr p q
  | .asmT s a, .asmT t b => beqFnSig s t && strEq a b
  | .formatT a v e f, .formatT b w g h =>
    strEq a b && beqOptExpr v w && beqOptWort e g && beqSFeldList f h
  | .tableT a v c b o g p, .tableT d w f e h i q =>
    strEq a d && beqOptWort v w && beqOptExpr c f && beqOptWort b e &&
    beqOptWort o h && (g == i) && beqSTabTeilList p q
  | .arenaT a l h x t p, .arenaT b m i y u q =>
    strEq a b && beqSExpr l m && beqSExpr h i && beqOptExpr x y && beqSTyp t u &&
    beqOptPathExpr p q
  | .whyT a c e, .whyT b d f =>
    strEq a b && beqGrundFallList c d && (e == f)
  | .stateT a t, .stateT b u => strEq a b && beqSTransList t u
  | .devT a p s m, .devT b q t n =>
    strEq a b && beqParamList p q && strEq s t && beqSGerTeilList m n
  | .assumT a c t k, .assumT b d u l =>
    strEq a b && beqOptWort c d && strEq t u && beqSAnKlasse k l
  | .axiomT a p r q e k, .axiomT b s t u f l =>
    strEq a b && beqParamList p s && beqSTypOpt r t &&
    beqOptExpr q u && beqSEffektList e f && beqSAnKlasse k l
  | .checkT a, .checkT b => beqSCheck a b
  | .atomT a t p o b, .atomT c u q s d =>
    strEq a c && beqSTyp t u && beqOptExprList p q &&
    beqOptWort o s && beqOptWort b d
  | .lockT a p r h s m v, .lockT b q t i u n w =>
    strEq a b && beqSExprList p q && beqSExpr r t &&
    beqOptExpr h i && beqOptExpr s u && beqOptWort m n && beqOptExpr v w
  | .rcuT a p r, .rcuT b q s =>
    strEq a b && beqSExprList p q && beqOptExpr r s
  | .groupT a m i, .groupT b n j =>
    strEq a b && beqWorte m n && beqSGruppenInvList i j
  | .concT a, .concT b => beqStartListe a b
  | .accT a t m p, .accT b u n q =>
    strEq a b && beqSTyp t u && strEq m n && beqOptExpr p q
  | .walkT a, .walkT b => beqSWeg a b
  | .entryT a, .entryT b => beqSEingang a b
  | .trustT a b c r s t, .trustT d e f u v w =>
    strEq a d && strEq b e && strEq c f && beqSRegBindList r u &&
    strEq s v && strEq t w
  | .bootT a c s d, .bootT b e t f =>
    strEq a b && strEq c e && beqSBootSchrittList s t && beqWorte d f
  | .callT a, .callT b => beqSSyscall a b
  | .varT a, .varT b => strEq a b
  | .goalT a x, .goalT b y => strEq a b && beqGoalOpt x y
  | .transT f s b, .transT g t d =>
    strEq f g && beqFnSig s t && beqSAnw b d
  | .profT a e, .profT b f =>
    (a == b) && beqSProfEintragList e f
  | .gateT a, .gateT b => beqSItemTief a b
  | .pubT a, .pubT b => beqSItemTief a b
  | .adaptT s p a b, .adaptT t q c d =>
    beqFnSig s t && beqSAdaptParamList p q && beqSAdapt a c && beqOptAnw b d
  | _, _ => false
def beqSItemTiefList : List SItemTief → List SItemTief → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqSItemTief x y && beqSItemTiefList xs ys
  | _, _ => false
end

-- The deep readers of SYNTAX.md sections 2 (`typeexpr`), 6
-- (`fndecl` heads, `uses`, clauses) and 1/9-14 (items), each
-- with fuel: every call passes strictly less fuel, so the block
-- terminates by `f`. Against `parse.rs`: the clause order is
-- free (the loop dispatches on the head word), `requires` /
-- `ensures` take comma-separated `predlist`s, `effects` the
-- `efflist` and `costs` the `<= e ops` shape -- one by one.
-- Predicates ride `SExpr` (no `pred` reader, same cut as item 1
-- of `Anweisung.lean`); comma lists allow a trailing comma (see
-- CUTS).

/-- The assumption class: `falsifier n` or `unfalsifiable "…"`. -/
def parseKlasse : List Token → Except String (SAnKlasse × List Token)
  | .wort s :: rest =>
    if strEq s "falsifier" then match nimmName rest with
      | .ok (n, r) => .ok (.probe n, r)
      | .error e => .error e
    else if strEq s "unfalsifiable" then match nimmTextTok rest with
      | .ok (t, r) => .ok (.trust t, r)
      | .error e => .error e
    else .error "falsifier expected"
  | _ => .error "falsifier expected"

/-- A comma-separated name list (trailing commas allowed). -/
def parseNamenListe (f : Nat) : List Token →
    Except String (List String × List Token)
  | [] => .error "name expected"
  | toks => match f with
    | 0 => .error "out of fuel"
    | f + 1 => match nimmName toks with
      | .error e => .error e
      | .ok (n, rest) => match rest with
        | .zeichen "," :: rest' => match nimmName rest' with
          | .ok _ => match parseNamenListe f rest' with
            | .error e => .error e
            | .ok (ns, r) => .ok (n :: ns, r)
          | .error _ => .ok ([n], rest')
        | _ => .ok ([n], rest)
