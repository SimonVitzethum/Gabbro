import Grammatik.Bausteine.Arena.Ownership.Body.Check.Ops

/-! **The executable admission check** of the ownership body judgment. One
structural pass over a body computes the context after every statement:
expressions are access-checked, branches joined, loops checked from their
head context, calls checked against the interfaces (pointer calls against
the common interface of every fitting function in the enumeration `fs`),
and the executed allocator forms recognised on their statements. A body
passes when the pass returns a context (`Option`) or `true`. Soundness
(`Check/Sound.lean`): a passing body has a derivation of the judgment. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

section Checker

variable (A : FreiForm D) (I : Interfaces A) (fs : List D.Fn)

/-- The interface a function pointer of signature `n` is checked against:
that of the first fitting function in `fs`. -/
def sigIface (n : Nat) : Modes (D.sigNr n).params × Bool :=
  match fs.find? (fun f => D.passt f n) with
  | some f => (modesOf _ (modeList (I f).parameters), Flow.Output.isOwner (I f).output)
  | none => (modesOf _ [], false)

/-- Every fitting function in `fs` has the signature interface. -/
def sigCompatB (n : Nat) (J : Modes (D.sigNr n).params) (owner : Bool) : Bool :=
  fs.all fun f => !(D.passt f n) ||
    (modeList (I f).parameters == modeList J && Flow.Output.isOwner (I f).output == owner)

/-- A field read that is the free-list link of the variable at bottom position `p`. -/
def slotIsLink {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (p : Nat) : Bool :=
  match exprSlotRead e with
  | some ⟨t, f, q⟩ => if h : t = A.tab then decide (h ▸ f = A.nxt) && q == p else false
  | none => false

/-- The outcome of checking a statement or block: `none` refuses, `some none`
never falls through (every context may follow), `some (some c)` falls
through in `c`. -/
abbrev Out := Option (Option Context)

/-- Join two branch outcomes; a branch that never falls through joins anything. -/
def joinR : Out → Out → Out
  | some none, r => r
  | r, some none => r
  | some (some a), some (some b) => (joinB a b).map some
  | _, _ => none

/-- Continue after a statement. -/
def seqR (r : Out) (f : Context → Out) : Out :=
  match r with
  | some (some c) => f c
  | some none => some none
  | none => none

def mapR (f : Context → Context) : Out → Out
  | some (some c) => some (some (f c))
  | r => r

def liveB (r : Out) : Bool := r.isSome

/-- A fall-through context (or none) is weaker-checked against the loop head. -/
def backB (kk : Context) : Out → Bool
  | some (some c1) => weakerB kk c1
  | some none => true
  | none => false

variable {V : Vertrag D} (out : Flow.Output A V.erg)

mutual

def chkS : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Stmt D V l Γ Λ Λ' → (k c : Context) → Out
  | _, _, _, _, .assignSlot t f i e _ _, _, c =>
    if decide (NotLink A t f) && checkExpression A c i && checkExpression A c e && storeCheck A c t i then
      some (some c) else none
  | _, _, _, _, .assignThru p t _ f i e _ _, _, c =>
    if decide (NotLink A t f) && checkExpression A c p && checkExpression A c i && checkExpression A c e &&
      storeCheck A c t i then some (some c) else none
  | _, _, _, _, .assignGlob g e _ _, _, c =>
    if decide (NotMetaGlob A g) && checkExpression A c e then some (some c) else none
  | _, _, _, _, .putBytes t _ _ _ i _ _ e _ _, _, c =>
    if decide (t ≠ A.tab) && checkExpression A c i && checkExpression A c e then some (some c) else none
  | _, _, _, _, .assignVar x e, _, c =>
    if checkExpression A c e then some (some (c.assign x (origin c e))) else none
  | _, _, _, _, .shift t f _ i _ _ _ _ _ _, _, c =>
    if decide (NotLink A t f) && checkExpression A c i && storeCheck A c t i then some (some c) else none
  | _, _, _, _, .ite cond t e, k, c =>
    if checkExpression A c cond then joinR (chkB t k c) (chkB e k c) else none
  | _, _, _, _, .onOption o p a, k, c =>
    if checkExpression A c o then joinR (mapR Context.drop (chkB p k (c.bind none))) (chkB a k c) else none
  | _, _, _, _, .onTag v arms, k, c => if checkExpression A c v then chkArms arms k c else none
  | _, _, _, _, .onWhy r arms, k, c => if checkExpression A c r then chkGrund arms k c else none
  | _, _, _, _, .call f args _ _, _, c =>
    if checkArguments A c args && planFits c (modeList (I f).parameters) (originList c args) then
      some (some (dropContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output))
    else none
  | _, _, _, _, .callInd (n := n) p args _ _, _, c =>
    if checkExpression A c p && checkArguments A c args &&
      sigCompatB A I fs n (sigIface A I fs n).1 (sigIface A I fs n).2 &&
      planFits c (modeList (sigIface A I fs n).1) (originList c args) then
      some (some (dropContextB (c.afterCall (modeList (sigIface A I fs n).1) (originList c args))
        (sigIface A I fs n).2))
    else none
  | _, _, _, _, .locks _ _ body, k, c => chkB body k c
  | _, _, _, _, .breaking _ body, k, c => chkB body k c
  | _, _, _, _, .traverse _ inv body, _, c =>
    let kk := loopCtx c (assignsB body)
    if checkExpression A kk inv && backB kk (mapR Context.drop (chkB body kk (kk.bind none))) then
      some (some kk) else none
  | _, _, _, _, .retry _ bis body u, k, c =>
    let kk := loopCtx c (assignsB body ++ assignsB u)
    if checkExpression A kk bis && backB kk (chkB body kk kk) && backB kk (chkB u k kk) then
      some (some kk) else none
  | _, _, _, _, .forever _ inv body, _, c =>
    let kk := loopCtx c (assignsB body)
    if checkExpression A kk inv && backB kk (chkB body kk kk) then some (some kk) else none
  | _, _, _, _, .axiomCall a args _ _ _ _ _, _, c =>
    if decide (AxiomFree A a) && checkArguments A c args then some (some c) else none
  | _, _, _, _, .regWrite _ _ e, _, c => if checkExpression A c e then some (some c) else none
  | _, _, _, _, .transition .., _, c => some (some c)
  | _, _, _, _, .publish g e _ _ _ _, _, c =>
    if decide (NotMetaGlob A g) && checkExpression A c e then some (some c) else none
  | _, _, _, _, .advances .., _, c => some (some c)
  | _, _, _, _, .retires .., _, c => some (some c)
  | _, _, _, _, .ret e _, _, c => if out.check A c e then some none else none
  | _, _, _, _, .retWhy _ _, _, c => if finish c none then some none else none
  | _, _, _, _, .leave _, k, c => if exitsB k c then some none else none
  | _, _, _, _, .next _, k, c => if exitsB k c then some none else none

def chkB : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    Block D V l Γ Λ Λ' → (k c : Context) → Out
  | _, _, _, _, .nil, _, c => some (some c)
  | _, _, _, _, .cons s rest, k, c =>
    let generic := seqR (chkS s k c) (fun c1 => chkB rest k c1)
    match s with
    | .assignSlot t f i e _ _ =>
      match rest with
      | .cons (.assignGlob g e2 _ _) rest' =>
        if (if ht : t = A.tab then decide (ht ▸ f = A.nxt) else false) && (exprVarPos i).isSome &&
            exprVarPos e2 == exprVarPos i && exprGlob e == some A.kopf && decide (g = A.kopf) then
          match consume c i with
          | some (c2, _) => chkB rest' k c2
          | none => none
        else generic
      | _ => generic
    | _ => generic
  | _, _, _, _, .bind e rest, k, c =>
    if checkExpression A c e then mapR Context.drop (chkB rest k (c.bind (origin c e))) else none
  | _, _, _, _, .bindCall f args _ _ _ rest, k, c =>
    if checkArguments A c args && planFits c (modeList (I f).parameters) (originList c args) then
      mapR Context.drop (chkB rest k (resultContext (c.afterCall (modeList (I f).parameters) (originList c args))
        (I f).output))
    else none
  | _, _, _, _, .bindCallInd (n := n) p args _ _ _ rest, k, c =>
    if checkExpression A c p && checkArguments A c args &&
      sigCompatB A I fs n (sigIface A I fs n).1 (sigIface A I fs n).2 &&
      planFits c (modeList (sigIface A I fs n).1) (originList c args) then
      mapR Context.drop (chkB rest k (resultContextB (c.afterCall (modeList (sigIface A I fs n).1)
        (originList c args)) (sigIface A I fs n).2))
    else none
  | _, _, _, _, .bindCallElse f args _ _ _ err rest, k, c =>
    if checkArguments A c args && planFits c (modeList (I f).parameters) (originList c args) &&
      chkE err k ((c.afterCall (modeList (I f).parameters) (originList c args)).bind none) then
      mapR Context.drop (chkB rest k (resultContext (c.afterCall (modeList (I f).parameters) (originList c args))
        (I f).output))
    else none
  | _, _, _, _, .bindAxiom a args _ _ _ _ _ rest, k, c =>
    if decide (AxiomFree A a) && checkArguments A c args then mapR Context.drop (chkB rest k (c.bind none))
    else none
  | _, _, _, _, .bindAxiomElse a args _ _ _ _ _ _ err rest, k, c =>
    if decide (AxiomFree A a) && checkArguments A c args && chkE err k (c.bind none) then
      mapR Context.drop (chkB rest k (c.bind none))
    else none
  | _, _, _, _, .regRead _ _ rest, k, c => mapR Context.drop (chkB rest k (c.bind none))
  | _, _, _, _, .regReadElse _ _ zusage sonst rest, k, c =>
    if checkExpression A (c.bind none) zusage && chkE sonst k c then mapR Context.drop (chkB rest k (c.bind none))
    else none
  | _, _, _, _, .awaits _ _ _ _ _ rest, k, c => mapR Context.drop (chkB rest k (c.bind none))
  | _, _, _, _, .exchange g neu _ _ rest, k, c =>
    if decide (NotMetaGlob A g) && checkExpression A (c.bind none) neu then
      mapR Context.drop (chkB rest k (c.bind none))
    else none
  | _, Γ, _, _, .narrow e lo' hi' voll rest, k, c =>
    let generic := if checkExpression A c e && chkE voll k c then
      mapR Context.drop (chkB rest k (c.bind (origin c e))) else none
    match rest with
    | .cons (.assignSlot t f i ev _ _) rest1 =>
      match rest1 with
      | .cons (.assignGlob g e2 _ _) rest' =>
        if exprGlob e == some A.zaehl && decide (hi' < D.count A.tab) && decide (NotLink A t f) &&
            decide (g = A.zaehl) && exprSucc e2 == some Γ.length && checkExpression A c.bindFresh i &&
            checkExpression A c.bindFresh ev && storeCheck A c.bindFresh t i then
          if chkE voll k c then mapR Context.drop (chkB rest' k c.bindFresh) else none
        else generic
      | _ => generic
    | .cons (.assignGlob g e2 _ _) rest1 =>
      match rest1 with
      | .cons (.assignSlot t f i ev _ _) rest' =>
        if exprGlob e == some A.kopf && decide (hi' < D.count A.tab) && decide (g = A.kopf) &&
            slotIsLink A e2 Γ.length && decide (NotLink A t f) && checkExpression A c.bindFresh i &&
            checkExpression A c.bindFresh ev && storeCheck A c.bindFresh t i then
          if chkE voll k c then mapR Context.drop (chkB rest' k c.bindFresh) else none
        else generic
      | _ => generic
    | _ => generic
  | _, _, _, _, .check cond sonst rest, k, c =>
    if checkExpression A c cond && chkE sonst k c then chkB rest k c else none
  | _, _, _, _, .float _ a b _ _ rest, k, c =>
    if checkExpression A c a && checkExpression A c b then mapR Context.drop (chkB rest k (c.bind none))
    else none
  | _, _, _, _, .floatLit _ _ _ rest, k, c => mapR Context.drop (chkB rest k (c.bind none))
  | _, _, _, _, .floatOf e _ _ rest, k, c =>
    if checkExpression A c e then mapR Context.drop (chkB rest k (c.bind none)) else none
  | _, _, _, _, .floatNarrow e _ _ sonst rest, k, c =>
    if checkExpression A c e && chkE sonst k c then mapR Context.drop (chkB rest k (c.bind none)) else none

def chkE : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Endblock D V l Γ Λ → (k c : Context) → Bool
  | _, _, _, .ret e _, _, c => out.check A c e
  | _, _, _, .retWhy _ _, _, c => finish c none
  | _, _, _, .leave _, k, c => exitsB k c
  | _, _, _, .next _, k, c => exitsB k c
  | _, _, _, .cons s rest, k, c =>
    match chkS s k c with
    | some (some c1) => chkE rest k c1
    | some none => true
    | none => false
  | _, _, _, .bind e rest, k, c => checkExpression A c e && chkE rest k (c.bind (origin c e))
  | _, _, _, .bindCall f args _ _ _ rest, k, c =>
    checkArguments A c args && planFits c (modeList (I f).parameters) (originList c args) &&
      chkE rest k (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output)
  | _, _, _, .bindCallElse f args _ _ _ err rest, k, c =>
    checkArguments A c args && planFits c (modeList (I f).parameters) (originList c args) &&
      chkE err k ((c.afterCall (modeList (I f).parameters) (originList c args)).bind none) &&
      chkE rest k (resultContext (c.afterCall (modeList (I f).parameters) (originList c args)) (I f).output)
  | _, _, _, .bindAxiom a args _ _ _ _ _ rest, k, c =>
    decide (AxiomFree A a) && checkArguments A c args && chkE rest k (c.bind none)
  | _, _, _, .bindAxiomElse a args _ _ _ _ _ _ err rest, k, c =>
    decide (AxiomFree A a) && checkArguments A c args && chkE err k (c.bind none) && chkE rest k (c.bind none)
  | _, _, _, .regRead _ _ rest, k, c => chkE rest k (c.bind none)
  | _, _, _, .regReadElse _ _ zusage sonst rest, k, c =>
    checkExpression A (c.bind none) zusage && chkE sonst k c && chkE rest k (c.bind none)
  | _, _, _, .awaits _ _ _ _ _ rest, k, c => chkE rest k (c.bind none)
  | _, _, _, .bindCallInd (n := n) p args _ _ _ rest, k, c =>
    checkExpression A c p && checkArguments A c args &&
      sigCompatB A I fs n (sigIface A I fs n).1 (sigIface A I fs n).2 &&
      planFits c (modeList (sigIface A I fs n).1) (originList c args) &&
      chkE rest k (resultContextB (c.afterCall (modeList (sigIface A I fs n).1) (originList c args))
        (sigIface A I fs n).2)

def chkArms : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} →
    {cs : List (Option (Int × Int))} → Arms D V l Γ Λ Λ' cs → (k c : Context) → Out
  | _, _, _, _, _, .nil, _, _ => some none
  | _, _, _, _, ca :: _, .cons b rest, k, c =>
    joinR (mapR (fun c1 => armDrop c1 ca) (chkB b k (armBind c ca))) (chkArms rest k c)

def chkGrund : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → {n : Nat} →
    GrundArms D V l Γ Λ Λ' n → (k c : Context) → Out
  | _, _, _, _, _, .nil, _, _ => some none
  | _, _, _, _, _, .cons b rest, k, c => joinR (chkB b k c) (chkGrund rest k c)

end

end Checker

end Gabbro.Grammatik.ArenaOwnership.Body
