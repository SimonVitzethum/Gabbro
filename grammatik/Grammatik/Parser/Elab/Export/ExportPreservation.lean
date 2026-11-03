module
public import Grammatik.Parser.Elab.UebersetzeAllg3
@[expose] public section

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- Retirement already has a source producer: preserve its name unchanged. -/
theorem retires_export (ctx : UCtx) (tabs : List UTab) (heads : List UFnKopf) (name : String) :
    uAnw1 ctx tabs heads (.retires name) = .ok (.retires name) := rfl

/-- The production statement dispatcher uses the checked retire constructor;
    exactly one held input is erased and no hardware assumption is introduced. -/
theorem retires_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (Λ : List (Res (declOf u))) (name : String) (mark : Fin u.marken.length)
    (notBorrowed : (fnAt u caller).leiht.any (strEq · name) = false)
    (resolved : markFin u.marken name = some mark) (held : Res.marke mark 0 ∈ Λ) :
    lowStmtL (l := l) u caller Γ fn Λ (.retires name) =
      .ok ⟨Λ.erase (.marke mark 0), Stmt.retires mark 0 held none⟩ := by
  exact lowRetiresL_exact u caller Γ Λ name mark notBorrowed resolved held

/-- No exported mark has a successor stage. Refuse the surface marker by name
    instead of erasing it or fabricating the premise of `Stmt.advances`. -/
theorem advances_export_refused (ctx : UCtx) (tabs : List UTab) (heads : List UFnKopf)
    (before after : String) :
    uAnw1 ctx tabs heads (.step before after) =
      .error "advances without G form: exported marks have only stage 0" := rfl

/-- The production source reader delegates labelled scopes to the exporter with
    the same recursive reader; its original outer context is retained. -/
theorem breaking_export (tabs : List UTab) (heads : List UFnKopf) (fuel : Nat)
    (ctx finalCtx : UCtx) (names : List String) (body : SAnw) (rest : List SAnw)
    (code : List UStmt)
    (exported : uBreaking (uAnwReihe tabs heads fuel) ctx names body rest = .ok (code, finalCtx)) :
    uAnwReiheCore tabs heads (fuel + 1) ctx (.waive names body :: rest) =
      .ok (code, finalCtx) := by
  exact exported

/-- Both operands retain their original predicate context; neither old/result nor a binder is
    invented by implication expansion. Failed operand exports stay failures. -/
theorem implication_export (ctx : UCtx) (p q : SExpr) (a b : UEns)
    (hp : uSichert ctx p = .ok a) (hq : uSichert ctx q = .ok b) :
    uSichert ctx (.ext .imp [] [p, q]) = .ok (.imp a b) := by
  simp only [uSichert, hp, hq]

/-- The same typed expression, including its resource context and result position, reaches G. -/
theorem implication_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (a b : UEns) (p q : Expr (declOf u) Γ Λ .bool)
    (hg : u.exportGate = .ok ())
    (hp : lowEns u Γ Λ fn er a = .ok p) (hq : lowEns u Γ Λ fn er b = .ok q) :
    lowEns u Γ Λ fn er (.imp a b) = .ok (Expr.impl p q) := by
  simp only [lowEns, hg, bind, Except.bind, hp, hq, pure, Except.pure, Expr.impl]

/-- Actual implication emission admits only a checked original-source duty set. -/
theorem implication_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option Ty) (a b : UEns) (value : Expr (declOf u) Γ Λ .bool)
    (h : lowEns u Γ Λ fn er (.imp a b) = .ok value) : u.exportGate = .ok () := by
  cases hg : u.exportGate with
  | error e => simp only [lowEns, hg, bind, Except.bind] at h; contradiction
  | ok v => cases v; rfl

/-- Evaluation and ordered read footprint coincide with canonical implication. -/
theorem implication_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (p q : Expr D Γ Λ .bool) (entry state : World D) (env : Env D Γ) :
    eval entry (Expr.impl p q) state env =
      (!wahr? (eval entry p state env) || wahr? (eval entry q state env)) ∧
    (Expr.impl p q).orte = p.orte ++ q.orte := ⟨rfl, rfl⟩

/-- Implication retains the old/result prohibition in executable bodies. -/
theorem implication_scope (a b : UEns) :
    ensAltErg (.imp a b) = (ensAltErg a || ensAltErg b) := by rfl

theorem implication_export_zeuge :
    let ctx : UCtx := {
      names := ["ready"], kinds := [.bool], types := [.bool], tabs := [], locks := [],
      held := [], res := some (0, 42), fname := "sample", alias := [], lits := [] }
    uSichert ctx (.ext .imp [] [.variable "ready", .bin "==" .res (.lit 42)]) =
      .ok (.imp (.var "ready") (.cmp "==" .erg (.lit 42))) ∧
    uBool ctx (.ext .imp [] [.variable "ready", .bin "==" .res (.lit 42)]) =
      .error "result without result" := by exact ⟨rfl, rfl⟩

/-- A successfully reified Held fact is backed by a real resource, never just its spelling. -/
theorem held_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (name : String)
    (value : Expr (declOf u) Γ Λ .bool) (h : lowHeld u Γ Λ name = .ok value) :
    u.exportGate = .ok () ∧
      ∃ lock, lockIdx u.locks name = .ok lock ∧ Res.held lock ∈ Λ ∧ value = .tru := by
  have hg : u.exportGate = .ok () := by
    cases hs : u.exportGate with
    | error e => simp only [lowHeld, hs, bind, Except.bind] at h; contradiction
    | ok v => cases v; rfl
  simp only [lowHeld, hg, bind, Except.bind] at h
  refine ⟨hg, ?_⟩
  cases hi : lockIdx u.locks name with
  | error e => simp only [hi] at h; contradiction
  | ok lock =>
    simp only [hi] at h
    split at h
    · rename_i held
      exact ⟨lock, rfl, held, (Except.ok.inj h).symm⟩
    · contradiction

/-- Under the canonical world/resource invariant, reification states an actual held fact. -/
theorem held_meaning (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (name : String)
    (value : Expr (declOf u) Γ Λ .bool) (h : lowHeld u Γ Λ name = .ok value)
    (entry state : World (declOf u)) (env : Env (declOf u) Γ) (hh : HeldIn Λ state.haelt) :
    ∃ lock, lockIdx u.locks name = .ok lock ∧ lock ∈ state.haelt ∧ eval entry value state env = true := by
  obtain ⟨_, lock, hi, possession, same⟩ := held_lower u Γ Λ name value h
  subst value
  exact ⟨lock, hi, hh lock possession, rfl⟩

def heldUnit : UProg := { tabs := [], fns := [], locks := [{name := "L", rank := 3, guard := []}] }

theorem held_lower_zeuge :
    lowHeld heldUnit [] [.held ⟨0, by decide⟩] "L" = .ok .tru ∧
    lowHeld heldUnit [] [] "L" = .error "Held predicate without possession" := by exact ⟨rfl, rfl⟩

/-- The hidden result parameter keeps the exact type and all original parameter positions. -/
theorem result_scope (u : UProg) (fn : UFn) (ty : Ty) (out : UFn)
    (h : ergAlsParam u fn (some ty) = .ok out) :
    ∃ kind, resultKind fn ty = .ok kind ∧ out.params = ("#erg", ty) :: fn.params ∧
      out.kinds = kind :: fn.kinds ∧ resultContextGate u (some ty) = .ok () := by
  unfold ergAlsParam at h
  cases hk : resultKind fn ty with
  | error e => simp only [hk, bind, Except.bind] at h; contradiction
  | ok kind =>
    simp only [hk, bind, Except.bind] at h
    cases hg : resultContextGate u (some ty) with
    | error e => simp only [hg, bind, Except.bind] at h; contradiction
    | ok v =>
      cases v
      simp only [hg, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact ⟨kind, rfl, rfl, rfl, rfl⟩

theorem result_scope_zeuge :
    let fn : UFn := {
      name := "sample", params := [("flag", .bool)], kinds := [.bool], res := none, resOpt := some (1, 2), held := [], puts := [], gives := [], body := [], ret := .opt .nichts }
    ergAlsParam heldUnit fn (some (.opt 2)) = .ok (fn.mitOpt "#erg" 1 2) ∧
    resultKind fn (.opt 3) = .error "result option count mismatch" := by
  exact ⟨rfl, rfl⟩

/-- The actual Endblock dispatcher passes both scopes and all callee checks to the existing
    constructor. The error body is parsed from the real source tail, with its own reason binder. -/
theorem nested_else_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (fuel : Nat) (Λ : List (Res (declOf u))) (top : AtTop u caller Λ)
    (y callee reason : String) (args : List UArg) (source tail remaining : List UStmt)
    (k : RufKopf u caller Γ Λ) (τ : Ty)
    (hg : u.exportGate = .ok ())
    (hk : lowRufKopf u caller Γ fn Λ callee args = .ok k)
    (hr : 0 < (declOf u).gruende k.callee) (he : (declOf u).erg k.callee = some τ)
    (err : Endblock (declOf u) (verOf u caller) l (Ty.why ((declOf u).gruende k.callee) :: Γ) (nach (declOf u) k.callee Λ))
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) (nach (declOf u) k.callee Λ))
    (herr : lowEndL (l := l) u caller (Ty.why ((declOf u).gruende k.callee) :: Γ)
      (fn.mitWhy reason 0 ((declOf u).gruende k.callee)) fuel (nach (declOf u) k.callee Λ) top source = .ok (err, .blkEnd :: tail))
    (hbody : lowEndL (l := l) u caller (τ :: Γ) (fn.mitTy y τ) fuel (nach (declOf u) k.callee Λ) top tail = .ok (body, remaining)) :
    lowEndL (l := l) u caller Γ fn (fuel + 1) Λ top (.bindElse y callee args reason :: source) =
      .ok (nestedElse u caller Γ Λ k τ he hr err body, remaining) := by
  simp only [lowEndL_succ, lowEndStep, lowStufe_ende, hg, bind, Except.bind, hk, hr, ↓reduceIte, withErg, herr]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [hbody, bind, Except.bind]

/-- Successful dispatch through the new Endblock case has consumed the unit's source duty gate. -/
theorem nested_else_gate {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (fn : UFn) (n : Nat) (Λ : List (Res (declOf u))) (top : AtTop u caller Λ)
    (y callee reason : String) (args : List UArg) (source : List UStmt)
    (output : Endblock (declOf u) (verOf u caller) l Γ Λ × List UStmt)
    (h : lowEndL (l := l) u caller Γ fn (n + 1) Λ top
      (.bindElse y callee args reason :: source) = .ok output) : u.exportGate = .ok () := by
  cases hg : u.exportGate with
  | error e => simp only [lowEndL_succ, lowEndStep, hg, bind, Except.bind] at h; contradiction
  | ok v => cases v; rfl

/-- Canonical call semantics retained by the exported nested continuation. Both paths use
    the post-call world, and the callee is evaluated exactly once at the original argument footprint. -/
theorem nested_else_meaning {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (callee : D.Fn) (args : Args D Γ Λ (D.params callee)) (τ : Ty)
    (he : D.erg callee = some τ) (hp : RufPasst D V (D.signatur callee) Λ)
    (hr : 0 < D.gruende callee)
    (err : Endblock D V l (Ty.why (D.gruende callee) :: Γ) (nach D callee Λ))
    (body : Endblock D V l (τ :: Γ) (nach D callee Λ)) (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (state : World D) (env : Env D Γ) :
    execEnd O passes R (.bindCallElse callee args he hp hr err body) state env =
      (let readState := state.lese Λ args.orte
       match R callee readState (evalArgs readState args readState env) with
       | .ok next value => (execEnd O passes R body next (.cons (ergWert he value) env)).schrumpf
       | .why next reason => (execEnd O passes R err next (.cons reason env)).schrumpf
       | .logik error => .logik error
       | .hardware error => .hardware error) := by rfl

/-- Cleanup evidence names exactly the lexical scopes and retains the whole contract end. -/
theorem scoped_return_resources (u : UProg) (caller : Fin u.fns.length)
    (Λ : List (Res (declOf u))) (scopes : AtTop u caller Λ)
    (resources : RueckRessourcen (declOf u) (verOf u caller) Λ)
    (h : lowReturnResources u caller Λ scopes = .ok resources) :
    resources.scopes = scopes ∧ Λ.Perm ((verOf u caller).ende ++ scopes.map Res.held) := by
  unfold lowReturnResources at h
  split at h
  · cases h
    exact ⟨rfl, of_decide_eq_true (by assumption)⟩
  · contradiction

/-- Both return dispatchers preserve the payload, residual resources and lexical cleanup. -/
theorem scoped_return_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (lock : (declOf u).Lock) (scopes : List (declOf u).Lock) (r : URet)
    (notReason : ∀ i, r ≠ .why i)
    (resources : RueckRessourcen (declOf u) (verOf u caller) Λ)
    (erg : ErgExpr (declOf u) Γ Λ (verOf u caller).erg)
    (hr : lowReturnResources u caller Λ (lock :: scopes) = .ok resources)
    (he : lowErg u caller Γ Λ fn r = .ok erg) :
    lowRetStmt (l := l) u caller Γ fn Λ (lock :: scopes) r = .ok (.retScoped erg resources) ∧
    lowRetEnd (l := l) u caller Γ fn Λ (lock :: scopes) r = .ok (.retScoped erg resources) := by
  cases r <;> simp_all [lowRetStmt, lowRetEnd, Except.map, bind, Except.bind]

/-- Reason returns retain their original channel bound and the same cleanup evidence. -/
theorem scoped_reason_return_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (lock : (declOf u).Lock) (scopes : List (declOf u).Lock)
    (i : Nat) (hi : i < (verOf u caller).gruende)
    (resources : RueckRessourcen (declOf u) (verOf u caller) Λ)
    (hr : lowReturnResources u caller Λ (lock :: scopes) = .ok resources) :
    lowRetStmt (l := l) u caller Γ fn Λ (lock :: scopes) (.why i) = .ok (.retWhyScoped ⟨i, hi⟩ resources) ∧
    lowRetEnd (l := l) u caller Γ fn Λ (lock :: scopes) (.why i) = .ok (.retWhyScoped ⟨i, hi⟩ resources) := by
  simp [lowRetStmt, lowRetEnd, hr, hi, bind, Except.bind]

/-- The indirect discard form keeps the pointer, checked arguments, result type,
    caller conformance and error scope from the binding sibling. -/
theorem call_ind_else_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (name reason : String) (args : List UArg)
    (source tail : List UStmt) (n : Nat) (pointer : Var Γ (.fnptr n))
    (k : RufKopfN u caller Γ Λ n) (τ : Ty)
    (hp : lowZeigerN u Γ fn name = .ok ⟨n, pointer⟩)
    (hk : lowRufKopfN u caller Γ fn Λ n args = .ok k)
    (hr : 0 < ((declOf u).sigNr n).gruende) (he : ((declOf u).sigNr n).erg = some τ)
    (handler : Endblock (declOf u) (verOf u caller) l
      (.why (((declOf u).sigNr n).gruende) :: Γ) (nachSig (declOf u) ((declOf u).sigNr n) Λ))
    (herr : R.ende (l := l) (.why (((declOf u).sigNr n).gruende) :: Γ)
      (fn.mitWhy reason 0 (((declOf u).sigNr n).gruende))
      (nachSig (declOf u) ((declOf u).sigNr n) Λ) top source = .ok (handler, .blkEnd :: tail)) :
    lowCallIndElse (l := l) u caller R Γ fn Λ top name args reason source =
      .ok (⟨_, .callIndElse (.var pointer) k.args he k.hp hr handler⟩, tail) := by
  simp only [lowCallIndElse, hp, hk, bind, Except.bind, hr, ↓reduceIte, withErgN]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [herr]

/-- The shared flat marker reaches the indirect producer in the real structural dispatcher. -/
theorem call_ind_else_dispatch {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (name reason : String) (args : List UArg)
    (source : List UStmt) (n : Nat)
    (resolved : (fn.params.find? (fun binding => strEq binding.1 name)).map (·.2) = some (.fnptr n)) :
    lowStructStep (l := l) u caller R Γ fn Λ top (.axCallElseBeg name args reason) source =
      lowCallIndElse u caller R Γ fn Λ top name args reason source := by
  simp only [lowStructStep, lowCallElse, resolved]

/-- The continuing foreign binder retains every write/guard premise from its
    checked head; only the success branch receives the answer binding. -/
theorem foreign_else_seq_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ Λ' : List (Res (declOf u)))
    (top : AtTop u caller Λ) (y name reason : String) (args : List UArg)
    (source tail remaining : List UStmt) (k : AxKopf u caller Γ Λ) (τ : Ty)
    (hk : lowAxKopf u caller Γ fn Λ name args = .ok k)
    (hr : 0 < (declOf u).agruende k.ax) (he : (declOf u).aerg k.ax = some τ)
    (handler : Endblock (declOf u) (verOf u caller) l (.why ((declOf u).agruende k.ax) :: Γ) Λ)
    (body : Block (declOf u) (verOf u caller) l (τ :: Γ) Λ Λ')
    (herr : R.ende (l := l) (.why ((declOf u).agruende k.ax) :: Γ)
      (fn.mitWhy reason 0 ((declOf u).agruende k.ax)) Λ top source = .ok (handler, .blkEnd :: tail))
    (hbody : R.seq (l := l) (τ :: Γ) (fn.mitTy y τ) Λ top tail = .ok (⟨Λ', body⟩, remaining)) :
    lowSeqStep (l := l) u caller R Γ fn Λ top (.bindAxElse y name args reason :: source) =
      .ok (⟨Λ', .bindAxiomElse k.ax k.args he hr k.hw k.hg k.hd k.hgd handler body⟩, remaining) := by
  simp only [lowSeqStep, hk, bind, Except.bind, hr, ↓reduceIte, withAxErg]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [herr, hbody, bind, Except.bind]

/-- Explicit ending branches use the same typed foreign binder as function bodies. -/
theorem foreign_bind_end_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (y name : String) (args : List UArg)
    (source remaining : List UStmt) (k : AxKopf u caller Γ Λ) (τ : Ty)
    (hk : lowAxKopf u caller Γ fn Λ name args = .ok k) (he : (declOf u).aerg k.ax = some τ)
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) Λ)
    (hbody : R.ende (l := l) (τ :: Γ) (fn.mitTy y τ) Λ top source = .ok (body, remaining)) :
    lowEndStep (l := l) u caller R Γ fn Λ top (.bindAx y name args :: source) =
      .ok (.bindAxiom k.ax k.args he k.hw k.hg k.hd k.hgd body, remaining) := by
  simp only [lowEndStep, hk, bind, Except.bind, withAxErg]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [hbody, bind, Except.bind]

/-- Nested foreign `let else` consumes its actual handler, closer and success
    tail; no source segment is replaced with an empty branch. -/
theorem foreign_else_end_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (y name reason : String) (args : List UArg)
    (source tail remaining : List UStmt) (k : AxKopf u caller Γ Λ) (τ : Ty)
    (hk : lowAxKopf u caller Γ fn Λ name args = .ok k)
    (hr : 0 < (declOf u).agruende k.ax) (he : (declOf u).aerg k.ax = some τ)
    (handler : Endblock (declOf u) (verOf u caller) l (.why ((declOf u).agruende k.ax) :: Γ) Λ)
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) Λ)
    (herr : R.ende (l := l) (.why ((declOf u).agruende k.ax) :: Γ)
      (fn.mitWhy reason 0 ((declOf u).agruende k.ax)) Λ top source = .ok (handler, .blkEnd :: tail))
    (hbody : R.ende (l := l) (τ :: Γ) (fn.mitTy y τ) Λ top tail = .ok (body, remaining)) :
    lowEndStep (l := l) u caller R Γ fn Λ top (.bindAxElse y name args reason :: source) =
      .ok (.bindAxiomElse k.ax k.args he hr k.hw k.hg k.hd k.hgd handler body, remaining) := by
  simp only [lowEndStep, hk, hr, ↓reduceIte, withAxErg]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [herr, hbody, bind, Except.bind]

/-- A discarded foreign value uses the same binder premises, with an inaccessible
    synthetic name; the following source locals retain their positions. -/
theorem foreign_discard_end_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (name : String) (args : List UArg)
    (source remaining : List UStmt) (k : AxKopf u caller Γ Λ) (τ : Ty)
    (hk : lowAxKopf u caller Γ fn Λ name args = .ok k) (he : (declOf u).aerg k.ax = some τ)
    (body : Endblock (declOf u) (verOf u caller) l (τ :: Γ) Λ)
    (hbody : R.ende (l := l) (τ :: Γ) (fn.mitTy "#ax" τ) Λ top source = .ok (body, remaining)) :
    lowEndStep (l := l) u caller R Γ fn Λ top (.axCall name args :: source) =
      .ok (.bindAxiom k.ax k.args he k.hw k.hg k.hd k.hgd body, remaining) := by
  simp only [lowEndStep, hk, bind, Except.bind, withAxErg]
  split
  · rename_i hn
    rw [he] at hn
    contradiction
  · rename_i τ' ht
    have same : τ' = τ := Option.some.inj (ht.symm.trans he)
    subst τ'
    simp only [hbody, bind, Except.bind]

/-- A void foreign call keeps the original context and all checked call premises. -/
theorem foreign_void_end_lower {l : Bool} (u : UProg) (caller : Fin u.fns.length)
    (R : LowStufe u caller) (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (top : AtTop u caller Λ) (name : String) (args : List UArg)
    (source remaining : List UStmt) (k : AxKopf u caller Γ Λ)
    (hk : lowAxKopf u caller Γ fn Λ name args = .ok k) (he : (declOf u).aerg k.ax = none)
    (body : Endblock (declOf u) (verOf u caller) l Γ Λ)
    (hbody : R.ende (l := l) Γ fn Λ top source = .ok (body, remaining)) :
    lowEndStep (l := l) u caller R Γ fn Λ top (.axCall name args :: source) =
      .ok (.cons (axiomStmt u caller Γ Λ k he) body, remaining) := by
  simp only [lowEndStep, hk, bind, Except.bind, withAxErg, he, hbody]

end Gabbro.Grammatik.Parser.ExportPreservation
