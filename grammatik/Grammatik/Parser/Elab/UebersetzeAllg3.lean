/-
  File:      Grammatik/Parser/Elab/UebersetzeAllg3.lean
  Subject:   T3 PART 7: generic lowering, third part: statement runs (`lowSeqL`: `let`, `locks`, `if`,
             `traverse`, early `return`), bodies, `lowerAllg`, and the 104/108 pins and the chain.
             Split from `UebersetzeAllg2` (which keeps the single statements and calls); same namespace.
-/
import Grammatik.Parser.Elab.UebersetzeAllg2

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-! ## Returns -/

/-- The held resources are the contract end, as a `Perm`. -/
theorem endPerm_ok (u : UProg) (caller : Fin u.fns.length) :
    (resOf u caller).Perm (verOf u caller).ende := by
  show ((heldAt u (fnAt u caller)).map
    (Res.held (D := declOf u))).Perm (verOf u caller).ende
  rw [show (verOf u caller).ende =
    (vertragVon (declOf u) caller).ende from rfl, ende_eq u caller]

/-- The value of a return, at the function's held resources `resOf`. -/
def lowErg (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) : URet →
    Except String (ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg)
  | .empty =>
    match hE : (fnAt u caller).ergTy with
    | none =>
      have hV : (verOf u caller).erg = none := by
        show (vertragVon (declOf u) caller).erg = none
        rw [vErg_eq u caller, hE]
      have eK : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
        rw [hV]
        exact ErgExpr.empty
      .ok eK
    | some _ => .error "return without value with result"
  | .val s =>
    match hE : (fnAt u caller).ergTy with
    | some (.int lo hi) =>
      match lowWertAt u Γ (resOf u caller) fn lo hi s with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          show ErgExpr (declOf u) Γ (resOf u caller) (Option.some (.int lo hi))
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "number returned for a non-number result"
    | none => .error "return with value without result"
  | .bool b =>
    match hE : (fnAt u caller).ergTy with
    | some .bool =>
      match lowEns u Γ (resOf u caller) fn none b with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "truth value returned for a non-bool result"
    | none => .error "return with value without result"

/-- The trailing return. -/
def lowEnd (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (r : URet) :
    Except String (Endblock (declOf u) (verOf u caller) false Γ (resOf u caller)) :=
  match lowErg u caller Γ fn r with
  | .error e => .error e
  | .ok e => .ok (Endblock.ret e (endPerm_ok u caller))

/-- `Λ` is exactly the function's held resources (not inside a `locks` block): where a `return` may
    stand (`Stmt.ret` needs `Λ` to be the contract end). -/
abbrev AtTop (u : UProg) (caller : Fin u.fns.length) (Λ : List (Res (declOf u))) : Type :=
  Option (PLift (Λ = resOf u caller))

/-- A `return` inside a block, at the top held list only. -/
def lowRetStmt {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (r : URet) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match pe with
  | none => .error "lower: return under locks has no G form"
  | some ⟨h⟩ =>
    match lowErg u caller Γ fn r with
    | .error e => .error e
    | .ok erg =>
      .ok (by subst h; exact Stmt.ret erg (endPerm_ok u caller))

/-- The rank rule of `locks L`: every held lock ranks below `L` (`H006`), as a Bool. -/
def rangOkB (u : UProg) (Λ : List (Res (declOf u))) (L : (declOf u).Lock) : Bool :=
  (heldLocksD u Λ).all fun M => decide ((declOf u).rang M < (declOf u).rang L)

theorem rangOkB_sound (u : UProg) (Λ : List (Res (declOf u))) (L : (declOf u).Lock)
    (h : rangOkB u Λ L = true) :
    ∀ M, Res.held (D := declOf u) M ∈ Λ → (declOf u).rang M < (declOf u).rang L := by
  intro M hM
  have hm := heldLocksD_mem u Λ M hM
  unfold rangOkB at h
  have := List.all_eq_true.mp h M hm
  exact of_decide_eq_true this

/-- The result type of a callee, for a binding (`he` of `Block.bindCall`); a callee without a value binds nothing. -/
def withErg {α : Type} (u : UProg) (callee : Fin u.fns.length)
    (K : (τ : Ty) → (declOf u).erg callee = some τ → Except String α) : Except String α :=
  match hE : (declOf u).erg callee with
  | none => .error "call without a value"
  | some τ => K τ hE

/-! ## Runs of statements -/

mutual
/-- A flat run of statements at `Λ`, up to (not including) the `zu`/`sonst` marker that ends it, or the
    end of the list; returns the block and what is left. A `let` binds for the rest of the run: its
    type is the COMPUTED range of the value (as the exporter pushes it) and the scope grows by it.
    Structural in the fuel. -/
def lowSeqL {l : Bool} (u : UProg) (caller : Fin u.fns.length) :
    (Γ : Ctx) → UFn → Nat → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String (Block (declOf u) (verOf u caller) l Γ Λ Λ × List UStmt)
  | _, _, 0, _, _, _ => .error "lower: blocks nested too deep"
  | _, _, _ + 1, _, _, [] => .ok (Block.nil, [])
  | _, _, _ + 1, _, _, .blkEnd :: rest => .ok (Block.nil, .blkEnd :: rest)
  | _, _, _ + 1, _, _, .ifElse :: rest => .ok (Block.nil, .ifElse :: rest)
  | Γ, fn, n + 1, Λ, pe, .lockBeg g :: rest =>
    match lowStructL u caller Γ fn n Λ pe (.lockBeg g) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowSeqL u caller Γ fn n Λ pe rest' with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, .ifBeg c :: rest =>
    match lowStructL u caller Γ fn n Λ pe (.ifBeg c) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowSeqL u caller Γ fn n Λ pe rest' with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, .loopBeg bnd tab inv :: rest =>
    match lowStructL u caller Γ fn n Λ pe (.loopBeg bnd tab inv) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowSeqL u caller Γ fn n Λ pe rest' with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, .bind x d v :: rest =>
    match lowBindWert u Γ Λ fn d v with
    | .error e => .error e
    | .ok s =>
      match lowSeqL u caller (.int s.range.1 s.range.2 :: Γ) (fn.mitBindung x s.range) n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.bind s.term b, r)
  | Γ, fn, n + 1, Λ, pe, .bindB x v :: rest =>
    match lowEns u Γ Λ fn none v with
    | .error e => .error e
    | .ok ev =>
      match lowSeqL u caller (.bool :: Γ) (fn.mitBindungB x) n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.bind ev b, r)
  | Γ, fn, n + 1, Λ, pe, .bindMut x lo hi v :: rest =>
    match lowWertAt u Γ Λ fn lo hi v with
    | .error e => .error e
    | .ok ev =>
      match lowSeqL u caller (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.bind ev b, r)
  | Γ, fn, n + 1, Λ, pe, .bindCall x cname args :: rest =>
    match lowRufKopf u caller Γ fn Λ cname args with
    | .error e => .error e
    | .ok k =>
      withErg u k.callee fun τ hE =>
        match lowSeqL (l := l) u caller (τ :: Γ) (fn.mitTy x τ) n Λ pe rest with
        | .error e => .error e
        | .ok (b, r) =>
          have hr : (declOf u).gruende k.callee = 0 := sigGruende_zero u k.callee
          have b' : Block (declOf u) (verOf u caller) l (τ :: Γ) (nach (declOf u) k.callee Λ) Λ := by
            rw [nach_eq u k.callee Λ]
            exact b
          .ok (Block.bindCall (D := declOf u) k.callee k.args hE k.hp hr b', r)
  | Γ, fn, n + 1, Λ, pe, .axCall c args :: rest =>
    match lowAxKopf u caller Γ fn Λ c args with
    | .error e => .error e
    | .ok k =>
      withAxErg u k.ax
        (fun h =>
          match lowSeqL (l := l) u caller Γ fn n Λ pe rest with
          | .error e => .error e
          | .ok (b, r) => .ok (Block.cons (axiomStmt u caller Γ Λ k h) b, r))
        (fun τ hE =>
          match lowSeqL (l := l) u caller (τ :: Γ) (fn.mitTy "#ax" τ) n Λ pe rest with
          | .error e => .error e
          | .ok (b, r) =>
            .ok (Block.bindAxiom (D := declOf u) k.ax k.args hE
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide))
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide)) b, r))
  | Γ, fn, n + 1, Λ, pe, .bindAx x c args :: rest =>
    match lowAxKopf u caller Γ fn Λ c args with
    | .error e => .error e
    | .ok k =>
      withAxErg u k.ax (fun _ => .error "call without a value")
        (fun τ hE =>
          match lowSeqL (l := l) u caller (τ :: Γ) (fn.mitTy x τ) n Λ pe rest with
          | .error e => .error e
          | .ok (b, r) =>
            .ok (Block.bindAxiom (D := declOf u) k.ax k.args hE
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide))
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide)) b, r))
  | Γ, fn, n + 1, Λ, pe, .narrowBeg x lo hi :: rest =>
    match paramPos fn.params x with
    | .error e => .error e
    | .ok j =>
      match fn.params[j]? with
      | some (_, .int l1 h1) =>
        match lowVar Γ j (.int l1 h1) with
        | .error e => .error e
        | .ok v =>
          match lowEndL (l := l) u caller Γ fn n Λ pe rest with
          | .error e => .error e
          | .ok (sonst, .blkEnd :: rest') =>
            match lowSeqL (l := l) u caller (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ pe rest' with
            | .error e => .error e
            | .ok (b, r) => .ok (Block.narrow (D := declOf u) (Expr.var v) lo hi sonst b, r)
          | .ok (_, _) => .error "lower: a narrow is not closed"
      | _ => .error "lower: narrow of a non-number"
  | Γ, fn, n + 1, Λ, pe, .ret v :: rest =>
    match lowRetStmt u caller Γ fn Λ pe v with
    | .error e => .error e
    | .ok st =>
      match lowSeqL u caller Γ fn n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, .leave _ :: rest =>
    if h : l = true then
      match lowSeqL u caller Γ fn n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons (Stmt.leave h) b, r)
    else .error "lower: leave outside a traverse"
  | Γ, fn, n + 1, Λ, pe, .next _ :: rest =>
    if h : l = true then
      match lowSeqL u caller Γ fn n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons (Stmt.next h) b, r)
    else .error "lower: next outside a traverse"
  | Γ, fn, n + 1, Λ, pe, s :: rest =>
    match lowStmtL u caller Γ fn Λ s with
    | .error e => .error e
    | .ok st =>
      match lowSeqL u caller Γ fn n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Block.cons st b, r)

/-- The structured statements, each with the rest of the run after its body: `locks g { … }` (the lock
    by name, the rank rule; no `return` inside), `if c { … } else { … }` and `traverse` (its body is a
    block with `l = true`, the binder an index into the table, the invariant read in the OUTER scope). -/
def lowStructL {l : Bool} (u : UProg) (caller : Fin u.fns.length) :
    (Γ : Ctx) → UFn → Nat → (Λ : List (Res (declOf u))) → AtTop u caller Λ → UStmt → List UStmt →
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ × List UStmt)
  | _, _, 0, _, _, _, _ => .error "lower: blocks nested too deep"
  | Γ, fn, n + 1, Λ, _, .lockBeg g, rest =>
    match lockIdx u.locks g with
    | .error e => .error e
    | .ok L =>
      if hr : rangOkB u Λ L = true then
        match lowSeqL u caller Γ fn n (Res.held L :: Λ) none rest with
        | .error e => .error e
        | .ok (body, .blkEnd :: rest') =>
          .ok (Stmt.locks L (rangOkB_sound u Λ L hr) body, rest')
        | .ok (_, _) => .error "lower: a locks block is not closed"
      else .error "lower: locks against a held lock of higher or equal rank"
  | Γ, fn, n + 1, Λ, pe, .ifBeg c, rest =>
    match lowEns u Γ Λ fn none c with
    | .error e => .error e
    | .ok cv =>
      match lowSeqL u caller Γ fn n Λ pe rest with
      | .error e => .error e
      | .ok (tb, .ifElse :: rest1) =>
        match lowSeqL u caller Γ fn n Λ pe rest1 with
        | .error e => .error e
        | .ok (eb, .blkEnd :: rest2) => .ok (Stmt.ite cv tb eb, rest2)
        | .ok (_, _) => .error "lower: an if is not closed"
      | .ok (_, _) => .error "lower: an if has no else part"
  | Γ, fn, n + 1, Λ, pe, .loopBeg bnd tab inv, rest =>
    match tabIdx u.tabs tab with
    | .error e => .error e
    | .ok t =>
      match lowEns u Γ Λ fn none inv with
      | .error e => .error e
      | .ok iv =>
        match lowSeqL (l := true) u caller (Ty.index ((declOf u).count t) :: Γ)
            (fn.mitIndex bnd t.val ((declOf u).count t)) n Λ pe rest with
        | .error e => .error e
        | .ok (body, .blkEnd :: rest') => .ok (Stmt.traverse t iv body, rest')
        | .ok (_, _) => .error "lower: a traverse is not closed"
  | _, _, _ + 1, _, _, _, _ => .error "lower: not a structured statement"

/-- The `else` branch of a narrowing as an end block: its statements and the ender (`return`, `leave`, `next`),
    which must not fall through; the marker `blkEnd` that closes the branch is left to the caller. -/
def lowEndL {l : Bool} (u : UProg) (caller : Fin u.fns.length) :
    (Γ : Ctx) → UFn → Nat → (Λ : List (Res (declOf u))) → AtTop u caller Λ → List UStmt →
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ × List UStmt)
  | _, _, 0, _, _, _ => .error "lower: blocks nested too deep"
  | _, _, _ + 1, _, _, [] => .error "lower: an else branch falls through"
  | _, _, _ + 1, _, _, .blkEnd :: _ => .error "lower: an else branch falls through"
  | _, _, _ + 1, _, _, .ifElse :: _ => .error "lower: an else branch falls through"
  | Γ, fn, _ + 1, Λ, pe, .ret v :: rest =>
    match pe with
    | none => .error "lower: return under locks has no G form"
    | some ⟨h⟩ =>
      match lowErg u caller Γ fn v with
      | .error e => .error e
      | .ok erg => .ok (by subst h; exact Endblock.ret erg (endPerm_ok u caller), rest)
  | _, _, _ + 1, _, _, .leave _ :: rest =>
    if h : l = true then .ok (Endblock.leave h, rest) else .error "lower: leave outside a traverse"
  | _, _, _ + 1, _, _, .next _ :: rest =>
    if h : l = true then .ok (Endblock.next h, rest) else .error "lower: next outside a traverse"
  | Γ, fn, n + 1, Λ, pe, .bind x d v :: rest =>
    match lowBindWert u Γ Λ fn d v with
    | .error e => .error e
    | .ok s =>
      match lowEndL (l := l) u caller (.int s.range.1 s.range.2 :: Γ) (fn.mitBindung x s.range) n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.bind s.term b, r)
  | Γ, fn, n + 1, Λ, pe, .bindB x v :: rest =>
    match lowEns u Γ Λ fn none v with
    | .error e => .error e
    | .ok ev =>
      match lowEndL (l := l) u caller (.bool :: Γ) (fn.mitBindungB x) n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.bind ev b, r)
  | Γ, fn, n + 1, Λ, pe, .bindMut x lo hi v :: rest =>
    match lowWertAt u Γ Λ fn lo hi v with
    | .error e => .error e
    | .ok ev =>
      match lowEndL (l := l) u caller (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.bind ev b, r)
  | _, _, _ + 1, _, _, .bindCall .. :: _ =>
    .error "lower: a value call in an else branch has no G form (Endblock lacks bindCall)"
  | _, _, _ + 1, _, _, .axCall .. :: _ =>
    .error "lower: a foreign call in an else branch has no G form here"
  | _, _, _ + 1, _, _, .bindAx .. :: _ =>
    .error "lower: a foreign call in an else branch has no G form here"
  | _, _, _ + 1, _, _, .narrowBeg .. :: _ =>
    .error "lower: a narrow in an else branch has no G form (Endblock lacks narrow)"
  | Γ, fn, n + 1, Λ, pe, .lockBeg g :: rest =>
    match lowStructL (l := l) u caller Γ fn n Λ pe (.lockBeg g) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowEndL (l := l) u caller Γ fn n Λ pe rest' with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, .ifBeg c :: rest =>
    match lowStructL (l := l) u caller Γ fn n Λ pe (.ifBeg c) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowEndL (l := l) u caller Γ fn n Λ pe rest' with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, .loopBeg bnd tab inv :: rest =>
    match lowStructL (l := l) u caller Γ fn n Λ pe (.loopBeg bnd tab inv) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowEndL (l := l) u caller Γ fn n Λ pe rest' with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.cons st b, r)
  | Γ, fn, n + 1, Λ, pe, s :: rest =>
    match lowStmtL u caller Γ fn Λ s with
    | .error e => .error e
    | .ok st =>
      match lowEndL (l := l) u caller Γ fn n Λ pe rest with
      | .error e => .error e
      | .ok (b, r) => .ok (Endblock.cons st b, r)
end

/-! ## Bodies and program assembly -/

/-- The fuel of a nested block (statements and nesting depth together). -/
def blockFuel : Nat := 100000

/-- The body reader, structural in a fuel: straight-line writes, direct calls, `locks`, `if` and
    `traverse` and `let` bindings (the scope `Γ`/`fn` grows by each), then the trailing return. -/
def lowBodyF (u : UProg) (caller : Fin u.fns.length) :
    (Γ : Ctx) → UFn → Nat → List UStmt → URet →
    Except String (Endblock (declOf u) (verOf u caller) false Γ (resOf u caller))
  | _, _, 0, _, _ => .error "lower: body too long"
  | Γ, fn, _ + 1, [], r => lowEnd u caller Γ fn r
  | Γ, fn, n + 1, .bind x d v :: rest, r =>
    match lowBindWert u Γ (resOf u caller) fn d v with
    | .error e => .error e
    | .ok s =>
      match lowBodyF u caller (.int s.range.1 s.range.2 :: Γ) (fn.mitBindung x s.range) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind s.term e)
  | Γ, fn, n + 1, .axCall c args :: rest, r =>
    match lowAxKopf u caller Γ fn (resOf u caller) c args with
    | .error e => .error e
    | .ok k =>
      withAxErg u k.ax
        (fun h =>
          match lowBodyF u caller Γ fn n rest r with
          | .error e => .error e
          | .ok e => .ok (Endblock.cons (axiomStmt u caller Γ (resOf u caller) k h) e))
        (fun τ hE =>
          match lowBodyF u caller (τ :: Γ) (fn.mitTy "#ax" τ) n rest r with
          | .error e => .error e
          | .ok e =>
            .ok (Endblock.bindAxiom (D := declOf u) k.ax k.args hE
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide))
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide)) e))
  | Γ, fn, n + 1, .bindAx x c args :: rest, r =>
    match lowAxKopf u caller Γ fn (resOf u caller) c args with
    | .error e => .error e
    | .ok k =>
      withAxErg u k.ax (fun _ => .error "call without a value")
        (fun τ hE =>
          match lowBodyF u caller (τ :: Γ) (fn.mitTy x τ) n rest r with
          | .error e => .error e
          | .ok e =>
            .ok (Endblock.bindAxiom (D := declOf u) k.ax k.args hE
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide))
              (fun t ht => by rw [ax_schreibt_nie u k.ax t] at ht; exact absurd ht (by decide))
              (fun g hg => by rw [ax_gschreibt_nie u k.ax g] at hg; exact absurd hg (by decide)) e))
  | _, _, _ + 1, .bindCall .. :: _, _ =>
    .error "lower: a value call at the top level of a body has no G form (Endblock lacks bindCall)"
  | _, _, _ + 1, .narrowBeg .. :: _, _ =>
    .error "lower: a narrow at the top level of a body has no G form (Endblock lacks narrow)"
  | Γ, fn, n + 1, .bindB x v :: rest, r =>
    match lowEns u Γ (resOf u caller) fn none v with
    | .error e => .error e
    | .ok ev =>
      match lowBodyF u caller (.bool :: Γ) (fn.mitBindungB x) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind ev e)
  | Γ, fn, n + 1, .bindMut x lo hi v :: rest, r =>
    match lowWertAt u Γ (resOf u caller) fn lo hi v with
    | .error e => .error e
    | .ok ev =>
      match lowBodyF u caller (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.bind ev e)
  | Γ, fn, n + 1, (.lockBeg g) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.lockBeg g) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.ifBeg c) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.ifBeg c) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, (.loopBeg b t i) :: rest, r =>
    match lowStructL (l := false) u caller Γ fn blockFuel (resOf u caller) (some ⟨rfl⟩) (.loopBeg b t i) rest with
    | .error e => .error e
    | .ok (st, rest') =>
      match lowBodyF u caller Γ fn n rest' r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)
  | Γ, fn, n + 1, s :: rest, r =>
    match lowStmtL u caller Γ fn (resOf u caller) s with
    | .error e => .error e
    | .ok st =>
      match lowBodyF u caller Γ fn n rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)

/-- The body: the statements of a function, then the trailing return, in the scope of its parameters. -/
def lowBody (u : UProg) (caller : Fin u.fns.length)
    (ss : List UStmt) (r : URet) :
    Except String (Endblock (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller)) :=
  lowBodyF u caller (ctxOf u caller) (fnAt u caller) (ss.length + 1) ss r

/-- The ensures type of a lowered function. -/
abbrev EnsTy (u : UProg) (f : Fin u.fns.length) :=
  Expr (declOf u) (ErgCtx ((declOf u).params f) ((declOf u).erg f))
    (vertragVon (declOf u) f).ende .bool

/-- The body type of a lowered function. -/
abbrev RumpTy (u : UProg) (f : Fin u.fns.length) :=
  Endblock (declOf u) (vertragVon (declOf u) f) false
    ((declOf u).params f)
    (Signatur.anfang (declOf u) ((declOf u).signatur f))

/-- One whole function: contracts and body through the
    declaration. -/
def lowerFnAt (u : UProg) (c : Fin u.fns.length) :
    Except String (EnsTy u c × RumpTy u c) :=
  match lowEnsList u (ErgCtx (ctxOf u c) ((verOf u c).erg))
      (resOf u c) (fnAt u c) (fnAt u c).res
      (fnAt u c).gives with
  | .error e => .error e
  | .ok e0 =>
    match lowBody u c (fnAt u c).body (fnAt u c).ret with
    | .error e => .error e
    | .ok b0 =>
      have e1 : EnsTy u c := by
        show Expr (declOf u)
          (ErgCtx ((declOf u).params c) ((declOf u).erg c))
          (vertragVon (declOf u) c).ende .bool
        rw [← ensCtx_eq u c, ← endeRes_eq u c]
        exact e0
      have b1 : RumpTy u c := by
        show Endblock (declOf u) (vertragVon (declOf u) c) false
          ((declOf u).params c)
          (Signatur.anfang (declOf u) ((declOf u).signatur c))
        rw [← ctxParams_eq u c, ← anfangRes_eq u c]
        exact b0
      .ok (e1, b1)

/-- Every function lowers (the success check of `lowerAllg`;
    the values ride `lowerFnAt` directly). -/
def lowerEach (u : UProg) :
    List (Fin u.fns.length) → Except String Unit
  | [] => .ok ()
  | f :: fs =>
    match lowerFnAt u f with
    | .error e => .error e
    | .ok _ => lowerEach u fs

/-- What `lowerEach` checks, per function. -/
theorem lowerEach_all_ok (u : UProg) (fs : List (Fin u.fns.length))
    (f : Fin u.fns.length) (hm : f ∈ fs)
    (h : lowerEach u fs = .ok ()) :
    ∃ v, lowerFnAt u f = .ok v := by
  induction fs with
  | nil =>
    simp at hm
  | cons g gs ih =>
    simp only [List.mem_cons] at hm
    cases hg : lowerFnAt u g with
    | error e =>
      have hE : lowerEach u (g :: gs) = .error e := by
        simp [lowerEach, hg]
      rw [hE] at h
      simp at h
    | ok v =>
      have hO : lowerEach u (g :: gs) = lowerEach u gs := by
        simp [lowerEach, hg]
      cases hm with
      | inl he =>
        subst he
        exact ⟨v, hg⟩
      | inr hm' =>
        rw [hO] at h
        exact ih hm' h

/-- The lowered pair at an index known good. -/
def lowerAtPair (u : UProg) (f : Fin u.fns.length)
    (h : ∃ v, lowerFnAt u f = .ok v) :
    EnsTy u f × RumpTy u f :=
  match hm : lowerFnAt u f with
  | .ok v => v
  | .error e => by
    exfalso
    obtain ⟨v, hv⟩ := h
    rw [hv] at hm
    simp at hm

/-- Assemble lowered functions to a program (no contract
    content in `requires`, per-function `ensures` and bodies). -/
def progOfFn (u : UProg) (E : ∀ f : Fin u.fns.length, EnsTy u f)
    (B : ∀ f : Fin u.fns.length, RumpTy u f) :
    Programm (declOf u) where
  invariante := fun i => nomatch i
  requires := fun _ => Expr.tru
  ensures := fun f => E f
  rumpf := fun f => B f
  unterbricht := fun f => u.hands.any (fun n => strEq n (fnAt u f).name)

/-- The generically lowered program: every function of the
    elaborated program over the declaration built from it. -/
def lowerAllg (u : UProg) :
    Except String (Programm (declOf u) × List (declOf u).Fn) :=
  match h : lowerEach u (List.finRange u.fns.length) with
  | .error e => .error e
  | .ok _ =>
    have w : ∀ f : Fin u.fns.length,
        ∃ v, lowerFnAt u f = .ok v := fun f =>
      lowerEach_all_ok u (List.finRange u.fns.length) f
        (List.mem_finRange f) h
    .ok (progOfFn u (fun f => (lowerAtPair u f (w f)).1)
      (fun f => (lowerAtPair u f (w f)).2),
      List.finRange u.fns.length)

/-! ## 104 pins on the generically lowered program -/

/-- The fragment check on the generically lowered 104 program. -/
theorem lowerAllg104fragment :
    (match lowerAllg uExp104 with
      | .ok (P, fs) => programmImFragmentG P fs
      | .error _ => false) = true := by
  decide

/-- The footprint check on the generically lowered 104 program. -/
theorem lowerAllg104fuss :
    (match lowerAllg uExp104 with
      | .ok (P, fs) => fussOrtGB P fs
      | .error _ => false) = true := by
  decide

/-- Declaration data agreement, construct by construct: the
    generic declaration built from `uExp104` agrees with the
    exporter universe `G104_referenz.gD` (counts, ranges, ranks,
    guards, held sets, writes). -/
theorem lowerAllg104data :
    (declOf uExp104).count ⟨0, by decide⟩ = 2 ∧
    G104_referenz.gD.count G104_referenz.GTab.Konto = 2 ∧
    (declOf uExp104).typ ⟨0, by decide⟩ ⟨0, by decide⟩ =
      .int 0 100 ∧
    G104_referenz.gD.typ G104_referenz.GTab.Konto
      G104_referenz.GKontoFeld.stand = .int 0 100 ∧
    (declOf uExp104).rang ⟨0, by decide⟩ = 0 ∧
    G104_referenz.gD.rang G104_referenz.GLock.M = 0 ∧
    (declOf uExp104).braucht ⟨0, by decide⟩ =
      ([.inl (⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List ((declOf uExp104).Lock ⊕
          ((declOf uExp104).Marke × Nat))) ∧
    G104_referenz.gD.braucht G104_referenz.GTab.Konto =
      [.inl G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_einzahlen =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.locks.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_lies =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).schreibt
      ⟨0, by decide⟩ = true ∧
    (G104_referenz.gD.signatur
      G104_referenz.g_einzahlen).schreibt
      G104_referenz.GTab.Konto = true ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).schreibt
      ⟨0, by decide⟩ = false ∧
    (G104_referenz.gD.signatur
      G104_referenz.g_lies).schreibt
      G104_referenz.GTab.Konto = false := by
  decide

/-! ## The real-text lexer pin for 104 -/

-- SRC-BEGIN src104real
/-- The real `beispiele/104-referenz.gab` text, one entry per source line (a long
    line cut again after a space). `zaehle-kette.py` compares the
    pieces against the file, byte for byte. WHY PIECES and not one
    literal: `Parser/Lexer.lean`'s `lex_ofList` -- one 2064-byte
    literal costs the kernel tens of gigabytes (O13). -/
def srcZeilen104 : List (List Char) :=
  ["// 104 -- The reference fixture as a ".toList,
   "real Gabbro program (lane 126).\n".toList,
   "//\n".toList,
   "// This is ".toList,
   "`grammatik/Grammatik/ReferenzB.lean` ".toList,
   "(`refD`/`refP`) in surface\n".toList,
   "// syntax: one table `Konto` of 2 slots ".toList,
   "with one `0 .. 100` field, guarded by\n".toList,
   "// the single lock `M`; `einzahlen` (one ".toList,
   "`0 .. 10` parameter, no result,\n".toList,
   "// writes the table, ensures the slot ".toList,
   "did not decrease) and `lies` (no\n".toList,
   "// parameters, one `0 .. 100` result, ".toList,
   "reads, ensures the answer equals the\n".toList,
   "// slot). Both run under the held lock ".toList,
   "(`requires Held(M)`, the `beispiele/01`\n".toList,
   "// idiom: the caller's duty, so the ".toList,
   "bodies touch the guarded slot ".toList,
   "directly).\n".toList,
   "// Not declared `concurrent`: both ".toList,
   "functions hold `M` by signature, and ".toList,
   "the\n".toList,
   "// start rule N240 (the goal theorem's ".toList,
   "`StartExklusiv`) forbids two threads\n".toList,
   "// starting in functions that share a ".toList,
   "signature lock. The earlier note: the ".toList,
   "declaration\n".toList,
   "// (lane 141: the certificate census ".toList,
   "classifies `concurrent` as erased -- ".toList,
   "the\n".toList,
   "// emitter writes nothing for it -- so ".toList,
   "the declaration passes stage 7 of\n".toList,
   "// `pruefe-emission.sh`). Threads cannot ".toList,
   "be driven from a C driver anyway, so\n".toList,
   "// the driver runs both threads one ".toList,
   "after the other -- the sequential\n".toList,
   "// composition the emitter produces: ".toList,
   "`einzahlen` like thread 1, then `lies`\n".toList,
   "// like thread 0. That is the observable ".toList,
   "half of the fixture\n".toList,
   "// (`refB_schreibt`: slot `0 -> 100`).\n".toList,
   "\n".toList,
   "module beispiel::referenz {\n".toList,
   "\n".toList,
   "const NKONTO : u32 = 2;\n".toList,
   "\n".toList,
   "type Betrag = u32 in 0 .. 10;\n".toList,
   "type Stand = u32 in 0 .. 100;\n".toList,
   "\n".toList,
   "table Konto count NKONTO {\n".toList,
   "    slot {\n".toList,
   "        stand : Stand,\n".toList,
   "    }\n".toList,
   "}\n".toList,
   "\n".toList,
   "lock M protects { stand } rank 0 held <= ".toList,
   "50 ops;\n".toList,
   "\n".toList,
   "impl fn einzahlen(k : ptr<normal, rw> ".toList,
   "Konto, i : index into Konto, b : ".toList,
   "Betrag)\n".toList,
   "    requires Held(M)\n".toList,
   "    ensures  old(k.slots[i].stand) <= ".toList,
   "k.slots[i].stand\n".toList,
   "    effects  { reads k.slots, writes ".toList,
   "k.slots, locks M }\n".toList,
   "    costs    <= 16 ops\n".toList,
   "{\n".toList,
   "    k.slots[i].stand = 100;\n".toList,
   "    lies(k, i);\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn lies(k : ptr<normal, r> Konto, i ".toList,
   ": index into Konto) -> Stand\n".toList,
   "    requires Held(M)\n".toList,
   "    ensures  result == k.slots[i].stand\n".toList,
   "    effects  { reads k.slots, locks M }\n".toList,
   "    costs    <= 8 ops\n".toList,
   "{\n".toList,
   "    return k.slots[i].stand;\n".toList,
   "}\n".toList,
   "\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END src104real

/-- The pinned text as characters. -/
def srcQuelle104 : List Char := srcZeilen104.flatten

/-- The pinned text as the `String` the chain is indexed by. -/
def src104real : String := String.ofList srcQuelle104

set_option maxHeartbeats 4000000 in
/-- **THE REAL 104 TEXT LEXES TO `tt104`** -- over the CHARACTERS, which is
    the only form the kernel ever sees (O13): the pieces are short literals,
    and the whole scan costs a fraction of one long literal's decode. -/
theorem lexL104real : lexL srcQuelle104 = .ok tt104 := by
  decide

/-- The same, as a statement about the `String` the chain is indexed by.
    `lex_ofList` carries the pin across WITHOUT running the UTF-8 decoder,
    so this theorem is a rewrite and not a reduction. -/
theorem lex104real : lex src104real = .ok tt104 := by
  show lex (String.ofList srcQuelle104) = _
  rw [lex_ofList]
  exact lexL104real

/-! ## The 104 chain, end to end -/

/-- One theorem chaining every stage for 104: real-text lexing,
    deep parsing, elaboration, generic lowering, and the fragment
    and footprint checks on the lowered program. -/
theorem kette104 : lex src104real = .ok tt104 ∧
    beqTopTief (parseTopTief tt104) (.ok items104) = true ∧
    beqElabU (elabU items104) (.ok uExp104) = true ∧
    (match lowerAllg uExp104 with
      | .ok (P, fs) => programmImFragmentG P fs && fussOrtGB P fs
      | .error _ => false) = true := by
  refine ⟨lex104real, u104parse, u104elab, ?_⟩
  decide

/-! ## 108 preprocessing: `concurrent` stripping, bare-`u32` norms -/

/-- Bare `u32` as its full range (what the exporter computes
    with, per `Export108.lean` CUTS). -/
def u32Voll : STyp :=
  .range (.atom "u32") (.lit 0) (.lit 4294967295) false

/-- A type with bare `u32` normalised (lane 160 has no
    full-range rule by design; the normalisation lives here,
    never by editing `Uebersetze.lean`). -/
def normTypU32 : STyp → STyp
  | .atom a => if a == "u32" then u32Voll else .atom a
  | t => t

/-- A slot field with bare `u32` normalised. -/
def normFeldU32 (f : SFeld) : SFeld :=
  { f with ftyp := normTypU32 f.ftyp }

/-- A table part with bare `u32` normalised. -/
def normTabTeilU32 : STabTeil → STabTeil
  | .tSlot fds => .tSlot (fds.map normFeldU32)
  | t => t

/-- A function head with bare `u32` normalised (parameters and
    result). -/
def normSigU32 (s : FnSig) : FnSig :=
  { s with params := s.params.map (fun p => (p.1, normTypU32 p.2)), res := s.res.map normTypU32 }

/-- One item with bare `u32` normalised (no module recursion:
    `uMembers` unwraps the single module `elabU` supports). -/
def normU32Item : SItemTief → SItemTief
  | .tableT n c a b g parts =>
    .tableT n c a b g (parts.map normTabTeilU32)
  | .fnT s k => .fnT (normSigU32 s) k
  | it => it

/-- Bare `u32` normalised over a top-level list. -/
def normTopU32 : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => normU32Item it :: normTopU32 rest

/-- The preprocessing of the bridge instances: unwrap like `elabU`, then normalise bare `u32`,
    before `elabU` (`concurrent` items are elaborated into the thread roots now). -/
def pre108 (items : List SItemTief) : List SItemTief :=
  normTopU32 (uMembers items)

/-! ## 108 pins: strip, normalise, elaborate, lower -/

-- SRC-BEGIN src108
/-- The real `beispiele/108-disjoint-start-locks.gab` text, one entry per source line (a long
    line cut again after a space). `zaehle-kette.py` compares the
    pieces against the file, byte for byte. WHY PIECES and not one
    literal: `Parser/Lexer.lean`'s `lex_ofList` -- one 2082-byte
    literal costs the kernel tens of gigabytes (O13). -/
def srcZeilen108 : List (List Char) :=
  ["// 108 -- Two lock-free readers over one ".toList,
   "shared, never-written table.\n".toList,
   "//\n".toList,
   "// TRANSFER of `StartExklusiv` ".toList,
   "(`RufMaschineG.lean`): the start ".toList,
   "functions of\n".toList,
   "// distinct threads hold no signature ".toList,
   "lock in common -- and since lane 183\n".toList,
   "// (`wurzelnB`) they hold NO signature ".toList,
   "lock at all: nobody holds a lock for a\n".toList,
   "// thread before it starts. This file ".toList,
   "used to show the disjoint shape\n".toList,
   "// (`read_a` under `Held(L)`, `read_c` ".toList,
   "under `Held(M)`); that shape is now\n".toList,
   "// refused at both starts (`N303`), and ".toList,
   "the take-inside remedy has no G form\n".toList,
   "// for value readers (`LG004`: no ".toList,
   "`return` under `locks`). What remains ".toList,
   "is\n".toList,
   "// the silent side both rules share: two ".toList,
   "readers over one table nobody\n".toList,
   "// writes -- every rule stays silent ".toList,
   "(`N240`/`N303`: nothing held; `N290`/\n".toList,
   "// `N291`/`N300`/`N301`: unwritten ".toList,
   "carriers; `W001`: reads overlap ".toList,
   "freely).\n".toList,
   "// The refused root shape lives in ".toList,
   "`beispiele/gift/967`, the pair side in\n".toList,
   "// gifts 910-915. The G export of this ".toList,
   "file is pinned in\n".toList,
   "// ".toList,
   "`grammatik/Grammatik/Export108.lean`.\n".toList,
   "//\n".toList,
   "// Evidence: the pre-183 program this ".toList,
   "file replaces, kept verbatim as a\n".toList,
   "// comment. It is refused since lane 183 ".toList,
   "at both starts by `N303`\n".toList,
   "// (`wurzelnB`: `D.haelt w = []` -- ".toList,
   "nobody holds a lock for a thread before\n".toList,
   "// it starts), although `N240` stays ".toList,
   "silent on it (disjoint held sets):\n".toList,
   "//   table U count 4 {\n".toList,
   "//       slot { v : u32, }\n".toList,
   "//   }\n".toList,
   "//   lock L protects { T } rank 0 held ".toList,
   "<= 100 ops;\n".toList,
   "//   lock M protects { U } rank 1 held ".toList,
   "<= 100 ops;\n".toList,
   "//   impl fn read_a() -> u32\n".toList,
   "//       requires Held(L)\n".toList,
   "//       effects { reads T.slots }\n".toList,
   "//       costs <= 4 ops\n".toList,
   "//   {\n".toList,
   "//       return T.slots[0].v;\n".toList,
   "//   }\n".toList,
   "//   impl fn read_c() -> u32\n".toList,
   "//       requires Held(M)\n".toList,
   "//       effects { reads U.slots }\n".toList,
   "//       costs <= 4 ops\n".toList,
   "//   {\n".toList,
   "//       return U.slots[0].v;\n".toList,
   "//   }\n".toList,
   "module beispiel::disjoint_start_locks {\n".toList,
   "\n".toList,
   "table T count 4 {\n".toList,
   "    slot { v : u32, }\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn read_a() -> u32\n".toList,
   "    effects { reads T.slots }\n".toList,
   "    costs <= 4 ops\n".toList,
   "{\n".toList,
   "    return T.slots[0].v;\n".toList,
   "}\n".toList,
   "\n".toList,
   "impl fn read_c() -> u32\n".toList,
   "    effects { reads T.slots }\n".toList,
   "    costs <= 4 ops\n".toList,
   "{\n".toList,
   "    return T.slots[1].v;\n".toList,
   "}\n".toList,
   "\n".toList,
   "concurrent { read_a, read_c };\n".toList,
   "\n".toList,
   "}\n".toList]
-- SRC-END src108

/-- The pinned text as characters. -/
def srcQuelle108 : List Char := srcZeilen108.flatten

/-- The pinned text as the `String` the chain is indexed by. -/
def src108 : String := String.ofList srcQuelle108

/-- The token list of the 108 source (`lex108` checks it). -/
def toks108 : List Token := [.wort "module",
 .ident "beispiel",
 .zeichen "::",
 .ident "disjoint_start_locks",
 .zeichen "{",
 .wort "table",
 .ident "T",
 .wort "count",
 .num 4,
 .zeichen "{",
 .wort "slot",
 .zeichen "{",
 .ident "v",
 .zeichen ":",
 .wort "u32",
 .zeichen ",",
 .zeichen "}",
 .zeichen "}",
 .wort "impl",
 .wort "fn",
 .ident "read_a",
 .zeichen "(",
 .zeichen ")",
 .zeichen "->",
 .wort "u32",
 .wort "effects",
 .zeichen "{",
 .wort "reads",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "}",
 .wort "costs",
 .zeichen "<=",
 .num 4,
 .wort "ops",
 .zeichen "{",
 .wort "return",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "[",
 .num 0,
 .zeichen "]",
 .zeichen ".",
 .ident "v",
 .zeichen ";",
 .zeichen "}",
 .wort "impl",
 .wort "fn",
 .ident "read_c",
 .zeichen "(",
 .zeichen ")",
 .zeichen "->",
 .wort "u32",
 .wort "effects",
 .zeichen "{",
 .wort "reads",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "}",
 .wort "costs",
 .zeichen "<=",
 .num 4,
 .wort "ops",
 .zeichen "{",
 .wort "return",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "[",
 .num 1,
 .zeichen "]",
 .zeichen ".",
 .ident "v",
 .zeichen ";",
 .zeichen "}",
 .wort "concurrent",
 .zeichen "{",
 .ident "read_a",
 .zeichen ",",
 .ident "read_c",
 .zeichen "}",
 .zeichen ";",
 .zeichen "}",
 .ende]


set_option maxHeartbeats 4000000 in
/-- **THE REAL 108 TEXT LEXES TO `toks108`**, over the characters (O13). -/
theorem lexL108 : lexL srcQuelle108 = .ok toks108 := by
  decide

/-- The same, as a statement about the `String` -- through `lex_ofList`
    and never through the UTF-8 decoder (O13). -/
theorem lex108 : lex src108 = .ok toks108 := by
  show lex (String.ofList srcQuelle108) = _
  rw [lex_ofList]
  exact lexL108

/-- The parsed 108 surface tree (raw, `concurrent` inside;
    `parse108` checks it against the reader). -/
def items108 : List SItemTief := [.modT
   "beispiel::disjoint_start_locks"
   [.tableT
      "T"
      (some (.lit 4))
      none
      none
      false
      [.tSlot
         [{ fname := "v",
            ftyp := .atom "u32",
            pos := none,
            bezug := none,
            wo := none,
            reserviert := false,
            byOps := false }]],
    .fnT
      { art := "impl",
        name := "read_a",
        params := [],
        res := some (.atom "u32"),
        fehler := none,
        klauseln := [.effs
                       [.reads
                          (.field (.variable "T") "slots")],
                     .cost (.lit 4)] }
      (.block
        []
        (some (.ret
           (some (.field
              (.index
                (.field (.variable "T") "slots")
                (.lit 0))
              "v"))))),
    .fnT
      { art := "impl",
        name := "read_c",
        params := [],
        res := some (.atom "u32"),
        fehler := none,
        klauseln := [.effs
                       [.reads
                          (.field (.variable "T") "slots")],
                     .cost (.lit 4)] }
      (.block
        []
        (some (.ret
           (some (.field
              (.index
                (.field (.variable "T") "slots")
                (.lit 1))
              "v"))))),
    .concT [["read_a"], ["read_c"]]]]

theorem parse108 : beqTopTief (parseTopTief toks108) (.ok items108) = true := by
  decide

/-- The elaborated 108 program (`elab108` checks it against
    the elaborator run after `pre108`). -/

def uExp108 : UProg := { tabs := [{ name := "T", count := 4, cols := [("v", 0, 4294967295)] }], locks := [], fns := [{ name := "read_a", params := [], kinds := [], res := some (0, 4294967295), held := [], puts := [], gives := [], body := [], ret := .val (.tab "T" "v" (.lit 0)) }, { name := "read_c", params := [], kinds := [], res := some (0, 4294967295), held := [], puts := [], gives := [], body := [], ret := .val (.tab "T" "v" (.lit 1)) }], roots := ["read_a", "read_c"] }

theorem elab108 : beqElabU (elabU (pre108 items108)) (.ok uExp108) = true := by
  decide

/-- The fragment check on the generically lowered 108 program. -/
theorem lowerAllg108fragment :
    (match lowerAllg uExp108 with
      | .ok (P, fs) => programmImFragmentG P fs
      | .error _ => false) = true := by
  decide

/-- The footprint check on the generically lowered 108 program. -/
theorem lowerAllg108fuss :
    (match lowerAllg uExp108 with
      | .ok (P, fs) => fussOrtGB P fs
      | .error _ => false) = true := by
  decide

/-- Declaration data agreement for 108: the generic
    declaration built from `uExp108` agrees with the exporter
    universe `G108_disjoint_start_locks.gD`. -/
theorem lowerAllg108data :
    (declOf uExp108).count ⟨0, by decide⟩ = 4 ∧
    G108_disjoint_start_locks.gD.count G108_disjoint_start_locks.GTab.T = 4 ∧
    (declOf uExp108).typ ⟨0, by decide⟩ ⟨0, by decide⟩ = .int 0 4294967295 ∧
    G108_disjoint_start_locks.gD.typ G108_disjoint_start_locks.GTab.T G108_disjoint_start_locks.GTFeld.v = .int 0 4294967295 ∧
    ((declOf uExp108).signatur ⟨0, by decide⟩).haelt = ([] : List (declOf uExp108).Lock) ∧
    G108_disjoint_start_locks.gD.haelt G108_disjoint_start_locks.g_read_a = [] ∧
    ((declOf uExp108).signatur ⟨1, by decide⟩).haelt = ([] : List (declOf uExp108).Lock) ∧
    G108_disjoint_start_locks.gD.haelt G108_disjoint_start_locks.g_read_c = [] ∧
    ((declOf uExp108).signatur ⟨0, by decide⟩).schreibt ⟨0, by decide⟩ = false ∧
    (G108_disjoint_start_locks.gD.signatur G108_disjoint_start_locks.g_read_a).schreibt G108_disjoint_start_locks.GTab.T = false ∧
    ((declOf uExp108).signatur ⟨1, by decide⟩).schreibt ⟨0, by decide⟩ = false ∧
    (G108_disjoint_start_locks.gD.signatur G108_disjoint_start_locks.g_read_c).schreibt G108_disjoint_start_locks.GTab.T = false := by
  decide

/-- One theorem chaining every stage for 108. -/
theorem kette108 : lex src108 = .ok toks108 ∧
    beqTopTief (parseTopTief toks108) (.ok items108) = true ∧
    beqElabU (elabU (pre108 items108)) (.ok uExp108) = true ∧
    (match lowerAllg uExp108 with
      | .ok (P, fs) => programmImFragmentG P fs && fussOrtGB P fs
      | .error _ => false) = true := by
  refine ⟨lex108, parse108, elab108, ?_⟩
  decide

end Gabbro.Grammatik.Parser.UebersetzeAllg2

/-
  CUTS: what is not proved here.

  1. `RufPasst` harvest is exactness in disguise: `hh` asks the
     callee held set inside the caller resources, `hx` (with every
     floor `none`) asks the reverse, so a call lowers only at an
     exact held set -- the same refusal `uAnw` states over names.
     A floor-bearing declaration would need the rank checks
     computed, not harvested; `mkSig` never sets `boden`.
  2. `beq`-style soundness is proved for nothing new here; the
     `beqElabU`/`beqTopTief` pins are reused from `Uebersetze.lean`
     (same cut as there).
  3. The shift fix in `UebersetzeAllg.lean` (`sh` on `lowIdx`,
     `lowParamSide`, `lowDurch`, `lowTabRead`, `lowAltRead`):
     `ensures` positions ride one past the result when one is
     present. Without it `lowerAllg` fails on every result-bearing
     function whose contract reads a slot (measured on `lies`).
  4. 108 is done the same way as 104: `pre108` unwraps the
     module and normalises bare `u32` to its
     full range before `elabU`; `toks108`/`items108`/`uExp108`
     are probe-generated literals (`#eval` + `Repr`, then pinned
     by `lex108`/`parse108`/`elab108`), with the fragment,
     footprint, data and chaining pins on top.
  5. Membership across the `Fin`/carrier line does not synthesize:
     `L ∈ S.haelt` with `L : Fin _` has no `Decidable` instance,
     the unfolded `∀ w ∈ braucht` form and `D.Lock`-quantified
     harvests do. List literals compared against carrier lists
     need an explicit `List (declOf u).Lock` ascription.
-/

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.sigSchreibt_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.nach_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerEach_all_ok
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg104fragment
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg104fuss
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg104data
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lex104real
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.kette104
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lex108
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.parse108
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.elab108
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg108fragment
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg108fuss
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.lowerAllg108data
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg2.kette108
