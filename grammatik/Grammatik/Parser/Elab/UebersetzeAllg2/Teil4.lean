module

public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Korpus.Programme.Export108
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil3
public import Grammatik.Bausteine.Arena.ArenaStaticReset
public import Grammatik.Kern.Semantik.Semantik.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000

/-- `p(..);` through a function pointer (`Stmt.callInd`): against the signature of `p`'s type. -/
def lowCallIndL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (p _cname : String) (args : List UArg) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match lowZeigerN u Γ fn p with
  | .error e => .error e
  | .ok ⟨n, v⟩ =>
    match lowRufKopfN u caller Γ fn Λ n args with
    | .error e => .error e
    | .ok k =>
      if hr : ((declOf u).sigNr n).gruende = 0 then
        have s := Stmt.callInd (D := declOf u) (l := l) (n := n) (Expr.var v) k.args k.hp hr
        .ok (by rw [nachSigAt_eq u n Λ] at s; exact s)
      else .error "call of a function with a reason channel needs `let .. else`"

/-- `transition T.slots[i].f : A -> B;` (`Stmt.shift`): the stage `B` in the field's range, the pair declared
    (`D.erlaubt`), the write right and the guards. -/
def lowShiftL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b fname : String) (ix : UIdx) (von nach : Int) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn 0 t ix with
      | .error e => .error e
      | .ok i =>
        if hn : fh.range.1 ≤ nach ∧ nach ≤ fh.range.2 then
          if he : (declOf u).erlaubt t fh.idx von nach = true then
            if hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ then
              if hw : writesAt u (fnAt u caller) t = true then
                have hwV : (verOf u caller).schreibt t = true := by
                  show (vertragVon (declOf u) caller).schreibt t = true
                  rw [vSchreibt_eq u caller t]
                  exact hw
                .ok (Stmt.shift (D := declOf u) t fh.idx fh.hint i von nach hn he hwV hL)
              else .error "write without right"
            else .error "access without held guard"
          else .error "transition not allowed at the field"
        else .error "stage outside the field's range"

/-- An array literal of `m` copies of `z` (C18): the value-level zero repeated `m` times,
    for the checked static-array reset. -/
def repZeroArr (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {elem : Ty}
    (z : Expr (declOf u) Γ Λ elem) : (m : Nat) → Expr (declOf u) Γ Λ (.arr elem m)
  | 0 => Expr.arrNil
  | m + 1 => Expr.arrCons z (repZeroArr u z m)

/-- The zero of a zero-admitting type as an expression (C18): numbers read `0`, truth values
    read `false`, arrays recurse element by element, strings are empty. -/
def zeroResetExpr (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} :
    (τ : Ty) → ZeroAdmitting τ → Expr (declOf u) Γ Λ τ
  | .int lo hi, .intZero h1 h2 => Expr.widen h1 h2 (Expr.lit 0)
  | .bool, .boolZero => Expr.fls
  | .arr elem m, .arrZero h' => repZeroArr u (zeroResetExpr u elem h') m
  | .str n, .strZero => Expr.strLit [] (Nat.zero_le n)
  | .prod _ _, h => absurd h (by intro h; cases h)

/-- A static-array index as an expression (C18): the literal `j` inside `0 ..< len`. -/
def resetIdxExpr (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {len : Nat}
    (j : Nat) (h : j < len) : Expr (declOf u) Γ Λ (.index (len : Int)) :=
  Expr.widen (by omega : (0 : Int) ≤ (j : Int)) (by omega : (j : Int) ≤ (len : Int) - 1)
    (Expr.lit (j : Int))

/-- The array with `[i, i + k)` zeroed (C18): `base` updated at each selected index from the
    left. Needs `i + k ≤ len`. -/
def resetRangeExpr (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {elem : Ty} {len : Nat}
    (base : Expr (declOf u) Γ Λ (.arr elem len)) (zero : Expr (declOf u) Γ Λ elem)
    (i : Nat) : (k : Nat) → i + k ≤ len → Expr (declOf u) Γ Λ (.arr elem len)
  | 0, _ => base
  | k + 1, h =>
    Expr.arrSet (resetRangeExpr u base zero i k (by omega))
      (resetIdxExpr (len := len) u (i + k) (by omega)) zero

/-- One more updated index stays inside the range-store law (C18): setting `i + k` in the
    `k`-prefix gives the `(k + 1)`-prefix. -/
theorem arrSetW_resetFinW {α : Type} {n : Nat} (a : Fin n → α) (i k : Nat)
    (h : i + (k + 1) ≤ n) (zero : α) (idx : Fin n) (hidx : idx.val = i + k)
    (j : Fin n) :
    arrSetW (resetFinW a i k zero) idx zero j = resetFinW a i (k + 1) zero j := by
  simp only [arrSetW, resetFinW]
  by_cases hj : j = idx
  · subst hj
    have h1 : i ≤ idx.val := by omega
    have h2 : idx.val < i + (k + 1) := by omega
    simp [h1, h2, hidx]
  · simp only [hj, ↓reduceIte]
    by_cases h1 : i ≤ j.val
    · by_cases h2 : j.val < i + k
      · have h3 : j.val < i + (k + 1) := by omega
        simp [h1, h2, h3]
      · by_cases h4 : j.val < i + (k + 1)
        · have h5 : j.val = i + k := by omega
          have hEq : j = idx := by
            apply Fin.ext
            simp [h5, hidx]
          exact absurd hEq hj
        · simp [h1, h2, h4]
    · simp [h1]

/-- An array literal of copies evaluates to the constant function (C18). -/
theorem repZeroArr_eval (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {elem : Ty}
    (z : Expr (declOf u) Γ Λ elem) (m : Nat) (σ₀ σ : World (declOf u))
    (ρ : Env (declOf u) Γ) :
    eval σ₀ (repZeroArr u z m) σ ρ = fun _ => eval σ₀ z σ ρ := by
  induction m with
  | zero =>
    simp only [repZeroArr, eval]
    funext j
    exact j.elim0
  | succ m ih =>
    simp only [repZeroArr, eval, ih]
    funext j
    simp only [arrConsW]
    by_cases hj : j.val = 0
    · simp [hj]
    · simp [hj]

/-- The expression zero evaluates to the value zero (C18). -/
theorem zeroResetExpr_eval (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))}
    (τ : Ty) (h : ZeroAdmitting τ) (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) :
    eval σ₀ (zeroResetExpr u τ h) σ ρ = zeroValue τ h := by
  induction h with
  | intZero h1 h2 => rfl
  | boolZero => rfl
  | arrZero h' ih =>
    simp only [zeroResetExpr]
    rw [repZeroArr_eval, ih]
    rfl
  | strZero => rfl

/-- A static-array index literal evaluates to its number (C18). -/
theorem resetIdxExpr_val (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {len : Nat}
    (j : Nat) (h : j < len) (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) :
    (eval σ₀ (resetIdxExpr u j h) σ ρ).fin.val = j := by
  simp only [resetIdxExpr, eval, Zahl.weiter, Zahl.fin]
  omega

/-- The range update evaluates to `resetFinW` (C18): zero inside the range, unchanged
    outside. -/
theorem resetRangeExpr_eval (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {elem : Ty}
    {len : Nat} (base : Expr (declOf u) Γ Λ (.arr elem len))
    (zero : Expr (declOf u) Γ Λ elem) (i k : Nat) (σ₀ σ : World (declOf u))
    (ρ : Env (declOf u) Γ) :
    ∀ h : i + k ≤ len,
      eval σ₀ (resetRangeExpr u base zero i k h) σ ρ =
        resetFinW (eval σ₀ base σ ρ) i k (eval σ₀ zero σ ρ) := by
  revert h
  induction k with
  | zero =>
    intro h
    simp only [resetRangeExpr]
    funext j
    simp only [resetFinW]
    have hn : ¬ (i ≤ j.val ∧ j.val < i + 0) := by omega
    simp [hn]
  | succ k ih =>
    intro h
    have hk : i + k ≤ len := by omega
    have e := ih hk
    simp only [resetRangeExpr, eval, e]
    funext j
    have hidx : (eval σ₀ (resetIdxExpr (len := len) u (i + k) (by omega)) σ ρ).fin.val
        = i + k := by
      exact resetIdxExpr_val (len := len) u (i + k) (by omega) σ₀ σ ρ
    exact arrSetW_resetFinW _ _ _ h _ _ hidx j

/-- A selected index reads zero after the lowered reset (C18). -/
theorem resetRangeExpr_zero_in (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))} {elem : Ty}
    {len : Nat} (base : Expr (declOf u) Γ Λ (.arr elem len))
    (zero : Expr (declOf u) Γ Λ elem) (i k : Nat) (h : i + k ≤ len)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (j : Fin len)
    (h1 : i ≤ j.val) (h2 : j.val < i + k) :
    eval σ₀ (resetRangeExpr u base zero i k h) σ ρ j = eval σ₀ zero σ ρ := by
  rw [resetRangeExpr_eval u base zero i k σ₀ σ ρ h]
  exact resetFinW_get_in _ _ _ _ _ h1 h2

/-- An index outside the lowered reset keeps its old value (C18). -/
theorem resetRangeExpr_outside_same (u : UProg) {Γ : Ctx} {Λ : List (Res (declOf u))}
    {elem : Ty} {len : Nat} (base : Expr (declOf u) Γ Λ (.arr elem len))
    (zero : Expr (declOf u) Γ Λ elem) (i k : Nat) (h : i + k ≤ len)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (j : Fin len)
    (hh : ¬ (i ≤ j.val ∧ j.val < i + k)) :
    eval σ₀ (resetRangeExpr u base zero i k h) σ ρ j = eval σ₀ base σ ρ j := by
  rw [resetRangeExpr_eval u base zero i k σ₀ σ ρ h]
  exact resetFinW_get_out _ _ _ _ _ hh

/-- `reset A at i count n;` over a zero-initialized static array (C18): the checked
    range-store expansion into `Stmt.assignGlob` of the array with `[i, i + n)` zeroed via
    iterated `Expr.arrSet` (no new kernel constructor). Both operands must be statically
    known (a singleton lowered range; literals are the closed case): their values give `i`
    and `k`, the range check `rangeOk` refuses an outside range, and a non-zero-admitting
    element type is refused. The operand terms are pure and total with type-determined
    values, so no `Block.bind` is needed for the single-statement lowering; the page-return
    transfer (C08 grant ledger) stays open and is not emitted here. -/
def lowResetRangeL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (a : String) (iu nu : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match globIdx u.globs a with
  | .error e => .error e
  | .ok g =>
    match hty : (globAt u g).ty with
    | .wert (.arr elem len) =>
      if hz : zeroAdmittingB elem = true then
        match lowSideVal u Γ Λ fn iu with
        | .error e => .error e
        | .ok si =>
          match lowSideVal u Γ Λ fn nu with
          | .error e => .error e
          | .ok sn =>
            if hi : si.range.1 = si.range.2 then
              if hn : sn.range.1 = sn.range.2 then
                if h0i : 0 ≤ si.range.1 then
                  if h0n : 0 ≤ sn.range.1 then
                    if hok : rangeOk len si.range.1.toNat sn.range.1.toNat = true then
                      have hElem : ZeroAdmitting elem := (zeroAdmittingB_iff).mp hz
                      have _hr := (rangeOk_iff).mp hok
                      if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
                        if hw : writesGAt u (fnAt u caller) g = true then
                          have hwV : (verOf u caller).gschreibt g = true := by
                            show (vertragVon (declOf u) caller).gschreibt g = true
                            rw [vGSchreibt_eq u caller g]
                            exact hw
                          have hg : (declOf u).gtyp g = .arr elem len := by
                            show (globAt u g).ty.toTy = _
                            rw [hty]
                            rfl
                          have eArr : Expr (declOf u) Γ Λ (.arr elem len) :=
                            resetRangeExpr u (Expr.glob (D := declOf u) g hd)
                              (zeroResetExpr u elem hElem) si.range.1.toNat sn.range.1.toNat
                              (by omega)
                          have e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp g) := by
                            rw [hg]
                            exact eArr
                          .ok (Stmt.assignGlob (D := declOf u) g e2 hwV hd)
                        else .error "write without right"
                      else .error "access without held guard"
                    else .error "reset range outside its static array"
                  else .error "reset count negative"
                else .error "reset start negative"
              else .error "reset count not statically known"
            else .error "reset start not statically known"
      else .error "reset of a static with a zero-less element type"
    | _ => .error "reset range of a static that is not a static array"

/-- One non-marker statement at the held list `Λ`, in the scope `Γ`/`fn` (the parameters and the
    `let` bindings read so far). -/
def lowStmtL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) : UStmt →
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ)
  | .assign b f ix v => (lowAssignDurchW u caller Γ fn Λ b f ix v).getD (lowAssignDurchL u caller Γ fn Λ b f ix v)
  | .assignTab b f ix v => (lowAssignTabW u caller Γ fn Λ b f ix v).getD (lowAssignTabL u caller Γ fn Λ b f ix v)
  | .assignB b f ix v => lowAssignDurchBL u caller Γ fn Λ b f ix v
  | .assignTabB b f ix v => lowAssignTabBL u caller Γ fn Λ b f ix v
  | .assignOpt b f ix v => lowAssignDurchOL u caller Γ fn Λ b f ix v
  | .assignTabOpt b f ix v => lowAssignTabOL u caller Γ fn Λ b f ix v
  | .assignGlob n v => lowAssignGlobL u caller Γ fn Λ n v
  | .assignGlobB n v => lowAssignGlobBL u caller Γ fn Λ n v
  | .assignGlobO n o => lowAssignGlobOL u caller Γ fn Λ n o
  | .storeAtom n v => lowStoreAtomL u caller Γ fn Λ n v
  | .storeAtomB n v => lowStoreAtomBL u caller Γ fn Λ n v
  | .setVar x v => lowSetVarL u caller Γ fn Λ x v
  | .setVarB x v => lowSetVarBL u caller Γ fn Λ x v
  | .call c args => lowCallL u caller Γ fn Λ c args
  | .regWrite d r v => lowRegWriteL u caller Γ fn Λ d r v
  | .regWriteB d r v => lowRegWriteBL u caller Γ fn Λ d r v
  | .callInd p f args => lowCallIndL u caller Γ fn Λ p f args
  | .shiftTab b f ix _ von nach => lowShiftL u caller Γ fn Λ b f ix von nach
  | .assignRef r f v => lowAssignRefL u caller Γ fn Λ r f v
  | .lockBeg _ => .error "lower: a locks block opens here"
  | .blkEnd => .error "lower: a block closes here without opening"
  | .resetRange a iu nu => lowResetRangeL u caller Γ fn Λ a iu nu
  | .floatLit .. | .float .. =>
    .error "float: IEEE introduction requires a continuing G block; no canonical Endblock form"
  | .bind .. | .bindB .. | .bindMut .. | .bindCall .. | .axCall .. | .bindAx .. | .narrowBeg .. | .retryBeg .. | .foreverBeg .. | .bindOpt .. | .matchBeg .. | .startS | .allocBeg .. | .bindOptBeg .. | .bindOptElseBeg .. | .allocReqBeg .. | .bindElse .. | .matchWhyBeg .. | .bindSum .. | .matchTagBeg .. | .bindAxElse .. | .ifBeg _ | .ifElse | .arrayLoopBeg .. | .loopBeg .. | .regRead .. | .regReadElse .. | .awaitBind .. | .bindFnref .. | .bindCallInd .. | .bindCallIndElse .. | .bindW .. | .tausch .. | .ifEnde .. =>
    .error "lower: a let, if or traverse is read by the block reader"
  | .ret _ => .error "lower: return in the middle of a body has no G form"
  | .leave _ => .error "lower: leave outside a traverse"
  | .next _ => .error "lower: next outside a traverse"

/-- A `let` value in the scope: its lowered side, inside the annotated range when there is one. -/
def lowBindWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (d : Option (Int × Int)) (v : USide) : Except String (LowSide u Γ Λ) :=
  match lowSideVal u Γ Λ fn v with
  | .error e => .error e
  | .ok s =>
    match d with
    | none => .ok s
    | some (lo, hi) =>
      if lo ≤ s.range.1 ∧ s.range.2 ≤ hi then .ok s
      else .error "let: value outside the annotated range"

/-- A `let` of an aggregate value: at its declared type, or at the type the value has. -/
def lowBindW (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn)
    (d : Option Ty) (v : USide) : Except String (LowWert u Γ Λ) :=
  match d with
  | some τ =>
    match lowWertAtE u Γ Λ fn none τ v with
    | .error e => .error e
    | .ok e => .ok ⟨τ, e⟩
  | none => lowWertE u Γ Λ fn none v

/-- The scope after a `let` of a value of type `τ`. -/
def _root_.Gabbro.Grammatik.Parser.Uebersetze.UFn.mitWert (f : UFn) (x : String) (τ : Ty) : UFn :=
  { f with params := (x, τ) :: f.params, kinds := (match τ with | .bool => .bool | t => uArtVon t) :: f.kinds }

end Gabbro.Grammatik.Parser.UebersetzeAllg2
