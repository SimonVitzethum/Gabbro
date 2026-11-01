module

public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Korpus.Programme.Export108
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil3

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
  | .bind .. | .bindB .. | .bindMut .. | .bindCall .. | .axCall .. | .bindAx .. | .narrowBeg .. | .retryBeg .. | .foreverBeg .. | .bindOpt .. | .matchBeg .. | .startS | .allocBeg .. | .bindElse .. | .matchWhyBeg .. | .bindSum .. | .matchTagBeg .. | .bindAxElse .. | .ifBeg _ | .ifElse | .arrayLoopBeg .. | .loopBeg .. | .regRead .. | .regReadElse .. | .awaitBind .. | .bindFnref .. | .bindCallInd .. | .bindW .. | .tausch .. | .ifEnde .. =>
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
