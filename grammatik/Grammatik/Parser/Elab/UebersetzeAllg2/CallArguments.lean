module
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- An index argument as a `UIdx` (literals and index parameters
    travel; every other side has no argument form). -/
def uIdxOfSide : USide → Except String UIdx
  | .lit n => .ok (.lit n)
  | .param p => .ok (.param p)
  | _ => .error "argument without G form"

/-- A reason value of `Ty.why n`: a case `R::C` or a variable of the scope. -/
def lowGrund (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (n : Nat) :
    UGrund → Except String (Expr (declOf u) Γ Λ (.why n))
  | .fall i => if h : i < n then .ok (Expr.why n ⟨i, h⟩) else .error "reason case outside the type"
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match lowVar Γ j (.why n) with
      | .error e => .error e
      | .ok v => .ok (Expr.var v)

/-- One call argument against the callee parameter kind and the
    recorded parameter type (the `tr_arg` of `lean_g.rs`). An owned callee
    capability passes only with its identity preserved and its owner guard
    held (`darf` over `braucht`, whose `.inr` entry is the owner mark resolved
    through `eignerMarke`); the caller's `RufPasst.ownerReady` carries the flow. -/
def lowCallArgOneL (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (k : UParamArt) (t : Ty) : UArg →
    Except String
      (Expr (declOf u) Γ Λ t)
  | a =>
    match k, t with
    | .ptr cap, .ptr ⟨space, ⟨read, write, none⟩, .table n⟩ =>
      let target : DataCapTy := ⟨space, ⟨read, write, none⟩, .table n⟩
      if hK : cap = target then
        match a with
        | .var name =>
          match paramPos fn.params name with
          | .error e => .error e
          | .ok j =>
            match fn.kinds[j]? with
            | some (.ptr source) =>
              if source = target then
                match lowVar Γ j (.ptr target) with
                | .error e => .error e
                | .ok x =>
                  if hn : n < u.tabs.length then do
                    let _ ← checkedTableCap u space n hn
                    pure (Expr.var x)
                  else .error "pointer table unknown"
              else .error "pointer argument requires an explicit checked attenuation"
            | _ => .error "pointer argument without G form"
        | .freshPtr name descriptor =>
          if descriptor = target then
            match tabIdx u.tabs name with
            | .error e => .error e
            | .ok ft =>
              if hT : ft.val = n then
                have hn : n < u.tabs.length := hT ▸ ft.isLt
                do
                  let cap ← checkedTableCap u space n hn
                  have same : (⟨n, hn⟩ : Fin u.tabs.length) = ft := Fin.ext hT.symm
                  pure (Expr.ptrOf (D := declOf u) ft n (cap.down.trans (congrArg some same)) (read, write))
              else .error "argument of foreign table"
          else .error "argument capability without G form"
        | _ => .error "value for pointer without G form"
      else .error "argument capability without G form"
    | .ptr cap, .ptr ⟨space, ⟨read, write, some owner⟩, .table n⟩ =>
      let target : DataCapTy := ⟨space, ⟨read, write, some owner⟩, .table n⟩
      if hK : cap = target then
        match eignerMarke u owner with
        | none => .error "owned pointer argument without a declared owner mark"
        | some _ =>
          if hT : n < u.tabs.length then
            if hL : ∀ wdd ∈ (declOf u).braucht ⟨n, hT⟩, Res.von (declOf u) wdd ∈ Λ then
              match a with
              | .var name =>
                match paramPos fn.params name with
                | .error e => .error e
                | .ok j =>
                  match fn.kinds[j]? with
                  | some (.ptr source) =>
                    if source = target then
                      match lowVar Γ j (.ptr target) with
                      | .error e => .error e
                      | .ok x => do
                        let _ ← checkedTableCap u space n hT
                        pure (Expr.var x)
                    else .error "pointer argument requires an explicit checked attenuation"
                  | _ => .error "pointer argument without G form"
              | _ => .error "owned fresh pointer without G form"
            else .error "owned pointer argument without held guard"
          else .error "pointer table unknown"
      else .error "argument capability without G form"
    | .index num, t =>
      match t with
      | .int lo hi =>
        match a with
        | .val s =>
          if h : num < u.tabs.length then
            if hLo : lo = 0 then
              if hHi : hi = (declOf u).count ⟨num, h⟩ - 1 then
                match uIdxOfSide s with
                | .error e => .error e
                | .ok ix =>
                  match lowIdx u Γ Λ
                      fn 0 ⟨num, h⟩ ix with
                  | .error e => .error e
                  | .ok e =>
                    have eI : Expr (declOf u) Γ
                        Λ (.int lo hi) := by
                      rw [hLo, hHi]
                      exact e
                    .ok eI
              else .error "argument range without G form"
            else .error "argument range without G form"
          else .error "index table unknown"
        | _ => .error "argument without G form"
      | _ => .error "argument type without G form"
    | .int, .int lo hi =>
      match a with
      | .val s =>
        match lowWertAt u Γ Λ
            fn lo hi s with
        | .error e => .error e
        | .ok e => .ok e
      | _ => .error "argument without G form"
    | .bool, .bool =>
      match a with
      | .bval b => lowEns u Γ Λ fn none b
      | _ => .error "argument without G form"
    | .opt num, .opt n =>
      match a with
      | .oval o =>
        if hnum : num < u.tabs.length then
          if hn : (declOf u).count ⟨num, hnum⟩ = n then
            match lowOpt u Γ Λ fn 0 num hnum o with
            | .error e => .error e
            | .ok e => .ok (by rw [← hn]; exact e)
          else .error "argument type without G form"
        else .error "option table unknown"
      | _ => .error "argument without G form"
    | .why _, .why n =>
      match a with
      | .gval g => lowGrund u Γ Λ fn n g
      | _ => .error "argument without G form"
    | .fnptr _, .fnptr m =>
      match a with
      | .fnref f => lowFnRef u Γ Λ m f
      | .var p =>
        match paramPos fn.params p with
        | .error e => .error e
        | .ok j =>
          match lowVar Γ j (.fnptr m) with
          | .error e => .error e
          | .ok x => .ok (Expr.var x)
      | _ => .error "argument without G form"
    | .sum _, .sum cases =>
      match a with
      | .var p =>
        match paramPos fn.params p with
        | .error e => .error e
        | .ok j =>
          match lowVar Γ j (.sum cases) with
          | .error e => .error e
          | .ok x => .ok (Expr.var x)
      | _ => .error "tagged argument without G form"
    | .wert, .prod name fields =>
      match a with
      | .val source => lowWertAtE u Γ Λ fn none (.prod name fields) source
      | _ => .error "aggregate argument without G form"
    | .wert, .arr item count =>
      match a with
      | .val source => lowWertAtE u Γ Λ fn none (.arr item count) source
      | _ => .error "aggregate argument without G form"
    | .wert, .str count =>
      match a with
      | .val source => lowWertAtE u Γ Λ fn none (.str count) source
      | _ => .error "aggregate argument without G form"
    | _, _ => .error "argument type without G form"

/-- The argument list against kinds and recorded types. -/
def lowCallArgsAuxL (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) :
    (ks : List UParamArt) → (ts : List Ty) → (as : List UArg) →
    Except String
      (Args (declOf u) Γ Λ ts)
  | [], ts, as =>
    match ts, as with
    | [], [] => .ok Args.nil
    | _, _ => .error "argument count without G form"
  | k :: ks, ts, as =>
    match ts, as with
    | t :: ts', a :: as' =>
      match lowCallArgOneL u caller Γ fn Λ k t a with
      | .error e => .error e
      | .ok e =>
        match lowCallArgsAuxL u caller Γ fn Λ ks ts' as' with
        | .error e => .error e
        | .ok rest => .ok (Args.cons e rest)
    | _, _ => .error "argument count without G form"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
