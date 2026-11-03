module

public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Korpus.Programme.Export108
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
public import Grammatik.Gen.Erzeuger.Entscheidung

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000

def lowAxKopf (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (cname : String) (args : List UArg) :
    Except String (AxKopf u caller Γ Λ) :=
  match uaxIdx u.axs cname with
  | .error e => .error e
  | .ok a =>
    match lowCallArgsAuxL u caller Γ fn Λ (uaxAt u a).kinds ((declOf u).aparams a) args with
    | .error e => .error e
    | .ok xs =>
      if hw : (List.finRange u.tabs.length).all (fun t => !(declOf u).aschreibt a t || (verOf u caller).schreibt t) then
        if hg : (List.finRange u.globs.length).all (fun g => !(declOf u).agschreibt a g || (verOf u caller).gschreibt g) then
          if hd : (List.finRange u.tabs.length).all (fun t => !(declOf u).aschreibt a t ||
              decide (∀ w ∈ (declOf u).braucht t, Res.von (declOf u) w ∈ Λ)) then
            if hgd : (List.finRange u.globs.length).all (fun g => !(declOf u).agschreibt a g ||
                decide (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ)) then
              .ok ⟨a, xs,
                fun t h => by
                  have := List.all_eq_true.mp hw t (List.mem_finRange t)
                  simp only [h, Bool.not_true, Bool.false_or] at this; exact this,
                fun g h => by
                  have := List.all_eq_true.mp hg g (List.mem_finRange g)
                  simp only [h, Bool.not_true, Bool.false_or] at this; exact this,
                fun t h => by
                  have := List.all_eq_true.mp hd t (List.mem_finRange t)
                  simp only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this; exact this,
                fun g h => by
                  have := List.all_eq_true.mp hgd g (List.mem_finRange g)
                  simp only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this; exact this⟩
            else .error "foreign call without held guard"
          else .error "foreign call without held guard"
        else .error "foreign call writes without right"
      else .error "foreign call writes without right"

/-- The answer of a foreign body, for the statement (none) or the binding (a type). -/
def withAxErg {α : Type} (u : UProg) (a : Fin u.axs.length)
    (Kn : (declOf u).aerg a = none → Except String α)
    (Ks : (τ : Ty) → (declOf u).aerg a = some τ → Except String α) : Except String α :=
  match hE : (declOf u).aerg a with
  | none => Kn hE
  | some τ => Ks τ hE

/-- `f(..);` at a foreign body with no answer: `Stmt.axiomCall`. -/
def axiomStmt {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (k : AxKopf u caller Γ Λ) (h : (declOf u).aerg k.ax = none) :
    Stmt (declOf u) (verOf u caller) l Γ Λ Λ :=
  Stmt.axiomCall (D := declOf u) k.ax k.args h
    k.hw
    k.hg
    k.hd
    k.hgd

/-- A direct call as a statement, stepping to the call transformer (C16). -/
def lowCallL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (cname : String) (args : List UArg) :
    Except String ((Σ Λ' : List (Res (declOf u)), Stmt (declOf u) (verOf u caller) l Γ Λ Λ')) :=
  match lowRufKopf u caller Γ fn Λ cname args with
  | .error e => .error e
  | .ok k =>
    if hr : (declOf u).gruende k.callee = 0 then
      .ok ⟨nach (declOf u) k.callee Λ, Stmt.call (D := declOf u) k.callee k.args k.hp hr⟩
    else .error "call of a function with a reason channel needs `let .. else`"

/-- A write of a static (`Stmt.assignGlob`): only where the function declares `writes X`. -/
def lowAssignGlobL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (n : String) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match globIdx u.globs n with
  | .error e => .error e
  | .ok g =>
    match h : (globAt u g).ty with
    | .int lo hi =>
      match lowWertAt u Γ Λ fn lo hi v with
      | .error e => .error e
      | .ok e =>
        if hw : writesGAt u (fnAt u caller) g = true then
          have hwV : (verOf u caller).gschreibt g = true := by
            show (vertragVon (declOf u) caller).gschreibt g = true
            rw [vGSchreibt_eq u caller g]
            exact hw
          have hg : (declOf u).gtyp g = .int lo hi := by
            show (globAt u g).ty.toTy = _
            rw [h]
            rfl
          have e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp g) := by
            rw [hg]
            exact e
          if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
            .ok (Stmt.assignGlob (D := declOf u) g e2 hwV hd)
          else .error "access without held guard"
        else .error "write without right"
    | .bool => .error "truth value for a number static"
    | .wert _ =>
      match lowWertAtE u Γ Λ fn none ((declOf u).gtyp g) v with
      | .error e => .error e
      | .ok e2 =>
        if hw : writesGAt u (fnAt u caller) g = true then
          have hwV : (verOf u caller).gschreibt g = true := by
            show (vertragVon (declOf u) caller).gschreibt g = true
            rw [vGSchreibt_eq u caller g]
            exact hw
          if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
            .ok (Stmt.assignGlob (D := declOf u) g e2 hwV hd)
          else .error "access without held guard"
        else .error "write without right"

/-- The same for a `bool` static. -/
def lowAssignGlobBL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (n : String) (v : UEns) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match globIdx u.globs n with
  | .error e => .error e
  | .ok g =>
    match h : (globAt u g).ty with
    | .bool =>
      match lowEns u Γ Λ fn none v with
      | .error e => .error e
      | .ok e =>
        if hw : writesGAt u (fnAt u caller) g = true then
          have hwV : (verOf u caller).gschreibt g = true := by
            show (vertragVon (declOf u) caller).gschreibt g = true
            rw [vGSchreibt_eq u caller g]
            exact hw
          have hg : (declOf u).gtyp g = .bool := by
            show (globAt u g).ty.toTy = _
            rw [h]
            rfl
          have e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp g) := by
            rw [hg]
            exact e
          if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
            .ok (Stmt.assignGlob (D := declOf u) g e2 hwV hd)
          else .error "access without held guard"
        else .error "write without right"
    | .int _ _ => .error "number for a bool static"
    | .wert _ => .error "truth value for an aggregate static"

/-- The store of a payload-free atomic (`Stmt.publish` with the empty payload): only where the function
    declares `writes A`. -/
def lowStoreAtomL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (n : String) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match globIdx u.globs n with
  | .error e => .error e
  | .ok g =>
    match h : (globAt u g).ty with
    | .int lo hi =>
      match lowWertAt u Γ Λ fn lo hi v with
      | .error e => .error e
      | .ok e =>
        if hw : writesGAt u (fnAt u caller) g = true then
          have hwV : (verOf u caller).gschreibt g = true := by
            show (vertragVon (declOf u) caller).gschreibt g = true
            rw [vGSchreibt_eq u caller g]
            exact hw
          have hg : (declOf u).gtyp g = .int lo hi := by
            show (globAt u g).ty.toTy = _
            rw [h]
            rfl
          have e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp g) := by
            rw [hg]
            exact e
          if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
            .ok (Stmt.publish (D := declOf u) g e2 ((declOf u).nutzlast g) rfl hwV hd)
          else .error "access without held guard"
        else .error "write without right"
    | .bool => .error "truth value for a number atomic"
    | .wert _ => .error "aggregate atomic without G form"

/-- The same for a `bool` atomic. -/
def lowStoreAtomBL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (n : String) (v : UEns) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match globIdx u.globs n with
  | .error e => .error e
  | .ok g =>
    match h : (globAt u g).ty with
    | .bool =>
      match lowEns u Γ Λ fn none v with
      | .error e => .error e
      | .ok e =>
        if hw : writesGAt u (fnAt u caller) g = true then
          have hwV : (verOf u caller).gschreibt g = true := by
            show (vertragVon (declOf u) caller).gschreibt g = true
            rw [vGSchreibt_eq u caller g]
            exact hw
          have hg : (declOf u).gtyp g = .bool := by
            show (globAt u g).ty.toTy = _
            rw [h]
            rfl
          have e2 : Expr (declOf u) Γ Λ ((declOf u).gtyp g) := by
            rw [hg]
            exact e
          if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
            .ok (Stmt.publish (D := declOf u) g e2 ((declOf u).nutzlast g) rfl hwV hd)
          else .error "access without held guard"
        else .error "write without right"
    | .int _ _ => .error "number for a bool atomic"
    | .wert _ => .error "aggregate atomic without G form"

/-- A write of an aggregate field through a pointer (`p.slots[i].f = v`, `Stmt.assignThru` at the field's type);
    `none` for any other field. -/
def lowAssignDurchW {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b fname : String) (ix : UIdx) (v : USide) :
    Option (Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ)) :=
  match paramPos fn.params b with
  | .error _ => none
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr ⟨0, ⟨read, true, none⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        (fieldHitW u ⟨num, h⟩ fname).map fun fi =>
          match lowVar Γ j (.ptr (.table num (read, true))), lowIdx u Γ Λ fn 0 ⟨num, h⟩ ix,
              lowWertAtE u Γ Λ fn none ((declOf u).typ ⟨num, h⟩ fi) v with
          | .ok pv, .ok i, .ok e =>
            if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ then
              if hw : writesAt u (fnAt u caller) ⟨num, h⟩ = true then
                have hwV : (verOf u caller).schreibt ⟨num, h⟩ = true := by
                  show (vertragVon (declOf u) caller).schreibt ⟨num, h⟩ = true
                  rw [vSchreibt_eq u caller ⟨num, h⟩]
                  exact hw
                .ok (Stmt.assignThru (D := declOf u) (Expr.var pv) ⟨num, h⟩ (capTab_some u num h) fi i e hwV hL)
              else .error "write without right"
            else .error "access without held guard"
          | .error e, _, _ | _, .error e, _ | _, _, .error e => .error e
      else none
    | _ => none

/-- A write of an aggregate field at a table (`T.slots[i].f = v`); `none` for any other field. -/
def lowAssignTabW {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b fname : String) (ix : UIdx) (v : USide) :
    Option (Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ)) :=
  match tabIdx u.tabs b with
  | .error _ => none
  | .ok t =>
    (fieldHitW u t fname).map fun fi =>
      match lowIdx u Γ Λ fn 0 t ix, lowWertAtE u Γ Λ fn none ((declOf u).typ t fi) v with
      | .ok i, .ok e =>
        if hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ then
          if hw : writesAt u (fnAt u caller) t = true then
            have hwV : (verOf u caller).schreibt t = true := by
              show (vertragVon (declOf u) caller).schreibt t = true
              rw [vSchreibt_eq u caller t]
              exact hw
            .ok (Stmt.assignSlot (D := declOf u) t fi i e hwV hL)
          else .error "write without right"
        else .error "access without held guard"
      | .error e, _ | _, .error e => .error e

/-- A write of an option static (`Stmt.assignGlob` at `Ty.opt` of its table's count). -/
def lowAssignGlobOL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (n : String) (o : UOpt) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match globIdx u.globs n with
  | .error e => .error e
  | .ok g =>
    match (globAt u g).optNum with
    | none => .error "option for a static that is no option"
    | some num =>
      if hnum : num < u.tabs.length then
        match lowOpt u Γ Λ fn 0 num hnum o with
        | .error e => .error e
        | .ok e =>
          if h : (declOf u).gtyp g = .opt ((declOf u).count ⟨num, hnum⟩) then
            if hw : writesGAt u (fnAt u caller) g = true then
              have hwV : (verOf u caller).gschreibt g = true := by
                show (vertragVon (declOf u) caller).gschreibt g = true
                rw [vGSchreibt_eq u caller g]
                exact hw
              if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
                .ok (Stmt.assignGlob (D := declOf u) g (h ▸ e) hwV hd)
              else .error "access without held guard"
            else .error "write without right"
          else .error "option of a foreign table"
      else .error "option table unknown"

/-- Assign a local at its actual declared type, including an IEEE accumulator.
    The canonical fitter retains integer widening and rejects incompatible types. -/
def lowSetVarL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (x : String) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match paramPos fn.params x with
  | .error e => .error e
  | .ok j =>
    match fn.params[j]? with
    | some (_, ty) =>
      match lowVar Γ j ty with
      | .error e => .error e
      | .ok var =>
        match lowWertAtE u Γ Λ fn none ty v with
        | .error e => .error e
        | .ok e => .ok (Stmt.assignVar (D := declOf u) var e)
    | _ => .error "assignment to an unknown variable"

/-- The same for a truth value. -/
def lowSetVarBL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (x : String) (v : UEns) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match paramPos fn.params x with
  | .error e => .error e
  | .ok j =>
    match lowVar Γ j .bool with
    | .error e => .error e
    | .ok var =>
      match lowEns u Γ Λ fn none v with
      | .error e => .error e
      | .ok e => .ok (Stmt.assignVar (D := declOf u) var e)

/-- A number as the value of a register: the register is an integer range. -/
def alsRegZahl {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    (g : UReg) → Expr D Γ Λ (.int g.lo g.hi) → Except String (Expr D Γ Λ g.ty)
  | ⟨_, _, _, _, _, _, _, _, _, false⟩, e => .ok e
  | ⟨_, _, _, _, _, _, _, _, _, true⟩, _ => .error "a number written to a truth-valued register"

/-- A truth value as the value of a register: the register is truth-valued. -/
def alsRegBool {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} :
    (g : UReg) → Expr D Γ Λ .bool → Except String (Expr D Γ Λ g.ty)
  | ⟨_, _, _, _, _, _, _, _, _, true⟩, e => .ok e
  | ⟨_, _, _, _, _, _, _, _, _, false⟩, _ => .error "a truth value written to a numeric register"

/-- `d.R = v;` (`Stmt.regWrite`): the value fitted into the register's range, the class writable. -/
def lowRegWriteL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (d r : String) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match regIdx u.regs d r with
  | .error e => .error e
  | .ok g =>
    match lowWertAt u Γ Λ fn (regAt u g).lo (regAt u g).hi v with
    | .error e => .error e
    | .ok e =>
      match alsRegZahl (regAt u g) e with
      | .error e => .error e
      | .ok e =>
        if hk : ((declOf u).rklasse g).schreibbar = true then
          .ok (Stmt.regWrite (D := declOf u) g hk e)
        else .error "register written against its class"

/-- `d.R = p;` at a truth-valued register (`Stmt.regWrite`). -/
def lowRegWriteBL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (d r : String) (v : UEns) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match regIdx u.regs d r with
  | .error e => .error e
  | .ok g =>
    match lowEns u Γ Λ fn none v with
    | .error e => .error e
    | .ok e =>
      match alsRegBool (regAt u g) e with
      | .error e => .error e
      | .ok e =>
        if hk : ((declOf u).rklasse g).schreibbar = true then
          .ok (Stmt.regWrite (D := declOf u) g hk e)
        else .error "register written against its class"

/-- The signature after a call through a pointer of the unit: the canonical call
    transformer of that signature (resolved, C16). -/
theorem nachSigAt_eq (u : UProg) (n : Nat) (L : List (Res (declOf u))) :
    nachSig (declOf u) ((declOf u).sigNr n) L =
      ((((declOf u).sigNr n).inputMarks.foldl
        (fun acc p => acc.erase (Res.vonMarke (declOf u) p)) L) ++
      (((declOf u).sigNr n).outputMarks.map (Res.vonMarke (declOf u))) := by
  unfold nachSig

/-- `RufPasst` against any signature of the unit, decided over the finite carriers. The
    admitted boundary holds the callee's input marks (C16) and an escrow-ready
    owner flow (C12: `ownerReadyB` -- empty flows and resolved borrowing callees). -/
def rufPasstB (u : UProg) (V : Vertrag (declOf u)) (S : Signatur (Fin u.tabs.length) (Fin u.globs.length)
    (Fin u.locks.length) (Fin u.marken.length)) (Λ : List (Res (declOf u))) : Bool :=
  (List.finRange u.tabs.length).all (fun t => !S.schreibt t || V.schreibt t) &&
  (List.finRange u.globs.length).all (fun g => !S.gschreibt g || V.gschreibt g) &&
  S.haelt.all (fun L => decide (Res.held (D := declOf u) L ∈ Λ)) &&
  (List.finRange u.locks.length).all (fun L => !(decide (Res.held (D := declOf u) L ∈ Λ)) ||
    decide (L ∈ S.haelt) || (match S.boden with | some c => decide ((lockAt u L).rank < c) | none => false)) &&
  (match V.boden with
    | none => true
    | some c => match S.boden with | some c' => decide (c ≤ c') | none => false) &&
  decide (Untermulti (S.inputMarks.map (Res.vonMarke (declOf u))) Λ) &&
  ownerReadyB u S

theorem rufPasstB_ok {u : UProg} {V : Vertrag (declOf u)} {S : Signatur (Fin u.tabs.length) (Fin u.globs.length)
    (Fin u.locks.length) (Fin u.marken.length)} {Λ : List (Res (declOf u))} (h : rufPasstB u V S Λ = true) :
    RufPasst (declOf u) V S Λ := by
  unfold rufPasstB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hw, hg⟩, hh⟩, hx⟩, hb⟩, hk⟩, ho⟩ := h
  refine ⟨fun t ht => ?_, fun g ht => ?_, hk, fun L hL => hh L hL, fun L hL hn => ?_, fun c hc => ?_, ownerReadyB_ok u S ho⟩
  · rcases hw t (List.mem_finRange t) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · rcases hg g (List.mem_finRange g) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · rcases hx L (List.mem_finRange L) with (h1 | h1) | h1
    · simp only [decide_eq_false_iff_not] at h1; exact absurd hL h1
    · exact absurd h1 hn
    · revert h1
      cases hS : S.boden with
      | none => intro h1; cases h1
      | some c => intro h1; exact ⟨c, rfl, of_decide_eq_true h1⟩
  · rw [hc] at hb
    revert hb
    cases hS : S.boden with
    | none => intro h1; cases h1
    | some c' => intro h1; exact ⟨c', rfl, of_decide_eq_true h1⟩

/-- The parameter kinds of the signature number `n` of the unit. -/
def sigKinds (u : UProg) (n : Nat) : List UParamArt := (((sigFns u)[n]?).map (·.kinds)).getD []

/-- The head of a call through a pointer of type `fnptr n`: the arguments against `n`'s parameters and the
    harvested `RufPasst` against `n`'s signature (a function the pointer holds conforms to it, `passt`). -/
structure RufKopfN (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u))) (n : Nat) where
  args : Args (declOf u) Γ Λ ((declOf u).sigNr n).params
  hp : RufPasst (declOf u) (verOf u caller) ((declOf u).sigNr n) Λ

def lowRufKopfN (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (n : Nat) (args : List UArg) : Except String (RufKopfN u caller Γ Λ n) :=
  match lowCallArgsAuxL u caller Γ fn Λ (sigKinds u n) ((declOf u).sigNr n).params args with
  | .error e => .error e
  | .ok a =>
    if hp : rufPasstB u (verOf u caller) (sigAt u n) Λ = true then .ok ⟨a, rufPasstB_ok hp⟩
    else .error "call through a pointer against the rights of its type"

/-- The pointer of an indirect call: the local `p` and the signature number of its type. -/
def lowZeigerN (u : UProg) (Γ : Ctx) (fn : UFn) (p : String) : Except String (Σ n : Nat, Var Γ (Ty.fnptr n)) :=
  match paramPos fn.params p with
  | .error e => .error e
  | .ok j =>
    match ((fn.params[j]?).map (·.2) : Option Ty) with
    | some (Ty.fnptr n) =>
      match lowVar Γ j (Ty.fnptr n) with
      | .error e => .error e
      | .ok v => .ok ⟨n, v⟩
    | _ => .error "call through a name that is no function pointer"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
