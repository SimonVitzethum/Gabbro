/-
  File:      Grammatik/Parser/UebersetzeAllg2.lean
  Subject:   T3 PART 6: generic lowering, second half.

  Lane 162 (`Parser/UebersetzeAllg.lean`) builds `declOf : UProg ->
  Deklaration` with `Fin` carriers and the generic lowering of
  indices, sides and ensures. This file finishes it: statement
  lowering (`UStmt.assign`/`assignTab`/`call` to
  `Stmt.assignDurch`/`assignSlot`/`Stmt.call`), call arguments
  (`var`/`freshPtr`/`wert`), `RufPasst` assembly by harvest, bodies
  and `Endblock`s, program assembly, and `lowerAllg : (u : UProg) ->
  Except String (Programm (declOf u) x List (declOf u).Fn)`.

  Then the 104 pins on the generically lowered program
  (`programmImFragmentG`/`fussOrtGB` by `decide`, data agreement
  with `G104_referenz.gD`), the real-text lexer pin for 104, and one
  theorem chaining all stages for 104.
-/
import Grammatik.Parser.Elab.UebersetzeAllg
import Grammatik.Korpus.Programme.Export108

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-! ## Lowering context of one function -/

/-- The body context of a function: its parameter types. -/
def ctxOf (u : UProg) (c : Fin u.fns.length) : Ctx :=
  (fnAt u c).params.map (·.2)

/-- The held resources of a function body. -/
def resOf (u : UProg) (c : Fin u.fns.length) : List (Res (declOf u)) :=
  (heldAt u (fnAt u c)).map (Res.held (D := declOf u))

/-- The contract of a function body. -/
def verOf (u : UProg) (c : Fin u.fns.length) : Vertrag (declOf u) :=
  vertragVon (declOf u) c

/-! ## Signature bridges: the computed contract meets the U data -/

/-- Callee writes through the declaration. -/
theorem sigSchreibt_eq (u : UProg) (i : Fin u.fns.length)
    (t : Fin u.tabs.length) :
    ((declOf u).signatur i).schreibt t =
      writesAt u (fnAt u i) t := by
  show (sigAt u i.val).schreibt t = _
  rw [sigAt_get u i]
  rfl

/-- Body writes through the declaration. -/
theorem vSchreibt_eq (u : UProg) (c : Fin u.fns.length)
    (t : Fin u.tabs.length) :
    (vertragVon (declOf u) c).schreibt t =
      writesAt u (fnAt u c) t := by
  show (sigAt u c.val).schreibt t = _
  rw [sigAt_get u c]
  rfl

/-- Callee writes of a static through the declaration. -/
theorem sigGSchreibt_eq (u : UProg) (i : Fin u.fns.length) (g : Fin u.globs.length) :
    ((declOf u).signatur i).gschreibt g = writesGAt u (fnAt u i) g := by
  show (sigAt u i.val).gschreibt g = _
  rw [sigAt_get u i]
  rfl

/-- Body writes of a static through the declaration. -/
theorem vGSchreibt_eq (u : UProg) (c : Fin u.fns.length) (g : Fin u.globs.length) :
    (vertragVon (declOf u) c).gschreibt g = writesGAt u (fnAt u c) g := by
  show (sigAt u c.val).gschreibt g = _
  rw [sigAt_get u c]
  rfl

/-- No consumed marks travel. -/
theorem sigKonsumiert_nil (u : UProg) (i : Fin u.fns.length) :
    ((declOf u).signatur i).konsumiert = [] := by
  show (sigAt u i.val).konsumiert = _
  rw [sigAt_get u i]
  rfl

/-- No produced marks travel. -/
theorem sigProduziert_nil (u : UProg) (i : Fin u.fns.length) :
    ((declOf u).signatur i).produziert = [] := by
  show (sigAt u i.val).produziert = _
  rw [sigAt_get u i]
  rfl

/-- The lock floor of a signature is the computed floor of the function. -/
theorem sigBoden_eq (u : UProg) (i : Fin u.fns.length) :
    ((declOf u).signatur i).boden = (fnAt u i).boden := by
  show (sigAt u i.val).boden = _
  rw [sigAt_get u i]
  rfl

/-- The same for a body contract. -/
theorem vBoden_eq (u : UProg) (c : Fin u.fns.length) :
    (vertragVon (declOf u) c).boden = (fnAt u c).boden := by
  show (sigAt u c.val).boden = _
  rw [sigAt_get u c]
  rfl

/-- The number of reasons of a signature is the recorded one. -/
theorem sigGruende_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).gruende i = (fnAt u i).gruende := by
  show (sigAt u i.val).gruende = _
  rw [sigAt_get u i]
  rfl

/-- A unit whose functions have no reason channel has none on any signature. -/
theorem sigGruende_null (u : UProg) (h : ∀ g ∈ u.fns, g.gruende = 0) (i : Fin u.fns.length) :
    (declOf u).gruende i = 0 := by
  rw [sigGruende_eq]
  exact h _ (List.get_mem u.fns i)

/-- The contract result is the recorded type (`bool`, a range, or none). -/
theorem vErg_eq (u : UProg) (c : Fin u.fns.length) :
    (vertragVon (declOf u) c).erg = (fnAt u c).ergTy := by
  show (sigAt u c.val).erg = _
  rw [sigAt_get u c]
  rfl

/-- A call keeps the held resources (both mark lists are empty). -/
theorem nach_eq (u : UProg) (i : Fin u.fns.length)
    (L : List (Res (declOf u))) :
    nach (declOf u) i L = L := by
  have hK := sigKonsumiert_nil u i
  have hP := sigProduziert_nil u i
  unfold nach nachSig
  rw [hK, hP]
  simp only [List.foldl_nil, List.map_nil, List.append_nil]

/-- The body context is the declared parameter list. -/
theorem ctxParams_eq (u : UProg) (c : Fin u.fns.length) :
    ctxOf u c = (declOf u).params c := by
  show (fnAt u c).params.map (·.2) = _
  exact (params_eq u c).symm

/-- The held resources are the signature beginning. -/
theorem anfangRes_eq (u : UProg) (c : Fin u.fns.length) :
    resOf u c =
      Signatur.anfang (declOf u) ((declOf u).signatur c) := by
  have h1 : ((declOf u).signatur c).haelt =
    heldAt u (fnAt u c) := haelt_eq u c
  have h2 : ((declOf u).signatur c).konsumiert = [] :=
    sigKonsumiert_nil u c
  show ((heldAt u (fnAt u c)).map (Res.held (D := declOf u))) = _
  unfold Signatur.anfang
  rw [h1, h2, List.map_nil, List.append_nil]

/-- The held resources are the contract end. -/
theorem endeRes_eq (u : UProg) (c : Fin u.fns.length) :
    resOf u c = (vertragVon (declOf u) c).ende := by
  show ((heldAt u (fnAt u c)).map (Res.held (D := declOf u))) = _
  exact (ende_eq u c).symm

/-- The ensures context through the declaration. -/
theorem ensCtx_eq (u : UProg) (c : Fin u.fns.length) :
    ErgCtx (ctxOf u c) ((verOf u c).erg) =
      ErgCtx ((declOf u).params c) ((declOf u).erg c) := by
  have hP := ctxParams_eq u c
  have hE : (verOf u c).erg = (declOf u).erg c := by
    show (vertragVon (declOf u) c).erg = _
    rw [vErg_eq u c, erg_eq u c]
  rw [hP, hE]

/-! ## Generic lowering: values, writes, calls -/

/-- A value side fitted into a target range (the `fit` of
    `lean_g.rs`: literals, parameters and slot reads widen from
    their recorded range). -/
def lowWertAt (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (lo hi : Int) (v : USide) :
    Except String (Expr (declOf u) Γ Λ (.int lo hi)) :=
  match lowSideVal u Γ Λ fn v with
  | .error e => .error e
  | .ok s =>
    if h1 : lo ≤ s.range.1 then
      if h2 : s.range.2 ≤ hi then .ok (Expr.widen h1 h2 s.term)
      else .error "value outside range"
    else .error "value outside range"

/-- A `durch` write at its recorded range. -/
def assignDurchStmt {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t) (p : Expr (declOf u) Γ Λ (.ptr t.val true))
    (ht : (declOf u).tabNr t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t fh.idx)
    rw [fh.hint]
    exact e
  exact Stmt.assignThru (D := declOf u) p t ht fh.idx i e2 hw hL

/-- A `slot` write at its recorded range. -/
def assignSlotStmt {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t fh.idx)
    rw [fh.hint]
    exact e
  exact Stmt.assignSlot (D := declOf u) t fh.idx i e2 hw hL

/-- A `durch` write into a BOOL field. -/
def assignDurchStmtB {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (bh : BoolHit u t) (p : Expr (declOf u) Γ Λ (.ptr t.val true))
    (ht : (declOf u).tabNr t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ .bool)
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t bh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t bh.idx)
    rw [bh.hbool]
    exact e
  exact Stmt.assignThru (D := declOf u) p t ht bh.idx i e2 hw hL

/-- A `slot` write into a BOOL field. -/
def assignSlotStmtB {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (bh : BoolHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ .bool)
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t bh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t bh.idx)
    rw [bh.hbool]
    exact e
  exact Stmt.assignSlot (D := declOf u) t bh.idx i e2 hw hL

/-- A slot write through a pointer parameter. -/
def lowAssignDurchL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (b fname : String) (ix : UIdx) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l
      Γ Λ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num true) =>
      if h : num < u.tabs.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ j (.ptr num true) with
          | .error e => .error e
          | .ok pv =>
            match lowIdx u Γ Λ
                fn 0 ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              match lowWertAt u Γ Λ
                  fn fh.range.1 fh.range.2 v with
              | .error e => .error e
              | .ok e =>
                if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                    Res.von (declOf u) wdd ∈ Λ then
                  if hw : writesAt u (fnAt u caller)
                      ⟨num, h⟩ = true then
                    have hwV : (verOf u caller).schreibt
                        ⟨num, h⟩ = true := by
                      show (vertragVon (declOf u) caller).schreibt
                        ⟨num, h⟩ = true
                      rw [vSchreibt_eq u caller ⟨num, h⟩]
                      exact hw
                    .ok (assignDurchStmt u Γ
                      Λ (verOf u caller) ⟨num, h⟩
                      fh (Expr.var pv) (tabNr_some u num h) i e
                      hwV hL)
                  else .error "write without right"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A write through a reference into an open table at the field's recorded range (`Stmt.assignSlotRef`). -/
def assignRefStmt {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (num : Nat) (h : num < u.tabs.length) (ho : (declOf u).offen ⟨num, h⟩ = true)
    (fh : FieldHit u ⟨num, h⟩) (r : Expr (declOf u) Γ Λ (.ref num))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hw : V.schreibt ⟨num, h⟩ = true)
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ ⟨num, h⟩ fh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u ⟨num, h⟩ fh.idx)
    rw [fh.hint]
    exact e
  exact Stmt.assignSlotRef (D := declOf u) r ⟨num, h⟩ (tabNr_some u num h) ho fh.idx e2 hw hL

/-- `r->f = v;` through a reference local `r`. -/
def lowAssignRefL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (r fname : String) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match paramPos fn.params r with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ref num) =>
      if h : num < u.tabs.length then
        if ho : (declOf u).offen ⟨num, h⟩ = true then
          match fieldHit u ⟨num, h⟩ fname with
          | .error e => .error e
          | .ok fh =>
            match lowVar Γ j (.ref num) with
            | .error e => .error e
            | .ok rv =>
              match lowWertAt u Γ Λ fn fh.range.1 fh.range.2 v with
              | .error e => .error e
              | .ok e =>
                if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ then
                  if hw : writesAt u (fnAt u caller) ⟨num, h⟩ = true then
                    have hwV : (verOf u caller).schreibt ⟨num, h⟩ = true := by
                      show (vertragVon (declOf u) caller).schreibt ⟨num, h⟩ = true
                      rw [vSchreibt_eq u caller ⟨num, h⟩]
                      exact hw
                    .ok (assignRefStmt u Γ Λ (verOf u caller) num h ho fh (Expr.var rv) e hwV hL)
                  else .error "write without right"
                else .error "access without held guard"
        else .error "reference into a table that is not open"
      else .error "reference table unknown"
    | _ => .error "place without G form"

/-- A slot write at a table. -/
def lowAssignTabL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (b fname : String) (ix : UIdx) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l
      Γ Λ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ
          fn 0 t ix with
      | .error e => .error e
      | .ok i =>
        match lowWertAt u Γ Λ
            fn fh.range.1 fh.range.2 v with
        | .error e => .error e
        | .ok e =>
          if hL : ∀ wdd ∈ (declOf u).braucht t,
              Res.von (declOf u) wdd ∈ Λ then
            if hw : writesAt u (fnAt u caller) t = true then
              have hwV : (verOf u caller).schreibt t = true := by
                show (vertragVon (declOf u) caller).schreibt t = true
                rw [vSchreibt_eq u caller t]
                exact hw
              .ok (assignSlotStmt u Γ
                Λ (verOf u caller) t fh i e hwV hL)
            else .error "write without right"
          else .error "access without held guard"

/-- An option write through a pointer into an option field, at the field's type `opt n`. -/
def assignDurchStmtO {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length) (oh : OptHit u t)
    (p : Expr (declOf u) Γ Λ (.ptr t.val true)) (ht : (declOf u).tabNr t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t))) (e : Expr (declOf u) Γ Λ (.opt oh.n))
    (hw : V.schreibt t = true) (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t oh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t oh.idx)
    rw [oh.hopt]
    exact e
  exact Stmt.assignThru (D := declOf u) p t ht oh.idx i e2 hw hL

/-- An option write at a table into an option field. -/
def assignSlotStmtO {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length) (oh : OptHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t))) (e : Expr (declOf u) Γ Λ (.opt oh.n))
    (hw : V.schreibt t = true) (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t oh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t oh.idx)
    rw [oh.hopt]
    exact e
  exact Stmt.assignSlot (D := declOf u) t oh.idx i e2 hw hL

/-- An option value written through a pointer parameter into an option field. -/
def lowAssignDurchOL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b fname : String) (ix : UIdx) (v : UOpt) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num true) =>
      if h : num < u.tabs.length then
        match fieldHitO u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok oh =>
          match lowVar Γ j (.ptr num true) with
          | .error e => .error e
          | .ok pv =>
            match lowIdx u Γ Λ fn 0 ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              match lowOpt u Γ Λ fn 0 oh.tnum oh.hlt v with
              | .error e => .error e
              | .ok e0 =>
                have e : Expr (declOf u) Γ Λ (.opt oh.n) := by rw [← oh.hcnt]; exact e0
                if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ then
                  if hw : writesAt u (fnAt u caller) ⟨num, h⟩ = true then
                    have hwV : (verOf u caller).schreibt ⟨num, h⟩ = true := by
                      show (vertragVon (declOf u) caller).schreibt ⟨num, h⟩ = true
                      rw [vSchreibt_eq u caller ⟨num, h⟩]
                      exact hw
                    .ok (assignDurchStmtO u Γ Λ (verOf u caller) ⟨num, h⟩ oh (Expr.var pv) (tabNr_some u num h) i e hwV hL)
                  else .error "write without right"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- An option value written at a table into an option field. -/
def lowAssignTabOL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (b fname : String) (ix : UIdx) (v : UOpt) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHitO u t fname with
    | .error e => .error e
    | .ok oh =>
      match lowIdx u Γ Λ fn 0 t ix with
      | .error e => .error e
      | .ok i =>
        match lowOpt u Γ Λ fn 0 oh.tnum oh.hlt v with
        | .error e => .error e
        | .ok e0 =>
          have e : Expr (declOf u) Γ Λ (.opt oh.n) := by rw [← oh.hcnt]; exact e0
          if hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ then
            if hw : writesAt u (fnAt u caller) t = true then
              have hwV : (verOf u caller).schreibt t = true := by
                show (vertragVon (declOf u) caller).schreibt t = true
                rw [vSchreibt_eq u caller t]
                exact hw
              .ok (assignSlotStmtO u Γ Λ (verOf u caller) t oh i e hwV hL)
            else .error "write without right"
          else .error "access without held guard"

/-- A truth value written through a pointer parameter into a bool field. -/
def lowAssignDurchBL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (b fname : String) (ix : UIdx) (v : UEns) :
    Except String (Stmt (declOf u) (verOf u caller) l
      Γ Λ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num true) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok bh =>
          match lowVar Γ j (.ptr num true) with
          | .error e => .error e
          | .ok pv =>
            match lowIdx u Γ Λ
                fn 0 ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              match lowEns u Γ Λ
                  fn none v with
              | .error e => .error e
              | .ok e =>
                if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                    Res.von (declOf u) wdd ∈ Λ then
                  if hw : writesAt u (fnAt u caller)
                      ⟨num, h⟩ = true then
                    have hwV : (verOf u caller).schreibt
                        ⟨num, h⟩ = true := by
                      show (vertragVon (declOf u) caller).schreibt
                        ⟨num, h⟩ = true
                      rw [vSchreibt_eq u caller ⟨num, h⟩]
                      exact hw
                    .ok (assignDurchStmtB u Γ
                      Λ (verOf u caller) ⟨num, h⟩
                      bh (Expr.var pv) (tabNr_some u num h) i e
                      hwV hL)
                  else .error "write without right"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A truth value written at a table into a bool field. -/
def lowAssignTabBL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (b fname : String) (ix : UIdx) (v : UEns) :
    Except String (Stmt (declOf u) (verOf u caller) l
      Γ Λ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHitB u t fname with
    | .error e => .error e
    | .ok bh =>
      match lowIdx u Γ Λ
          fn 0 t ix with
      | .error e => .error e
      | .ok i =>
        match lowEns u Γ Λ
            fn none v with
        | .error e => .error e
        | .ok e =>
          if hL : ∀ wdd ∈ (declOf u).braucht t,
              Res.von (declOf u) wdd ∈ Λ then
            if hw : writesAt u (fnAt u caller) t = true then
              have hwV : (verOf u caller).schreibt t = true := by
                show (vertragVon (declOf u) caller).schreibt t = true
                rw [vSchreibt_eq u caller t]
                exact hw
              .ok (assignSlotStmtB u Γ
                Λ (verOf u caller) t bh i e hwV hL)
            else .error "write without right"
          else .error "access without held guard"

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
    recorded parameter type (the `tr_arg` of `lean_g.rs`). -/
def lowCallArgOneL (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (k : UParamArt) (t : Ty) : UArg →
    Except String
      (Expr (declOf u) Γ Λ t)
  | a =>
    match k, t with
    | .ptr num w, .ptr n w' =>
      match a with
      | .var p =>
        if hN : n = num then
          if hW : w' = w then
            match paramPos fn.params p with
            | .error e => .error e
            | .ok j =>
              match fn.kinds[j]? with
              | some (.ptr num2 w2) =>
                if hC : num2 = num then
                  if w2 = w then
                    match lowVar Γ j
                        (.ptr n w') with
                    | .error e => .error e
                    | .ok x => .ok (Expr.var x)
                  else
                    if h : num < u.tabs.length then
                      have eP : Expr (declOf u) Γ
                          Λ (.ptr n w') := by
                        rw [hN, hW]
                        exact Expr.ptrOf (D := declOf u) ⟨num, h⟩
                          num (tabNr_some u num h) w
                      .ok eP
                    else .error "pointer table unknown"
                else .error "argument of foreign table"
              | _ => .error "pointer argument without G form"
          else .error "argument type without G form"
        else .error "argument type without G form"
      | .freshPtr tname w2 =>
        if hN : n = num then
          if hW : w' = w then
            if hW2 : w2 = w then
              match tabIdx u.tabs tname with
              | .error e => .error e
              | .ok ft =>
                if hT : ft.val = num then
                  have hTlt : num < u.tabs.length := by
                    rw [← hT]
                    exact ft.isLt
                  have hE : (⟨num, hTlt⟩ :
                      Fin u.tabs.length) = ft := by
                    apply Fin.ext
                    show num = ft.val
                    exact hT.symm
                  have ht : (declOf u).tabNr num = some ft := by
                    rw [← hE]
                    exact tabNr_some u num hTlt
                  have eP : Expr (declOf u) Γ
                      Λ (.ptr n w') := by
                    rw [hN, hW]
                    exact Expr.ptrOf (D := declOf u) ft num ht w
                  .ok eP
                else .error "argument of foreign table"
            else .error "argument right without G form"
          else .error "argument type without G form"
        else .error "argument type without G form"
      | .val _ | .bval _ | .oval _ | .gval _ | .fnref _ => .error "value for pointer without G form"
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
      | .fnref f =>
        match fnIdx u.fns f with
        | .error e => .error e
        | .ok g =>
          if h : (declOf u).passt g m = true then .ok (Expr.fnref (D := declOf u) g m h)
          else .error "function does not conform to the pointer type"
      | .var p =>
        match paramPos fn.params p with
        | .error e => .error e
        | .ok j =>
          match lowVar Γ j (.fnptr m) with
          | .error e => .error e
          | .ok x => .ok (Expr.var x)
      | _ => .error "argument without G form"
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

/-- No consumed marks at a call (`RufPasst.hk`). -/
theorem rufHk_ok (u : UProg) (callee : Fin u.fns.length)
    (Λ : List (Res (declOf u))) :
    Untermulti (((declOf u).signatur callee).konsumiert.map
      (Res.vonMarke (declOf u))) Λ := by
  rw [sigKonsumiert_nil u callee]
  show Untermulti ([] : List (Res (declOf u))) Λ
  exact ⟨[], List.Perm.refl _, by simp only [List.nil_sublist]⟩

/-- The caller's floor is at most the callee's (the Bool the lowering decides). -/
def floorLeB (u : UProg) (caller callee : Fin u.fns.length) : Bool :=
  match (fnAt u caller).boden, (fnAt u callee).boden with
  | none, _ => true
  | some _, none => false
  | some c, some c' => decide (c ≤ c')

/-- The floors line up (`RufPasst.hb`). -/
theorem rufHb_ok (u : UProg) (caller callee : Fin u.fns.length)
    (h : floorLeB u caller callee = true) :
    ∀ c, (vertragVon (declOf u) caller).boden = some c →
      ∃ c', ((declOf u).signatur callee).boden = some c' ∧
        c ≤ c' := fun c hc => by
  rw [vBoden_eq u caller] at hc
  rw [sigBoden_eq u callee]
  unfold floorLeB at h
  rw [hc] at h
  cases hb : (fnAt u callee).boden with
  | none => rw [hb] at h; simp only [Bool.false_eq_true] at h
  | some c' =>
    rw [hb] at h
    exact ⟨c', rfl, of_decide_eq_true h⟩

/-- An extra held lock ranks below the callee's floor (the Bool the lowering decides). -/
def floorUeberB (u : UProg) (callee : Fin u.fns.length) (L : (declOf u).Lock) : Bool :=
  match (fnAt u callee).boden with
  | some c => decide ((declOf u).rang L < c)
  | none => false

/-- The held locks named in a resource list, at the
    declaration lock type (so membership synthesizes). -/
def heldLocksD (u : UProg) : List (Res (declOf u)) →
    List (declOf u).Lock
  | [] => []
  | .held L :: rest => L :: heldLocksD u rest
  | .marke _ _ :: rest => heldLocksD u rest

/-- A held resource names its lock in the projection. -/
theorem heldLocksD_mem (u : UProg) (Λ : List (Res (declOf u)))
    (L : (declOf u).Lock)
    (h : Res.held (D := declOf u) L ∈ Λ) :
    L ∈ heldLocksD u Λ := by
  induction Λ with
  | nil =>
    simp only [List.not_mem_nil] at h
  | cons w rest ih =>
    cases w with
    | held M =>
      show L ∈ M :: heldLocksD u rest
      simp only [List.mem_cons] at h ⊢
      cases h with
      | inl he =>
        simp only [Res.held.injEq] at he
        subst he
        exact Or.inl rfl
      | inr hm =>
        exact Or.inr (ih hm)
    | marke m s =>
      show L ∈ heldLocksD u rest
      simp only [List.mem_cons] at h
      cases h with
      | inl he =>
        simp only [reduceCtorEq] at he
      | inr hm =>
        exact ih hm

/-- A `nach` step back at the held resources. -/
def castNachStmtL {l : Bool} (u : UProg) (caller callee : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u)))
    (s : Stmt (declOf u) (verOf u caller) l Γ
      Λ (nach (declOf u) callee Λ)) :
    Stmt (declOf u) (verOf u caller) l Γ
      Λ Λ := by
  rw [nach_eq u callee Λ] at s
  exact s

/-- The head of a direct call: the callee, its arguments and the harvested `RufPasst` (`hw` over the write
    flags, `hh` over the callee held list, `hx` over the lock carrier -- vacuous past the exact held set,
    since every floor is `none`). The statement `Stmt.call` and the binding `Block.bindCall` share it. -/
structure RufKopf (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  callee : Fin u.fns.length
  args : Args (declOf u) Γ Λ ((declOf u).params callee)
  hp : RufPasst (declOf u) (verOf u caller) ((declOf u).signatur callee) Λ

def lowRufKopf (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (cname : String) (args : List UArg) :
    Except String (RufKopf u caller Γ Λ) :=
  match fnIdx u.fns cname with
  | .error e => .error e
  | .ok callee =>
    match lowCallArgsAuxL u caller Γ fn Λ (fnAt u callee).kinds
        ((declOf u).params callee) args with
    | .error e => .error e
    | .ok a =>
      if hW : ∀ t : Fin u.tabs.length,
          writesAt u (fnAt u callee) t = true →
            writesAt u (fnAt u caller) t = true then
       if hG : ∀ g : Fin u.globs.length,
          writesGAt u (fnAt u callee) g = true →
            writesGAt u (fnAt u caller) g = true then
        if hH : ∀ L ∈ ((declOf u).signatur callee).haelt,
            Res.held (D := declOf u) L ∈ Λ then
         if hB : floorLeB u caller callee = true then
          if hX : ∀ L ∈ heldLocksD u Λ,
              L ∈ ((declOf u).signatur callee).haelt ∨ floorUeberB u callee L = true then
            have hw : ∀ t, ((declOf u).signatur callee).schreibt t =
                true → (vertragVon (declOf u) caller).schreibt t =
                true := fun t ht => by
              rw [sigSchreibt_eq u callee t] at ht
              rw [vSchreibt_eq u caller t]
              exact hW t ht
            have hx : ∀ L, Res.held (D := declOf u) L ∈
                Λ →
                L ∉ ((declOf u).signatur callee).haelt →
                ∃ c, ((declOf u).signatur callee).boden = some c ∧
                  (declOf u).rang L < c :=
              fun L hL hn => by
                rcases hX L (heldLocksD_mem u _ L hL) with h | h
                · exact absurd h hn
                · rw [sigBoden_eq u callee]
                  unfold floorUeberB at h
                  cases hf : (fnAt u callee).boden with
                  | none => rw [hf] at h; simp only [Bool.false_eq_true] at h
                  | some c =>
                    rw [hf] at h
                    exact ⟨c, rfl, of_decide_eq_true h⟩
            have hg : ∀ g, ((declOf u).signatur callee).gschreibt g =
                true → (vertragVon (declOf u) caller).gschreibt g =
                true := fun g hg0 => by
              rw [sigGSchreibt_eq u callee g] at hg0
              rw [vGSchreibt_eq u caller g]
              exact hG g hg0
            .ok { callee := callee, args := a,
                  hp := { hw := hw, hg := hg, hk := rufHk_ok u callee Λ, hh := hH, hx := hx,
                          hb := rufHb_ok u caller callee hB } }
          else .error "call: a held lock does not rank below the callee's floor"
         else .error "call: the caller's lock floor is above the callee's"
        else .error "call without held guard"
       else .error "call writes without right"
      else .error "call writes without right"

/-- The head of a call of a foreign body: the axiom, its arguments, and the four write premises of
    `axiomCall`/`bindAxiom`: what it writes the caller may write, under the guards it holds. -/
structure AxKopf (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  ax : Fin u.axs.length
  args : Args (declOf u) Γ Λ ((declOf u).aparams ax)
  hw : ∀ t, (declOf u).aschreibt ax t = true → (verOf u caller).schreibt t = true
  hg : ∀ g, (declOf u).agschreibt ax g = true → (verOf u caller).gschreibt g = true
  hd : ∀ t, (declOf u).aschreibt ax t = true → darf (declOf u) t Λ
  hgd : ∀ g, (declOf u).agschreibt ax g = true → gdarf (declOf u) g Λ

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

/-- A direct call as a statement. -/
def lowCallL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u)))
    (cname : String) (args : List UArg) :
    Except String (Stmt (declOf u) (verOf u caller) l
      Γ Λ Λ) :=
  match lowRufKopf u caller Γ fn Λ cname args with
  | .error e => .error e
  | .ok k =>
    if hr : (declOf u).gruende k.callee = 0 then
      .ok (castNachStmtL u caller k.callee Γ Λ (Stmt.call (D := declOf u) k.callee k.args k.hp hr))
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
    | some (.ptr num true) =>
      if h : num < u.tabs.length then
        (fieldHitW u ⟨num, h⟩ fname).map fun fi =>
          match lowVar Γ j (.ptr num true), lowIdx u Γ Λ fn 0 ⟨num, h⟩ ix,
              lowWertAtE u Γ Λ fn none ((declOf u).typ ⟨num, h⟩ fi) v with
          | .ok pv, .ok i, .ok e =>
            if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ then
              if hw : writesAt u (fnAt u caller) ⟨num, h⟩ = true then
                have hwV : (verOf u caller).schreibt ⟨num, h⟩ = true := by
                  show (vertragVon (declOf u) caller).schreibt ⟨num, h⟩ = true
                  rw [vSchreibt_eq u caller ⟨num, h⟩]
                  exact hw
                .ok (Stmt.assignThru (D := declOf u) (Expr.var pv) ⟨num, h⟩ (tabNr_some u num h) fi i e hwV hL)
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

/-- `x = v;` at a `let mut` number: `Stmt.assignVar`, the value fitted into the variable's range. -/
def lowSetVarL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (x : String) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match paramPos fn.params x with
  | .error e => .error e
  | .ok j =>
    match fn.params[j]? with
    | some (_, .int lo hi) =>
      match lowVar Γ j (.int lo hi) with
      | .error e => .error e
      | .ok var =>
        match lowWertAt u Γ Λ fn lo hi v with
        | .error e => .error e
        | .ok e => .ok (Stmt.assignVar (D := declOf u) var e)
    | _ => .error "assignment to a non-number variable"

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

/-- The signature after a call through a pointer of the unit: the held set stays (no marks). -/
theorem nachSigAt_eq (u : UProg) (n : Nat) (L : List (Res (declOf u))) :
    nachSig (declOf u) ((declOf u).sigNr n) L = L := by
  show nachSig (declOf u) (sigAt u n) L = L
  unfold sigAt
  split <;> exact List.append_nil L

/-- `RufPasst` against any signature of the unit, decided over the finite carriers. -/
def rufPasstB (u : UProg) (V : Vertrag (declOf u)) (S : Signatur (Fin u.tabs.length) (Fin u.globs.length)
    (Fin u.locks.length) Empty) (Λ : List (Res (declOf u))) : Bool :=
  (List.finRange u.tabs.length).all (fun t => !S.schreibt t || V.schreibt t) &&
  (List.finRange u.globs.length).all (fun g => !S.gschreibt g || V.gschreibt g) &&
  S.haelt.all (fun L => decide (Res.held (D := declOf u) L ∈ Λ)) &&
  (List.finRange u.locks.length).all (fun L => !(decide (Res.held (D := declOf u) L ∈ Λ)) ||
    decide (L ∈ S.haelt) || (match S.boden with | some c => decide ((lockAt u L).rank < c) | none => false)) &&
  (match V.boden with
    | none => true
    | some c => match S.boden with | some c' => decide (c ≤ c') | none => false)

theorem rufPasstB_ok {u : UProg} {V : Vertrag (declOf u)} {S : Signatur (Fin u.tabs.length) (Fin u.globs.length)
    (Fin u.locks.length) Empty} {Λ : List (Res (declOf u))} (h : rufPasstB u V S Λ = true) :
    RufPasst (declOf u) V S Λ := by
  unfold rufPasstB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hw, hg⟩, hh⟩, hx⟩, hb⟩ := h
  refine ⟨fun t ht => ?_, fun g ht => ?_, ?_, fun L hL => hh L hL, fun L hL hn => ?_, fun c hc => ?_⟩
  · rcases hw t (List.mem_finRange t) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · rcases hg g (List.mem_finRange g) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · have : S.konsumiert = [] := by
      cases hk : S.konsumiert with
      | nil => rfl
      | cons m _ => exact m.1.elim
    rw [this]; exact ⟨[], List.Perm.refl _, by simp only [List.nil_sublist]⟩
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
  | .bind .. | .bindB .. | .bindMut .. | .bindCall .. | .axCall .. | .bindAx .. | .narrowBeg .. | .retryBeg .. | .foreverBeg .. | .bindOpt .. | .matchBeg .. | .startS | .allocBeg .. | .bindElse .. | .matchWhyBeg .. | .bindSum .. | .matchTagBeg .. | .bindAxElse .. | .ifBeg _ | .ifElse | .loopBeg .. | .regRead .. | .regReadElse .. | .awaitBind .. | .bindFnref .. | .bindCallInd .. | .bindW .. | .tausch .. | .ifEnde .. =>
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
