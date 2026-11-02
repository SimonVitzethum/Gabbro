module

public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Korpus.Programme.Export108

@[expose] public section



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
  unfold nach nachSig Signatur.inputMarks Signatur.outputMarks
  rw [OwnerFlow.empty_of_empty ((declOf u).signatur i).owner]
  rw [hK, hP]
  change L ++ [] = L
  exact List.append_nil L

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
  unfold Signatur.anfang Signatur.inputMarks
  rw [h1, h2, OwnerFlow.empty_of_empty ((declOf u).signatur c).owner]
  rfl

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

end Gabbro.Grammatik.Parser.UebersetzeAllg2
