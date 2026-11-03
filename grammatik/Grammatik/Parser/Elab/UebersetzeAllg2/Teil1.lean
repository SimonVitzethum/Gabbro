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

/-- The held resources of a function body: its held locks and consumed input marks
    (C16: bodies start holding what the signature consumes). -/
def resOf (u : UProg) (c : Fin u.fns.length) : List (Res (declOf u)) :=
  Signatur.anfang (declOf u) ((declOf u).signatur c)

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

/-- The consumed marks travel from `nimmt`. -/
theorem sigKonsumiert_eq (u : UProg) (i : Fin u.fns.length) :
    ((declOf u).signatur i).konsumiert = nimmtAt u (fnAt u i) := by
  show (sigAt u i.val).konsumiert = _
  rw [sigAt_get u i]
  rfl

/-- The produced marks travel from `gibt` (never owners). -/
theorem sigProduziert_eq (u : UProg) (i : Fin u.fns.length) :
    ((declOf u).signatur i).produziert = gibtAt u (fnAt u i) := by
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

/-- A call steps to the canonical call transformer: consumed marks are erased,
    produced marks appended (definitionally `nachSig` of the signature). -/
theorem nach_eq (u : UProg) (i : Fin u.fns.length)
    (L : List (Res (declOf u))) :
    nach (declOf u) i L = nachSig (declOf u) ((declOf u).signatur i) L := rfl

/-- The body context is the declared parameter list. -/
theorem ctxParams_eq (u : UProg) (c : Fin u.fns.length) :
    ctxOf u c = (declOf u).params c := by
  show (fnAt u c).params.map (·.2) = _
  exact (params_eq u c).symm

/-- The held resources are the signature beginning (bodies start holding inputs). -/
theorem anfangRes_eq (u : UProg) (c : Fin u.fns.length) :
    resOf u c =
      Signatur.anfang (declOf u) ((declOf u).signatur c) := rfl

/-- The contract end is held locks plus produced marks (resolved, C16). -/
theorem ende_eq_resolved (u : UProg) (c : Fin u.fns.length) :
    (vertragVon (declOf u) c).ende =
      ((declOf u).haelt c).map (Res.held (D := declOf u)) ++
        ((((declOf u).signatur c).produziert ++
          ((declOf u).signatur c).owner.outputs).map (Res.vonMarke (declOf u))) := by
  show Vertrag.ende (vertragVon (declOf u) c) = _
  unfold Vertrag.ende Vertrag.vonSig
  rfl

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
def assignDurchStmt {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t) (p : Expr (declOf u) Γ Λ (.ptr (.table t.val (read, true))))
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
  exact Stmt.assignThru (D := declOf u) p t (Deklaration.capTab_of ht rfl (by decide)) fh.idx i e2 hw hL

/-- An owned `durch` write at its recorded range: the same guarded store as
    `assignDurchStmt` through the `own@m` capability, holding the owner mark. -/
def assignDurchOwnStmt {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t) (o : Nat) (m : Fin u.marken.length)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨0, ⟨read, true, some o⟩, .table t.val⟩))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2))
    (hm : eignerMarke u o = some m) (he : m ∈ eignerAt u t)
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t fh.idx)
    rw [fh.hint]
    exact e
  obtain ⟨ho, he', hg, hmΛ⟩ := ownGuard_holds u Λ t o m hm he hL
  exact Stmt.assignThruOwn (D := declOf u) p t (capTab_some u t.val t.isLt) fh.idx i e2 m 0
    ho he' hg hmΛ hw hL

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
def assignDurchStmtB {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (bh : BoolHit u t) (p : Expr (declOf u) Γ Λ (.ptr (.table t.val (read, true))))
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
  exact Stmt.assignThru (D := declOf u) p t (Deklaration.capTab_of ht rfl (by decide)) bh.idx i e2 hw hL

/-- An owned `durch` write into a BOOL field: the same guarded store as
    `assignDurchStmtB` through the `own@m` capability, holding the owner mark. -/
def assignDurchOwnStmtB {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (bh : BoolHit u t) (o : Nat) (m : Fin u.marken.length)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨0, ⟨read, true, some o⟩, .table t.val⟩))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ .bool)
    (hm : eignerMarke u o = some m) (he : m ∈ eignerAt u t)
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t bh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t bh.idx)
    rw [bh.hbool]
    exact e
  obtain ⟨ho, he', hg, hmΛ⟩ := ownGuard_holds u Λ t o m hm he hL
  exact Stmt.assignThruOwn (D := declOf u) p t (capTab_some u t.val t.isLt) bh.idx i e2 m 0
    ho he' hg hmΛ hw hL

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
    | some (.ptr ⟨0, ⟨read, true, none⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ j (.ptr (.table num (read, true))) with
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
def assignDurchStmtO {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length) (oh : OptHit u t)
    (p : Expr (declOf u) Γ Λ (.ptr (.table t.val (read, true)))) (ht : (declOf u).tabNr t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t))) (e : Expr (declOf u) Γ Λ (.opt oh.n))
    (hw : V.schreibt t = true) (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V l Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t oh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t oh.idx)
    rw [oh.hopt]
    exact e
  exact Stmt.assignThru (D := declOf u) p t (Deklaration.capTab_of ht rfl (by decide)) oh.idx i e2 hw hL

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
    | some (.ptr ⟨0, ⟨read, true, none⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        match fieldHitO u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok oh =>
          match lowVar Γ j (.ptr (.table num (read, true))) with
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
