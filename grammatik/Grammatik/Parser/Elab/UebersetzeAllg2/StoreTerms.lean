module
public import Grammatik.Parser.Elab.UebersetzeAllg
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- A `durch` write at its recorded range. -/
def assignDurchStmt {space : Nat} {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t) (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, none⟩, .table t.val⟩))
    (ht : (declOf u).capTab space t.val = some t)
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

/-- An owned `durch` write at its recorded range: the same guarded store as
    `assignDurchStmt` through the `own@m` capability, holding the owner mark. -/
def assignDurchOwnStmt {space : Nat} {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (fh : FieldHit u t) (o : Nat) (m : Fin u.marken.length)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table t.val⟩))
    (hc : (declOf u).capTab space t.val = some t)
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
  obtain ⟨ho, he', hg⟩ := ownGuard_holds u Λ t o m hm he hL
  exact Stmt.assignThruOwn (D := declOf u) p t hc fh.idx i e2 m 0
    ho he' hg hw hL

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
def assignDurchStmtB {space : Nat} {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (bh : BoolHit u t) (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, none⟩, .table t.val⟩))
    (ht : (declOf u).capTab space t.val = some t)
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

/-- An owned `durch` write into a BOOL field: the same guarded store as
    `assignDurchStmtB` through the `own@m` capability, holding the owner mark. -/
def assignDurchOwnStmtB {space : Nat} {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length)
    (bh : BoolHit u t) (o : Nat) (m : Fin u.marken.length)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table t.val⟩))
    (hc : (declOf u).capTab space t.val = some t)
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
  obtain ⟨ho, he', hg⟩ := ownGuard_holds u Λ t o m hm he hL
  exact Stmt.assignThruOwn (D := declOf u) p t hc bh.idx i e2 m 0
    ho he' hg hw hL

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

/-- An option write through a pointer into an option field, at the field's type `opt n`. -/
def assignDurchStmtO {space : Nat} {read : Bool} {l : Bool} (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabs.length) (oh : OptHit u t)
    (p : Expr (declOf u) Γ Λ (.ptr ⟨space, ⟨read, true, none⟩, .table t.val⟩)) (ht : (declOf u).capTab space t.val = some t)
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

end Gabbro.Grammatik.Parser.UebersetzeAllg2
