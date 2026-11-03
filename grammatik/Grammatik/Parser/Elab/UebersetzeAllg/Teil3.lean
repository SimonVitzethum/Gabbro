module
public import Grammatik.Parser.Elab.Uebersetze.Folds.ConstantBytes

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- `-a`: `Expr.neg`. -/
def LowSide.minusEins {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (-x.range.2, -x.range.1), term := Expr.neg x.term }

/-- Two lowered operands into one lowered result (the first error wins). -/
def lowZwei {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (f : LowSide u Γ Λ → LowSide u Γ Λ → Except String (LowSide u Γ Λ))
    (a b : Except String (LowSide u Γ Λ)) : Except String (LowSide u Γ Λ) :=
  match a with
  | .error e => .error e
  | .ok x =>
    match b with
    | .error e => .error e
    | .ok y => f x y

/-- The table a basis names: a pointer parameter's target, or a
    table (for `old`, where both spellings travel). -/
def lowBasisTab (u : UProg) (fn : UFn) (b : String) :
    Except String (Fin u.tabs.length) :=
  match paramPos fn.params b with
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr ⟨0, ⟨true, _, none⟩, .table num⟩) =>
      if h : num < u.tabs.length then .ok ⟨num, h⟩
      else .error "pointer table unknown"
    | some (.ptr ⟨0, ⟨true, _, some _⟩, .table num⟩) =>
      if h : num < u.tabs.length then .ok ⟨num, h⟩
      else .error "pointer table unknown"
    | _ => .error "place without G form"
  | .error _ =>
    match tabIdx u.tabs b with
    | .ok t => .ok t
    | .error e => .error e

/-- A numeric parameter as a side (positions shift by `sh`,
    see `lowIdx`). -/
def lowParamSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (p : String) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params p with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr _) => .error "pointer as value without G form"
    | some _ =>
      match fn.params[j]? with
      | some (_, .int a b) =>
        match lowVar Γ (sh + j) (.int a b) with
        | .error e => .error e
        | .ok v => .ok { range := (a, b), term := Expr.var v }
      | _ => .error "parameter without G form"
    | none => .error "parameter without G form"

/-- A `durch` term at its recorded range (the `rw` turns the
    goal into the field type, where the constructor fits). -/
def durchTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr (.table num (true, w))))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
    (capTab_some u num h) fh.idx i hL

/-- The owned-access proof bundle (C12): the capability owner resolves to the
    declaration mark `m`, the table declares `m` as its owner, and the guard at
    the held stage is in hand (so the held mark itself follows from `hL`). -/
theorem ownGuard_holds (u : UProg) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (o : Nat) (m : Fin u.marken.length)
    (hm : eignerMarke u o = some m) (he : m ∈ eignerAt u t)
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    (declOf u).ownerNr o = some m ∧ m ∈ (declOf u).eigner t ∧
      Sum.inr (m, (0 : Nat)) ∈ (declOf u).braucht t := by
  have ho : (declOf u).ownerNr o = some m := by rw [ownerNr_eq]; exact hm
  have hg : Sum.inr (m, (0 : Nat)) ∈ (declOf u).braucht t := by
    show Sum.inr (m, 0) ∈ needsAt u t ++ (eignerAt u t).map (fun m => Sum.inr (m, 0))
    exact List.mem_append_right _ (List.mem_map.mpr ⟨m, he, rfl⟩)
  exact ⟨ho, he, hg⟩

/-- An owned `durch` term at its recorded range: the same guarded carrier as
    `durchTerm` through the `own@m` capability, holding the owner mark. -/
def durchOwnTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length)
    (fh : FieldHit u ⟨num, h⟩) (o : Nat) (m : Fin u.marken.length)
    (v : Var Γ (.ptr ⟨0, ⟨true, w, some o⟩, .table num⟩))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hm : eignerMarke u o = some m) (he : m ∈ eignerAt u ⟨num, h⟩)
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  obtain ⟨ho, he', hg⟩ := ownGuard_holds u Λ ⟨num, h⟩ o m hm he hL
  exact Expr.thruOwn (D := declOf u) (Expr.var v) ⟨num, h⟩
    (capTab_some u num h) fh.idx i m 0 ho he' hg hL

/-- An owned `durch` term for a bool field: the same guarded carrier as the
    plain bool `durch`, holding the owner mark. -/
def durchOwnTermB (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length)
    (fh : BoolHit u ⟨num, h⟩) (o : Nat) (m : Fin u.marken.length)
    (v : Var Γ (.ptr ⟨0, ⟨true, w, some o⟩, .table num⟩))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hm : eignerMarke u o = some m) (he : m ∈ eignerAt u ⟨num, h⟩)
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ .bool := by
  rw [← fh.hbool]
  obtain ⟨ho, he', hg⟩ := ownGuard_holds u Λ ⟨num, h⟩ o m hm he hL
  exact Expr.thruOwn (D := declOf u) (Expr.var v) ⟨num, h⟩
    (capTab_some u num h) fh.idx i m 0 ho he' hg hL

/-- A `slot` term at its recorded range. -/
def slotTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.slot (D := declOf u) t fh.idx i hL

/-- An `altSlot` term at its recorded range. -/
def altTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.oldS (D := declOf u) t fh.idx i hL

/-- A slot read through a pointer parameter (positions shift
    by `sh`, see `lowIdx`). -/
def lowDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr (.table num (true, w))) =>
      if h : num < u.tabs.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ (sh + j) (.ptr (.table num (true, w))) with
          | .error e => .error e
          | .ok v =>
            match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok { range := fh.range, term := durchTerm u Γ Λ num w h fh v i hL }
              else .error "access without held guard"
      else .error "pointer table unknown"
    | some (.ptr ⟨0, ⟨true, w, some owner⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match heig : eignerMarke u owner with
          | .none => .error "owned read without a declared owner mark"
          | .some m =>
            match lowVar Γ (sh + j) (.ptr ⟨0, ⟨true, w, some owner⟩, .table num⟩) with
            | .error e => .error e
            | .ok v =>
              match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
              | .error e => .error e
              | .ok i =>
                if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                    Res.von (declOf u) wdd ∈ Λ) then
                  if he : m ∈ eignerAt u ⟨num, h⟩ then
                    .ok { range := fh.range,
                      term := durchOwnTerm u Γ Λ num w h fh owner m v i heig he hL }
                  else .error "owned read without owner guard"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A field read through a reference into an open table, at the field's recorded range. -/
def refTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (h : num < u.tabs.length) (ho : (declOf u).offen ⟨num, h⟩ = true)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ref num))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.slotRef (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) ho fh.idx hL

/-- `r->f`: a field read through a reference local `r` (positions shift by `sh`). -/
def lowRefRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (r fname : String) :
    Except String (LowSide u Γ Λ) :=
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
            match lowVar Γ (sh + j) (.ref num) with
            | .error e => .error e
            | .ok v =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok { range := fh.range, term := refTerm u Γ Λ num h ho fh v hL }
              else .error "access without held guard"
        else .error "reference into a table that is not open"
      else .error "reference table unknown"
    | _ => .error "place without G form"

/-- A slot read at a table (positions shift by `sh`). -/
def lowTabRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok { range := fh.range, term := slotTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

/-- An entry read (`old`) at a resolved table (positions
    shift by `sh`). -/
def lowAltRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match lowBasisTab u fn b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok { range := fh.range, term := altTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

end Gabbro.Grammatik.Parser.UebersetzeAllg
