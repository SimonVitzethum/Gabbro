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
import Grammatik.Parser.UebersetzeAllg
import Grammatik.Export108

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
    (t : Fin u.tabellen.length) :
    ((declOf u).signatur i).schreibt t =
      writesAt u (fnAt u i) t := by
  show (sigAt u i.val).schreibt t = _
  rw [sigAt_get u i]
  rfl

/-- Body writes through the declaration. -/
theorem vSchreibt_eq (u : UProg) (c : Fin u.fns.length)
    (t : Fin u.tabellen.length) :
    (vertragVon (declOf u) c).schreibt t =
      writesAt u (fnAt u c) t := by
  show (sigAt u c.val).schreibt t = _
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

/-- No lock floor on a signature (the default `none`). -/
theorem sigBoden_none (u : UProg) (i : Fin u.fns.length) :
    ((declOf u).signatur i).boden = none := by
  show (sigAt u i.val).boden = _
  rw [sigAt_get u i]
  rfl

/-- No lock floor on a body contract. -/
theorem vBoden_none (u : UProg) (c : Fin u.fns.length) :
    (vertragVon (declOf u) c).boden = none := by
  show (sigAt u c.val).boden = _
  rw [sigAt_get u c]
  rfl

/-- No error channel anywhere. -/
theorem sigGruende_zero (u : UProg) (i : Fin u.fns.length) :
    (declOf u).gruende i = 0 := by
  show (sigAt u i.val).gruende = _
  rw [sigAt_get u i]
  rfl

/-- The contract result is the recorded range. -/
theorem vErg_eq (u : UProg) (c : Fin u.fns.length) :
    (vertragVon (declOf u) c).erg =
      (fnAt u c).ergebnis.map fun r => .int r.1 r.2 := by
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
  simp

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
    if h1 : lo ≤ s.weit.1 then
      if h2 : s.weit.2 ≤ hi then .ok (Expr.weiter h1 h2 s.term)
      else .error "value outside range"
    else .error "value outside range"

/-- A `durch` write at its recorded range. -/
def assignDurchStmt (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabellen.length)
    (fh : FieldHit u t) (p : Expr (declOf u) Γ Λ (.ptr t.val true))
    (ht : (declOf u).tabNr t.val = some t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V false Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t fh.idx)
    rw [typAt_of u t fh.idx fh.weit fh.hit]
    exact e
  exact Stmt.assignDurch (D := declOf u) p t ht fh.idx i e2 hw hL

/-- A `slot` write at its recorded range. -/
def assignSlotStmt (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (V : Vertrag (declOf u)) (t : Fin u.tabellen.length)
    (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (e : Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2))
    (hw : V.schreibt t = true)
    (hL : ∀ wdd ∈ (declOf u).braucht t,
      Res.von (declOf u) wdd ∈ Λ) :
    Stmt (declOf u) V false Γ Λ Λ := by
  have e2 : Expr (declOf u) Γ Λ ((declOf u).typ t fh.idx) := by
    show Expr (declOf u) Γ Λ (typAt u t fh.idx)
    rw [typAt_of u t fh.idx fh.weit fh.hit]
    exact e
  exact Stmt.assignSlot (D := declOf u) t fh.idx i e2 hw hL

/-- A slot write through a pointer parameter. -/
def lowAssignDurch (u : UProg) (caller : Fin u.fns.length)
    (b fname : String) (ix : UIdx) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller) (resOf u caller)) :=
  match paramPos (fnAt u caller).params b with
  | .error e => .error e
  | .ok j =>
    match (fnAt u caller).parten[j]? with
    | some (.ptr num true) =>
      if h : num < u.tabellen.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar (ctxOf u caller) j (.ptr num true) with
          | .error e => .error e
          | .ok pv =>
            match lowIdx u (ctxOf u caller) (resOf u caller)
                (fnAt u caller) 0 ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              match lowWertAt u (ctxOf u caller) (resOf u caller)
                  (fnAt u caller) fh.weit.1 fh.weit.2 v with
              | .error e => .error e
              | .ok e =>
                if hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                    Res.von (declOf u) wdd ∈ resOf u caller then
                  if hw : writesAt u (fnAt u caller)
                      ⟨num, h⟩ = true then
                    have hwV : (verOf u caller).schreibt
                        ⟨num, h⟩ = true := by
                      show (vertragVon (declOf u) caller).schreibt
                        ⟨num, h⟩ = true
                      rw [vSchreibt_eq u caller ⟨num, h⟩]
                      exact hw
                    .ok (assignDurchStmt u (ctxOf u caller)
                      (resOf u caller) (verOf u caller) ⟨num, h⟩
                      fh (Expr.var pv) (tabNr_some u num h) i e
                      hwV hL)
                  else .error "write without right"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A slot write at a table. -/
def lowAssignTab (u : UProg) (caller : Fin u.fns.length)
    (b fname : String) (ix : UIdx) (v : USide) :
    Except String (Stmt (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller) (resOf u caller)) :=
  match tabIdx u.tabellen b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u (ctxOf u caller) (resOf u caller)
          (fnAt u caller) 0 t ix with
      | .error e => .error e
      | .ok i =>
        match lowWertAt u (ctxOf u caller) (resOf u caller)
            (fnAt u caller) fh.weit.1 fh.weit.2 v with
        | .error e => .error e
        | .ok e =>
          if hL : ∀ wdd ∈ (declOf u).braucht t,
              Res.von (declOf u) wdd ∈ resOf u caller then
            if hw : writesAt u (fnAt u caller) t = true then
              have hwV : (verOf u caller).schreibt t = true := by
                show (vertragVon (declOf u) caller).schreibt t = true
                rw [vSchreibt_eq u caller t]
                exact hw
              .ok (assignSlotStmt u (ctxOf u caller)
                (resOf u caller) (verOf u caller) t fh i e hwV hL)
            else .error "write without right"
          else .error "access without held guard"

/-- An index argument as a `UIdx` (literals and index parameters
    travel; every other side has no argument form). -/
def uIdxOfSide : USide → Except String UIdx
  | .lit n => .ok (.lit n)
  | .param p => .ok (.param p)
  | _ => .error "argument without G form"

/-- One call argument against the callee parameter kind and the
    recorded parameter type (the `tr_arg` of `lean_g.rs`). -/
def lowCallArgOne (u : UProg) (caller : Fin u.fns.length)
    (k : UParamArt) (t : Ty) : UArg →
    Except String
      (Expr (declOf u) (ctxOf u caller) (resOf u caller) t)
  | a =>
    match k, t with
    | .ptr num w, .ptr n w' =>
      match a with
      | .var p =>
        if hN : n = num then
          if hW : w' = w then
            match paramPos (fnAt u caller).params p with
            | .error e => .error e
            | .ok j =>
              match (fnAt u caller).parten[j]? with
              | some (.ptr num2 w2) =>
                if hC : num2 = num then
                  if w2 = w then
                    match lowVar (ctxOf u caller) j
                        (.ptr n w') with
                    | .error e => .error e
                    | .ok x => .ok (Expr.var x)
                  else
                    if h : num < u.tabellen.length then
                      have eP : Expr (declOf u) (ctxOf u caller)
                          (resOf u caller) (.ptr n w') := by
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
              match tabIdx u.tabellen tname with
              | .error e => .error e
              | .ok ft =>
                if hT : ft.val = num then
                  have hTlt : num < u.tabellen.length := by
                    rw [← hT]
                    exact ft.isLt
                  have hE : (⟨num, hTlt⟩ :
                      Fin u.tabellen.length) = ft := by
                    apply Fin.ext
                    show num = ft.val
                    exact hT.symm
                  have ht : (declOf u).tabNr num = some ft := by
                    rw [← hE]
                    exact tabNr_some u num hTlt
                  have eP : Expr (declOf u) (ctxOf u caller)
                      (resOf u caller) (.ptr n w') := by
                    rw [hN, hW]
                    exact Expr.ptrOf (D := declOf u) ft num ht w
                  .ok eP
                else .error "argument of foreign table"
            else .error "argument right without G form"
          else .error "argument type without G form"
        else .error "argument type without G form"
      | .wert _ => .error "value for pointer without G form"
    | .index num, t =>
      match t with
      | .int lo hi =>
        match a with
        | .wert s =>
          if h : num < u.tabellen.length then
            if hLo : lo = 0 then
              if hHi : hi = (declOf u).count ⟨num, h⟩ - 1 then
                match uIdxOfSide s with
                | .error e => .error e
                | .ok ix =>
                  match lowIdx u (ctxOf u caller) (resOf u caller)
                      (fnAt u caller) 0 ⟨num, h⟩ ix with
                  | .error e => .error e
                  | .ok e =>
                    have eI : Expr (declOf u) (ctxOf u caller)
                        (resOf u caller) (.int lo hi) := by
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
      | .wert s =>
        match lowWertAt u (ctxOf u caller) (resOf u caller)
            (fnAt u caller) lo hi s with
        | .error e => .error e
        | .ok e => .ok e
      | _ => .error "argument without G form"
    | _, _ => .error "argument type without G form"

/-- The argument list against kinds and recorded types. -/
def lowCallArgsAux (u : UProg) (caller : Fin u.fns.length) :
    (ks : List UParamArt) → (ts : List Ty) → (as : List UArg) →
    Except String
      (Args (declOf u) (ctxOf u caller) (resOf u caller) ts)
  | [], ts, as =>
    match ts, as with
    | [], [] => .ok Args.nil
    | _, _ => .error "argument count without G form"
  | k :: ks, ts, as =>
    match ts, as with
    | t :: ts', a :: as' =>
      match lowCallArgOne u caller k t a with
      | .error e => .error e
      | .ok e =>
        match lowCallArgsAux u caller ks ts' as' with
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
  exact ⟨[], List.Perm.refl _, by simp⟩

/-- The floors line up (`RufPasst.hb`, both `none`). -/
theorem rufHb_ok (u : UProg) (caller callee : Fin u.fns.length) :
    ∀ c, (vertragVon (declOf u) caller).boden = some c →
      ∃ c', ((declOf u).signatur callee).boden = some c' ∧
        c ≤ c' := fun c hc => by
  rw [vBoden_none u caller] at hc
  simp at hc

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
    simp at h
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
        simp at he
      | inr hm =>
        exact ih hm

/-- A `nach` step back at the held resources. -/
def castNachStmt (u : UProg) (caller callee : Fin u.fns.length)
    (s : Stmt (declOf u) (verOf u caller) false (ctxOf u caller)
      (resOf u caller) (nach (declOf u) callee (resOf u caller))) :
    Stmt (declOf u) (verOf u caller) false (ctxOf u caller)
      (resOf u caller) (resOf u caller) := by
  rw [nach_eq u callee (resOf u caller)] at s
  exact s

/-- A direct call: arguments plus the harvested `RufPasst`
    (`hw` over the write flags, `hh` over the callee held list,
    `hx` over the lock carrier -- vacuous past the exact held
    set, since every floor is `none`). -/
def lowCall (u : UProg) (caller : Fin u.fns.length)
    (cname : String) (args : List UArg) :
    Except String (Stmt (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller) (resOf u caller)) :=
  match fnIdx u.fns cname with
  | .error e => .error e
  | .ok callee =>
    match lowCallArgsAux u caller (fnAt u callee).parten
        ((declOf u).params callee) args with
    | .error e => .error e
    | .ok a =>
      if hW : ∀ t : Fin u.tabellen.length,
          writesAt u (fnAt u callee) t = true →
            writesAt u (fnAt u caller) t = true then
        if hH : ∀ L ∈ ((declOf u).signatur callee).haelt,
            Res.held (D := declOf u) L ∈ resOf u caller then
          if hX : ∀ L ∈ heldLocksD u (resOf u caller),
              L ∈ ((declOf u).signatur callee).haelt then
            have hw : ∀ t, ((declOf u).signatur callee).schreibt t =
                true → (vertragVon (declOf u) caller).schreibt t =
                true := fun t ht => by
              rw [sigSchreibt_eq u callee t] at ht
              rw [vSchreibt_eq u caller t]
              exact hW t ht
            have hx : ∀ L, Res.held (D := declOf u) L ∈
                resOf u caller →
                L ∉ ((declOf u).signatur callee).haelt →
                ∃ c, ((declOf u).signatur callee).boden = some c ∧
                  (declOf u).rang L < c :=
              fun L hL hn =>
                absurd (hX L (heldLocksD_mem u _ L hL)) hn
            have hg : ∀ g, ((declOf u).signatur callee).gschreibt g =
                true → (vertragVon (declOf u) caller).gschreibt g =
                true := by
              intro g _
              cases g
            have hp : RufPasst (declOf u)
                (vertragVon (declOf u) caller)
                ((declOf u).signatur callee)
                (resOf u caller) :=
              { hw := hw, hg := hg, hk := rufHk_ok u callee (resOf u caller), hh := hH, hx := hx, hb := rufHb_ok u caller callee }
            have s : Stmt (declOf u) (verOf u caller) false
                (ctxOf u caller) (resOf u caller)
                (nach (declOf u) callee (resOf u caller)) :=
              Stmt.call (D := declOf u) callee a hp
                (sigGruende_zero u callee)
            .ok (castNachStmt u caller callee s)
          else .error "call under foreign lock without G form"
        else .error "call without held guard"
      else .error "call writes without right"

/-- One body statement. -/
def lowStmt (u : UProg) (caller : Fin u.fns.length) : UStmt →
    Except String (Stmt (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller) (resOf u caller))
  | .assign b f ix v => lowAssignDurch u caller b f ix v
  | .assignTab b f ix v => lowAssignTab u caller b f ix v
  | .call c args => lowCall u caller c args

/-! ## Generic lowering: bodies and program assembly -/

/-- The held resources are the contract end, as a `Perm`. -/
theorem endPerm_ok (u : UProg) (caller : Fin u.fns.length) :
    (resOf u caller).Perm (verOf u caller).ende := by
  show ((heldAt u (fnAt u caller)).map
    (Res.held (D := declOf u))).Perm (verOf u caller).ende
  rw [show (verOf u caller).ende =
    (vertragVon (declOf u) caller).ende from rfl, ende_eq u caller]

/-- The trailing return. -/
def lowEnd (u : UProg) (caller : Fin u.fns.length) : URet →
    Except String (Endblock (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller))
  | .keine =>
    match hE : (fnAt u caller).ergebnis with
    | none =>
      have hV : (verOf u caller).erg = none := by
        show (vertragVon (declOf u) caller).erg = none
        rw [vErg_eq u caller, hE]
        rfl
      have eK : ErgExpr (declOf u) (ctxOf u caller)
          (resOf u caller) (verOf u caller).erg := by
        rw [hV]
        exact ErgExpr.keine
      .ok (Endblock.ret eK (endPerm_ok u caller))
    | some _ => .error "return without value with result"
  | .wert s =>
    match hE : (fnAt u caller).ergebnis with
    | none => .error "return with value without result"
    | some w =>
      match lowWertAt u (ctxOf u caller) (resOf u caller)
          (fnAt u caller) w.1 w.2 s with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) (ctxOf u caller)
            (resOf u caller) (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          show ErgExpr (declOf u) (ctxOf u caller)
            (resOf u caller) (Option.some (.int w.1 w.2))
          exact ErgExpr.wert v
        .ok (Endblock.ret eW (endPerm_ok u caller))

/-- The body: straight-line writes and direct calls, then the
    trailing return. -/
def lowBody (u : UProg) (caller : Fin u.fns.length) :
    List UStmt → URet →
    Except String (Endblock (declOf u) (verOf u caller) false
      (ctxOf u caller) (resOf u caller))
  | [], r => lowEnd u caller r
  | s :: rest, r =>
    match lowStmt u caller s with
    | .error e => .error e
    | .ok st =>
      match lowBody u caller rest r with
      | .error e => .error e
      | .ok e => .ok (Endblock.cons st e)

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
      (resOf u c) (fnAt u c) (fnAt u c).ergebnis
      (fnAt u c).sichert with
  | .error e => .error e
  | .ok e0 =>
    match lowBody u c (fnAt u c).saetze (fnAt u c).rueck with
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
  requires := fun _ => Expr.wahr
  ensures := fun f => E f
  rumpf := fun f => B f

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
      ([.inl (⟨0, by decide⟩ : Fin uExp104.sperren.length)] :
        List ((declOf uExp104).Lock ⊕
          ((declOf uExp104).Marke × Nat))) ∧
    G104_referenz.gD.braucht G104_referenz.GTab.Konto =
      [.inl G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨0, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.sperren.length)] :
        List (declOf uExp104).Lock) ∧
    G104_referenz.gD.haelt G104_referenz.g_einzahlen =
      [G104_referenz.GLock.M] ∧
    ((declOf uExp104).signatur ⟨1, by decide⟩).haelt =
      ([(⟨0, by decide⟩ : Fin uExp104.sperren.length)] :
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
  ["-- 104 -- The reference fixture as a ".toList,
   "real Gabbro program (lane 126).\n".toList,
   "--\n".toList,
   "-- This is ".toList,
   "`grammatik/Grammatik/ReferenzB.lean` ".toList,
   "(`refD`/`refP`) in surface\n".toList,
   "-- syntax: one table `Konto` of 2 slots ".toList,
   "with one `0 .. 100` field, guarded by\n".toList,
   "-- the single lock `M`; `einzahlen` (one ".toList,
   "`0 .. 10` parameter, no result,\n".toList,
   "-- writes the table, ensures the slot ".toList,
   "did not decrease) and `lies` (no\n".toList,
   "-- parameters, one `0 .. 100` result, ".toList,
   "reads, ensures the answer equals the\n".toList,
   "-- slot). Both run under the held lock ".toList,
   "(`requires Held(M)`, the `beispiele/01`\n".toList,
   "-- idiom: the caller's duty, so the ".toList,
   "bodies touch the guarded slot ".toList,
   "directly).\n".toList,
   "-- Not declared `concurrent`: both ".toList,
   "functions hold `M` by signature, and ".toList,
   "the\n".toList,
   "-- start rule N240 (the goal theorem's ".toList,
   "`StartExklusiv`) forbids two threads\n".toList,
   "-- starting in functions that share a ".toList,
   "signature lock. The earlier note: the ".toList,
   "declaration\n".toList,
   "-- (lane 141: the certificate census ".toList,
   "classifies `concurrent` as erased -- ".toList,
   "the\n".toList,
   "-- emitter writes nothing for it -- so ".toList,
   "the declaration passes stage 7 of\n".toList,
   "-- `pruefe-emission.sh`). Threads cannot ".toList,
   "be driven from a C driver anyway, so\n".toList,
   "-- the driver runs both threads one ".toList,
   "after the other -- the sequential\n".toList,
   "-- composition the emitter produces: ".toList,
   "`einzahlen` like thread 1, then `lies`\n".toList,
   "-- like thread 0. That is the observable ".toList,
   "half of the fixture\n".toList,
   "-- (`refB_schreibt`: slot `0 -> 100`).\n".toList,
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
  .bereich (.atom "u32") (.lit 0) (.lit 4294967295) false

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
  | .tPlatz fds => .tPlatz (fds.map normFeldU32)
  | t => t

/-- A function head with bare `u32` normalised (parameters and
    result). -/
def normSigU32 (s : FnSig) : FnSig :=
  { s with params := s.params.map (fun p => (p.1, normTypU32 p.2)), ergebnis := s.ergebnis.map normTypU32 }

/-- Drop `concurrent` items (`nebenT` has no G form). Top
    level only, like `uMembers`: nested modules are refused by
    `uRestFehler` afterwards, loudly. Single recursion, so the
    kernel reduces it (nested-subterm recursion does not). -/
def stripTopNeben : List SItemTief → List SItemTief
  | [] => []
  | .nebenT _ :: rest => stripTopNeben rest
  | it :: rest => it :: stripTopNeben rest

/-- One item with bare `u32` normalised (no module recursion:
    `uMembers` unwraps the single module `elabU` supports). -/
def normU32Item : SItemTief → SItemTief
  | .tabelleT n c a b g parts =>
    .tabelleT n c a b g (parts.map normTabTeilU32)
  | .funktionT s k => .funktionT (normSigU32 s) k
  | it => it

/-- Bare `u32` normalised over a top-level list. -/
def normTopU32 : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => normU32Item it :: normTopU32 rest

/-- The 108 preprocessing: unwrap like `elabU`, strip
    `concurrent`, then normalise bare `u32`, before `elabU`. -/
def pre108 (items : List SItemTief) : List SItemTief :=
  normTopU32 (stripTopNeben (uMembers items))

/-! ## 108 pins: strip, normalise, elaborate, lower -/

-- SRC-BEGIN src108
/-- The real `beispiele/108-disjoint-start-locks.gab` text, one entry per source line (a long
    line cut again after a space). `zaehle-kette.py` compares the
    pieces against the file, byte for byte. WHY PIECES and not one
    literal: `Parser/Lexer.lean`'s `lex_ofList` -- one 2082-byte
    literal costs the kernel tens of gigabytes (O13). -/
def srcZeilen108 : List (List Char) :=
  ["-- 108 -- Two lock-free readers over one ".toList,
   "shared, never-written table.\n".toList,
   "--\n".toList,
   "-- TRANSFER of `StartExklusiv` ".toList,
   "(`RufMaschineG.lean`): the start ".toList,
   "functions of\n".toList,
   "-- distinct threads hold no signature ".toList,
   "lock in common -- and since lane 183\n".toList,
   "-- (`wurzelnB`) they hold NO signature ".toList,
   "lock at all: nobody holds a lock for a\n".toList,
   "-- thread before it starts. This file ".toList,
   "used to show the disjoint shape\n".toList,
   "-- (`read_a` under `Held(L)`, `read_c` ".toList,
   "under `Held(M)`); that shape is now\n".toList,
   "-- refused at both starts (`N303`), and ".toList,
   "the take-inside remedy has no G form\n".toList,
   "-- for value readers (`LG004`: no ".toList,
   "`return` under `locks`). What remains ".toList,
   "is\n".toList,
   "-- the silent side both rules share: two ".toList,
   "readers over one table nobody\n".toList,
   "-- writes -- every rule stays silent ".toList,
   "(`N240`/`N303`: nothing held; `N290`/\n".toList,
   "-- `N291`/`N300`/`N301`: unwritten ".toList,
   "carriers; `W001`: reads overlap ".toList,
   "freely).\n".toList,
   "-- The refused root shape lives in ".toList,
   "`beispiele/gift/967`, the pair side in\n".toList,
   "-- gifts 910-915. The G export of this ".toList,
   "file is pinned in\n".toList,
   "-- ".toList,
   "`grammatik/Grammatik/Export108.lean`.\n".toList,
   "--\n".toList,
   "-- Evidence: the pre-183 program this ".toList,
   "file replaces, kept verbatim as a\n".toList,
   "-- comment. It is refused since lane 183 ".toList,
   "at both starts by `N303`\n".toList,
   "-- (`wurzelnB`: `D.haelt w = []` -- ".toList,
   "nobody holds a lock for a thread before\n".toList,
   "-- it starts), although `N240` stays ".toList,
   "silent on it (disjoint held sets):\n".toList,
   "--   table U count 4 {\n".toList,
   "--       slot { v : u32, }\n".toList,
   "--   }\n".toList,
   "--   lock L protects { T } rank 0 held ".toList,
   "<= 100 ops;\n".toList,
   "--   lock M protects { U } rank 1 held ".toList,
   "<= 100 ops;\n".toList,
   "--   impl fn read_a() -> u32\n".toList,
   "--       requires Held(L)\n".toList,
   "--       effects { reads T.slots }\n".toList,
   "--       costs <= 4 ops\n".toList,
   "--   {\n".toList,
   "--       return T.slots[0].v;\n".toList,
   "--   }\n".toList,
   "--   impl fn read_c() -> u32\n".toList,
   "--       requires Held(M)\n".toList,
   "--       effects { reads U.slots }\n".toList,
   "--       costs <= 4 ops\n".toList,
   "--   {\n".toList,
   "--       return U.slots[0].v;\n".toList,
   "--   }\n".toList,
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
 .zahl 4,
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
 .zahl 4,
 .wort "ops",
 .zeichen "{",
 .wort "return",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "[",
 .zahl 0,
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
 .zahl 4,
 .wort "ops",
 .zeichen "{",
 .wort "return",
 .ident "T",
 .zeichen ".",
 .wort "slots",
 .zeichen "[",
 .zahl 1,
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
def items108 : List SItemTief := [.modulT
   "beispiel::disjoint_start_locks"
   [.tabelleT
      "T"
      (some (.lit 4))
      none
      none
      false
      [.tPlatz
         [{ fname := "v",
            ftyp := .atom "u32",
            pos := none,
            bezug := none,
            wo := none,
            reserviert := false,
            byOps := false }]],
    .funktionT
      { art := "impl",
        name := "read_a",
        params := [],
        ergebnis := some (.atom "u32"),
        fehler := none,
        klauseln := [.wirkung
                       [.liest
                          (.feld (.variable "T") "slots")],
                     .kosten (.lit 4)] }
      (.block
        []
        (some (.ret
           (some (.feld
              (.index
                (.feld (.variable "T") "slots")
                (.lit 0))
              "v"))))),
    .funktionT
      { art := "impl",
        name := "read_c",
        params := [],
        ergebnis := some (.atom "u32"),
        fehler := none,
        klauseln := [.wirkung
                       [.liest
                          (.feld (.variable "T") "slots")],
                     .kosten (.lit 4)] }
      (.block
        []
        (some (.ret
           (some (.feld
              (.index
                (.feld (.variable "T") "slots")
                (.lit 1))
              "v"))))),
    .nebenT [["read_a"], ["read_c"]]]]

theorem parse108 : beqTopTief (parseTopTief toks108) (.ok items108) = true := by
  decide

/-- The elaborated 108 program (`elab108` checks it against
    the elaborator run after `pre108`). -/

def uExp108 : UProg := { tabellen := [{ name := "T", count := 4, felder := [("v", 0, 4294967295)] }], sperren := [], fns := [{ name := "read_a", params := [], parten := [], ergebnis := some (0, 4294967295), held := [], schreibt := [], sichert := [], saetze := [], rueck := .wert (.tab "T" "v" (.lit 0)) }, { name := "read_c", params := [], parten := [], ergebnis := some (0, 4294967295), held := [], schreibt := [], sichert := [], saetze := [], rueck := .wert (.tab "T" "v" (.lit 1)) }] }

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
  4. 108 is done the same way as 104: `pre108` strips
     `concurrent` (`nebenT`) and normalises bare `u32` to its
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
