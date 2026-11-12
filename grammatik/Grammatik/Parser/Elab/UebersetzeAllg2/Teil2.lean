module

public import Grammatik.Parser.Elab.UebersetzeAllg
public import Grammatik.Korpus.Programme.Export108
public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1
public import Grammatik.Parser.Elab.UebersetzeAllg2.CallArguments
public import Grammatik.Gen.Erzeuger.Entscheidung

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
set_option maxRecDepth 100000

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
    | some (.ptr ⟨space, ⟨read, true, none⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok bh =>
          match lowVar Γ j (.ptr ⟨space, ⟨read, true, none⟩, .table num⟩) with
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
                    do
                      let cap ← checkedTableCap u space num h
                      pure (assignDurchStmtB u Γ
                        Λ (verOf u caller) ⟨num, h⟩
                        bh (Expr.var pv) cap.down i e hwV hL)
                  else .error "write without right"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | some (.ptr ⟨space, ⟨read, true, some owner⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok bh =>
          match heig : eignerMarke u owner with
          | .none => .error "owned write without a declared owner mark"
          | .some m =>
            match lowVar Γ j (.ptr ⟨space, ⟨read, true, some owner⟩, .table num⟩) with
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
                    if he : m ∈ eignerAt u ⟨num, h⟩ then
                      if hw : writesAt u (fnAt u caller)
                          ⟨num, h⟩ = true then
                        have hwV : (verOf u caller).schreibt
                            ⟨num, h⟩ = true := by
                          show (vertragVon (declOf u) caller).schreibt
                            ⟨num, h⟩ = true
                          rw [vSchreibt_eq u caller ⟨num, h⟩]
                          exact hw
                        do
                          let cap ← checkedTableCap u space num h
                          pure (assignDurchOwnStmtB u Γ
                            Λ (verOf u caller) ⟨num, h⟩
                            bh owner m (Expr.var pv) cap.down i e heig he hwV hL)
                      else .error "write without right"
                    else .error "owned write without owner guard"
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

/-- The consumed input marks are held at a call (C16): the decided sub-multiset
    check over the callee's input marks. -/
theorem rufHk_ok (u : UProg) (callee : Fin u.fns.length)
    (Λ : List (Res (declOf u)))
    (h : decide (Untermulti (((declOf u).signatur callee).inputMarks.map
      (Res.vonMarke (declOf u))) Λ) = true) :
    Untermulti (((declOf u).signatur callee).inputMarks.map
      (Res.vonMarke (declOf u))) Λ :=
  of_decide_eq_true h

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
  match fnNr u cname with
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
           if hK : decide (Untermulti (((declOf u).signatur callee).inputMarks.map
               (Res.vonMarke (declOf u))) Λ) = true then
            if hO : ownerReadyB u ((declOf u).signatur callee) = true then
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
              .ok { callee := callee, args := a, hp := { hw := hw, hg := hg, hk := rufHk_ok u callee Λ hK, hh := hH, hx := hx, hb := rufHb_ok u caller callee hB, ownerReady := ownerReadyB_ok u _ hO } }
            else .error "call: callee owner flow not escrow-ready"
           else .error "call without held mark"
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

end Gabbro.Grammatik.Parser.UebersetzeAllg2
