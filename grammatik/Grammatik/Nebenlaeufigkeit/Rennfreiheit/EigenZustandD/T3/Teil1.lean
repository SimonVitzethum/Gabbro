module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T2

@[expose] public section



namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik
variable {D : Deklaration}

/-- `next` keeps every table slot (control step, memory-free). -/
theorem next_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {h : l = true}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.next (V := V) (l := l) h)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-! ## 6. Call leaves: `call`/`callInd` through `keinRuf` yield no world.

  The machine fires leaves through `execStmt O passes keinRuf`: the call
  handler is `keinRuf`, which answers every call with
  `.logik (.abstieg f)`. Hence a firing equation `hstep` for a `call` or
  `callInd` leaf reduces to `none = some σ'` -- vacuous. Both lemmas use
  every premise: `hs` to rewrite the statement, `hstep` to close. -/

/-- `call` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem call_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {fn : D.Fn} {args : Args D Γ Λ (D.params fn)}
    {hp : RufPasst D V (D.signatur fn) Λ} {hr : D.gruende fn = 0}
    (s : Stmt D V l Γ Λ (nach D fn Λ))
    (hs : s = Stmt.call (V := V) fn args hp hr)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  have hR : keinRuf (D := D) fn (sg.lese Λ args.orte)
      (evalArgs (sg.lese Λ args.orte) args (sg.lese Λ args.orte) rho) =
      RufAusgang.logik (.abstieg fn) := rfl
  simp only [execStmt] at hstep
  rw [hR] at hstep
  simp only [Ausgang.welt] at hstep
  exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- `callInd` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem callInd_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {hp : RufPasst D V (D.sigNr n) Λ} {hr : (D.sigNr n).gruende = 0}
    (s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ))
    (hs : s = Stmt.callInd (V := V) p args hp hr)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt] at hstep
  revert hstep
  generalize hP : eval (sg.lese Λ (p.orte ++ args.orte)) p
      (sg.lese Λ (p.orte ++ args.orte)) rho = pv
  intro hstep
  cases pv with
  | mk fn hf =>
      simp only at hstep
      have hR : keinRuf (D := D) fn (sg.lese Λ (p.orte ++ args.orte))
          (umsig hf (evalArgs (sg.lese Λ (p.orte ++ args.orte)) args
            (sg.lese Λ (p.orte ++ args.orte)) rho)) =
          RufAusgang.logik (.abstieg fn) := rfl
      rw [hR] at hstep
      simp only [Ausgang.welt] at hstep
      exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-! ## 7. Other-table and degenerate arms: slots of `t` survive writes to `t₂ ≠ t`.

  Each lemma takes the firing equation for ONE constructor form with an
  explicit inequality hypothesis. All premises are used: `hstep` fixes the
  outcome, the inequality selects the `storeSlot_andere`/`schreibBytes_slots_other`
  leg. -/

/-- `assignSlot t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignSlot_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignSlot (V := V) (l := l) t₂ f₂ i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt
      = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignSlot (V := V) (l := l) t₂ f₂ i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `assignDurch t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignDurch_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat}
    {p : Expr D Γ Λ (.ptr n true)} {t₂ : D.Tab} {ht₂ : D.tabNr n = some t₂}
    {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignThru (V := V) (l := l) p t₂ ht₂ f₂ i e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignThru (V := V) (l := l) p t₂ ht₂ f₂ i e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `assignSlotRef t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignSlotRef_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat}
    {r : Expr D Γ Λ (.ref n)} {t₂ : D.Tab} {ht₂ : D.tabNr n = some t₂} {ho : D.offen t₂ = true}
    {f₂ : D.Feld t₂}
    {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignSlotRef (V := V) (l := l) r t₂ ht₂ ho f₂ e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignSlotRef (V := V) (l := l) r t₂ ht₂ ho f₂ e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (r.orte ++ e.orte)).schreibSlot t₂ Λ
        ((eval (σ.lese Λ (r.orte ++ e.orte)) r
          (σ.lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) f₂
        (eval (σ.lese Λ (r.orte ++ e.orte)) e
          (σ.lese Λ (r.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (r.orte ++ e.orte)).schreibSlot t₂ Λ
      ((eval (σ.lese Λ (r.orte ++ e.orte)) r
        (σ.lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) f₂
      (eval (σ.lese Λ (r.orte ++ e.orte)) e
        (σ.lese Λ (r.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (r.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `uebergang t₂` with `t₂ ≠ t` keeps every slot of `t` (failed guard
    yields no world; success writes `t₂`). -/
theorem uebergang_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂} {lo hi : Int}
    {hτ : D.typ t₂ f₂ = .int lo hi}
    {i : Expr D Γ Λ (.index (D.count t₂))} {von nach : Int}
    {hn : lo ≤ nach ∧ nach ≤ hi} {he : D.erlaubt t₂ f₂ von nach = true}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.shift (V := V) (l := l) t₂ f₂ hτ i von nach hn he hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.shift (V := V) (l := l) t₂ f₂ hτ i von nach hn he hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      (if (hτ ▸ (σ.lese Λ (.inl t₂ :: i.orte)).slots t₂
        (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
          (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂ : Zahl _ _).n = von
      then (Ausgang.ok ((σ.lese Λ (.inl t₂ :: i.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
          (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂
        (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ : Ausgang V l Γ)
      else .logik .vorzustand).welt := rfl
  rw [hcomp] at hstep
  by_cases hvon : (hτ ▸ (σ.lese Λ (.inl t₂ :: i.orte)).slots t₂
      (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
        (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂ : Zahl _ _).n = von
  · rw [if_pos hvon, Ausgang.welt] at hstep
    have hσ' : σ' = ((σ.lese Λ (.inl t₂ :: i.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
          (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂
        (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) :=
      Option.some_inj.mp hstep.symm
    rw [hσ']
    have hne : t ≠ t₂ := fun h => ht h.symm
    show ((σ.lese Λ (.inl t₂ :: i.orte)).storeSlot t₂ _ f₂ _).slots t k f =
      σ.slots t k f
    rw [storeSlot_andere _ _ _ _ _ _ hne]
    rfl
  · rw [if_neg hvon, Ausgang.welt] at hstep
    exact absurd hstep (by simp only [reduceCtorEq, not_false_eq_true])

/-- `schreibBytes t₂` with `t₂ ≠ t` keeps every slot of `t` (every fold
    step targets `t₂`). -/
theorem schreibBytes_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂} {hf₂ : D.typ t₂ f₂ = .int 0 255} {n : Nat}
    {lo hi : Int}
    {i : Expr D Γ Λ (.int lo hi)} {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t₂}
    {e : Expr D Γ Λ (.int 0 (256 ^ n - 1))}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.putBytes (V := V) (l := l) t₂ f₂ hf₂ n i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.putBytes (V := V) (l := l) t₂ f₂ hf₂ n i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t₂ f₂ hf₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n
        (zahlZuBytes n
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t₂ f₂ hf₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n
      (zahlZuBytes n
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  exact schreibBytes_slots_other _ _ _ _ _ _ hne _ _ _ _

/-- `schreibBytes t` at `n = 0` keeps every slot of `t` (empty byte list,
    the fold is the identity on top of the `lese` prefix). -/
theorem schreibBytes_null_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t : D.Tab} {f₂ : D.Feld t} {hf₂ : D.typ t f₂ = .int 0 255}
    {lo hi : Int}
    {i : Expr D Γ Λ (.int lo hi)} {hlo : 0 ≤ lo} {hhi : hi + 0 ≤ D.count t}
    {e : Expr D Γ Λ (.int 0 (256 ^ 0 - 1))}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.putBytes (V := V) (l := l) t f₂ hf₂ 0 i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hlen0 : zahlZuBytes 0
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n = [] := by
    have hlen := zahlZuBytes_length 0
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n
    simp only [Int.reducePow, Int.reduceSub, List.length_eq_zero_iff] at hlen
    exact hlen
  have hEq : (execStmt O passes keinRuf
      (Stmt.putBytes (V := V) (l := l) t f₂ hf₂ 0 i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f₂ hf₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n
        (zahlZuBytes 0
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f₂ hf₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n
      (zahlZuBytes 0
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ', hlen0]
  rfl

/-! ## 8. The non-writing oracle arm: `axiomCall` with `aschreibt = false`.

  When the axiom declares no write to `t`, the `GutO` frame keeps every slot
  of `t`: the `lese` prefix keeps slots by `rfl`, the oracle answer by
  `axiomCall_slots_frame` (§3). Failed `einpassen` yields no world. Both `hO`
  (frame) and `hstep` (outcome) are used. -/

/-- `axiomCall a` with `D.aschreibt a t = false` keeps every slot of `t`. -/
theorem axiomCall_nichtschreibt_fest (O : Orakel D) (hO : GutO O) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {h : D.aerg a = none}
    {hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ}
    {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.axiomCall (V := V) a args h hw hg hd hgd)
    (t : D.Tab) (ht : D.aschreibt a t = false)
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  subst hs
  -- Name the oracle answer and split on its result.
  cases hAns : axiomAntwort O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk fst snd =>
      cases snd with
      | some v =>
          have hcomp : (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
              some fst := by
            have hrfl : (execStmt O passes keinRuf
                (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
                (match axiomAntwort O a (σ.lese Λ args.orte)
                  (evalArgs (σ.lese Λ args.orte) args
                    (σ.lese Λ args.orte) ρ) with
                | (sg₂, Option.some w) => (Ausgang.ok sg₂ ρ : Ausgang V l Γ)
                | (_, Option.none) =>
                  (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ)).welt := rfl
            rw [hrfl, hAns, Ausgang.welt]
          rw [hcomp] at hstep
          have hsg' : σ' = fst := Option.some_inj.mp hstep.symm
          rw [hsg']
          have hfst : fst = (O.wirkt a ((σ.lese Λ args.orte).fragt (.inl a))
              (evalArgs (σ.lese Λ args.orte) args
                (σ.lese Λ args.orte) ρ)).1 := by
            have hA := hAns
            simp only [axiomAntwort] at hA
            have hF := congrArg Prod.fst hA
            simp only at hF
            exact hF.symm
          have hlese : ((σ.lese Λ args.orte).fragt (.inl a)).slots t k f = σ.slots t k f := rfl
          rw [hfst]
          have hframe := axiomCall_slots_frame O hO a t ht
            ((σ.lese Λ args.orte).fragt (.inl a))
            (evalArgs (σ.lese Λ args.orte) args
              (σ.lese Λ args.orte) ρ) k f
          rw [hframe, hlese]
      | none =>
          have hcomp : (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
              (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ).welt := by
            have hrfl : (execStmt O passes keinRuf
                (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
                (match axiomAntwort O a (σ.lese Λ args.orte)
                  (evalArgs (σ.lese Λ args.orte) args
                    (σ.lese Λ args.orte) ρ) with
                | (sg₂, Option.some w) => (Ausgang.ok sg₂ ρ : Ausgang V l Γ)
                | (_, Option.none) =>
                  (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ)).welt := rfl
            rw [hrfl, hAns, Ausgang.welt]
          rw [hcomp, Ausgang.welt] at hstep
          simp only [reduceCtorEq] at hstep

/-! ## 9. The leaf dispatch: every firing leaf either records `t`, keeps it,
    or is a declared oracle write to `t`.

  `blattSlots_dispatch`: for a fired leaf `s` with recorded list `neu`, one
  of three holds: some recorded event carries `Sum.inl t` (the four writing
  forms, §2); the outcome keeps every slot of `t` (the §4/§7/§8 lemmas);
  or `s` is an `axiomCall a` whose declared writes cover `t`
  (`D.aschreibt a t = true`) -- the open remainder (see CUTS): `GutO` keeps
  the oracle spur unchanged, so no event records the write, yet slots may
  change. Compound statements cannot fire (`istBlatt = false` contradicts
  `hleaf`). Every premise is used: `hleaf` rules compounds out,
  `hstep`/`hneu` feed the arm lemmas, `hO` feeds the oracle arm. -/

end Gabbro.Grammatik.EZD
