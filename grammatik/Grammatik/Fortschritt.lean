/-
  Gabbro/Grammatik/Fortschritt.lean

  **Progress up to named stops** (`Zielsatz.FortschrittG`, SATZKARTE §19.2).

  On every reachable machine of G, every thread is finished, waits for a
  lock another thread holds, stands at a named stop of one of three kinds
  (`Zielsatz.HaltBenannt`: `flagge`, a wait for a publication; `budget`, a
  spent `forever` budget; `hardware`, an axiom or register answer outside
  its declaration -- since 2026-09-15, verdict F3), or can step. The proof is a case analysis over
  every head shape of a frame residue against the rules of G
  (`RufMaschineG.lean`): at each shape either some rule fires (the `w_*`
  step builders of `RufAdaequatG.lean`/`RufAdaequatRufG.lean`) or one of
  the stops (finished, waiting, a named stop) applies.

  Three shapes had no rule and no stop, and are excluded by an invariant of
  every run (`FortInvG`, carried through every rule like `schrittMerk`):

  1. **The caller's shape at a pop** (SATZKARTE §13.5 item 6). A pop needs
     a caller that can receive the answer: a value return into a caller
     that does not wait (`rueck`) or waits for a value of the callee's
     result type (`rueckBind`); a reason into a caller waiting in
     `let … else` with the callee's reason count (`rueckGrund`).
     `FormKette`: every suspended frame has the shape of the call that
     suspended it (`FormG`): not waiting and the callee has no reasons
     (`call`, `callInd`), waiting for `τ` with `erg callee = some τ` and no
     reasons (`bindCall`, `bindCallInd`), or waiting in `wartetSonst n`
     with `erg callee = some τ` and `gruende callee = n` (`bindCallElse`).
  2. **An abrupt exit without a loop.** `leave`/`next` fire only when the
     continuation reaches a loop shim through `dann`/`schrumpf`/`frei`/
     `abbruch` layers (`GRest.absorb`); an `ende` node never stands inside
     a loop (`fOk`: its loop flag is `false`), and every continuation of a
     loop-flagged residue absorbs.
  3. **An `else` residue that falls through.** `abbruch k` has no rule: the
     block in front of it must not end normally. Every block in front of an
     `abbruch` chain ends in a return, reason, `leave` or `next`
     (`Block.terminal`; `Endblock.alsBlock_terminal`), and no residue that
     becomes the head behind a finished block is such a chain
     (`GRest.blockiert`).

  The only premises: `GutO` (axiom leaves extend the trace by accesses,
  static holdings held), `StufenM` and a duplicate-free start trace (the
  `locks` rule's rank side conditions, `sperre_rang`), and
  `KeinLogikHaltG` at the machine -- the conjunct of the flagship that says
  no `logik` check fails (loop invariants, `state` transitions) -- and
  `BereichG` (since 2026-09-15, verdict F1): no float range check fails. An
  out-of-range float is `logik bereich` in the sequential semantics, which
  the body obligation excludes; `fadenS_bereich` carries that to every
  thread of every reachable machine, as `fadenS_prueft` does for the
  `logik` checks.
-/
import Grammatik.Zielsatz.Spec
import Grammatik.RufAdaequatRufG

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Shapes -/

section Formen

variable {V : Vertrag D}

/-- A statement that never ends normally: a return, a reason, `leave`, `next`. -/
def Stmt.istAbschluss {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave .. => true
  | .next .. => true
  | _ => false

/-- The block never ends normally: a statement on its spine is a return, a
    reason, `leave` or `next`. -/
def Block.terminal {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => false
  | .cons s rest => s.istAbschluss || rest.terminal
  | .bind _ rest => rest.terminal
  | .bindCall _ _ _ _ _ rest => rest.terminal
  | .bindCallInd _ _ _ _ _ rest => rest.terminal
  | .bindCallElse _ _ _ _ _ _ rest => rest.terminal
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.terminal
  | .regLies _ _ rest => rest.terminal
  | .regLiesElse _ _ _ _ rest => rest.terminal
  | .awaits _ _ _ _ rest => rest.terminal
  | .exchange _ _ _ _ rest => rest.terminal
  | .narrow _ _ _ _ rest => rest.terminal
  | .pruefung _ _ rest => rest.terminal
  | .gleit _ _ _ _ _ rest => rest.terminal
  | .gleitLit _ _ _ rest => rest.terminal
  | .gleitVon _ _ _ rest => rest.terminal
  | .gleitNarrow _ _ _ _ rest => rest.terminal

/-- An end block run as a block never ends normally. -/
theorem Endblock.alsBlock_terminal {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.terminal = true
  | _, _, .ret _ _ => rfl
  | _, _, .retGrund _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest, Bool.or_true]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]

/-- The residue takes an abrupt exit (`leave`/`next`): a loop shim behind
    `dann`/`schrumpf`/`frei`/`abbruch` layers. -/
def GRest.absorb {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .travRest .. => true
  | .wiederRest .. => true
  | .ewigRest .. => true
  | .dann _ k => k.absorb
  | .schrumpf k => k.absorb
  | .frei _ k => k.absorb
  | .abbruch k => k.absorb
  | _ => false

/-- The residue is an `else` continuation (`abbruch`, under bindings). -/
def GRest.blockiert {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ → Bool
  | .abbruch _ => true
  | .schrumpf k => k.blockiert
  | _ => false

/-- A loop-flagged continuation takes abrupt exits. -/
def GRest.nimmtAb {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ) : Bool :=
  !l || k.absorb

/-- **The residue shape invariant**: no `ende` node inside a loop; every
    loop-flagged continuation absorbs abrupt exits; the block in front of
    an `else` continuation never ends normally; a loop, a release marker
    and a loop shim never continue into an `else` continuation. -/
def GRest.fOk : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ → Bool
  | l, _, _, .ende _ => !l
  | _, _, _, .dann b k => k.fOk && k.nimmtAb && (!k.blockiert || b.terminal)
  | _, _, _, .schrumpf k => k.fOk
  | _, _, _, .frei _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .trav _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .travRest _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .wieder _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .wiederRest _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .ewig _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .ewigRest _ _ _ _ k => k.fOk && k.nimmtAb && !k.blockiert
  | _, _, _, .wartet rest k => k.fOk && k.nimmtAb && (!k.blockiert || rest.terminal)
  | _, _, _, .wartetSonst _ _ rest k => k.fOk && k.nimmtAb && (!k.blockiert || rest.terminal)
  | _, _, _, .abbruch k => k.fOk

end Formen

/-! ## 2. The caller's shape -/

/-- **The frame `c` suspended by a call of `g` can receive `g`'s answer**:
    it does not wait and `g` has no reasons; or it waits for a value of
    `g`'s result type and `g` has no reasons; or it waits in `let … else`
    with `g`'s result type and `g`'s reason count. -/
def FormG (c : RufRahmenG D) (g : D.Fn) : Prop :=
  (c.wartend = false ∧ D.gruende g = 0) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
      (restb : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D c.f) l Γ Λ') (ρc : Env D Γ),
    c.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∧ D.erg g = some τ ∧ D.gruende g = 0) ∨
  (∃ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
      (err : Endblock D (vertragVon D c.f) l (.grund n :: Γ) Λ)
      (restb : Block D (vertragVon D c.f) l (τ :: Γ) Λ Λ')
      (k : GRest D (vertragVon D c.f) l Γ Λ') (ρc : Env D Γ),
    c.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ ∧ D.erg g = some τ ∧ D.gruende g = n)

/-- Every suspended frame has the shape of the call that suspended it: the
    frame right below the frame of `g` can receive `g`'s answer, and so on
    down the stack. -/
def FormKette : D.Fn → List (RufRahmenG D) → Prop
  | _, [] => True
  | g, c :: rest => FormG c g ∧ FormKette c.f rest

/-- **The thread invariant of progress**: the head residue and every
    suspended residue are in shape and no `else` continuation; the stack
    has the shape of its calls. -/
def FortInvG (z : RufFadenG D) : Prop :=
  z.kopf.rest.2.2.2.2.fOk = true ∧ z.kopf.rest.2.2.2.2.blockiert = false ∧
  (∀ c ∈ z.stapel, c.rest.2.2.2.2.fOk = true ∧ c.rest.2.2.2.2.blockiert = false) ∧
  FormKette z.kopf.f z.stapel

/-! ## 3. The invariant along every rule -/

/-- A statement that ends normally is no return, reason or abrupt exit. -/
theorem Stmt.istAbschluss_ok {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (s : Stmt D V l Γ Λ Λ') (σ σ' : World D) (ρ ρ' : Env D Γ)
    (h : execStmt O passes R s σ ρ = .ok σ' ρ') : s.istAbschluss = false := by
  cases s <;> first | rfl | (simp [execStmt] at h)

section Inv

variable {P : Programm D} {O : Orakel D} {passes : Nat}

set_option hygiene false in
/-- A head-local rule: the stack and the function are kept; the new head
    residue is in shape by Boolean bookkeeping over the old one. -/
macro "kopfLokal" : tactic => `(tactic| (
  simp only [rufUpdateG_self]
  obtain ⟨hk, hb, hst, hkt⟩ := h
  rw [‹(M.faeden f).kopf.rest = _›] at hk hb
  refine ⟨?_, ?_, hst, hkt⟩ <;> clear hst hkt hpopS <;>
  (revert hk hb
   simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Block.terminal,
     Stmt.istAbschluss, Endblock.alsBlock_terminal, Bool.and_eq_true, Bool.or_eq_true,
     Bool.not_eq_true', Bool.not_true, Bool.not_false, Bool.true_or, Bool.or_true,
     Bool.false_or, Bool.or_false]
   intro hk hb
   simp_all)))

/-- **Every rule keeps `FortInvG` of the acting thread.** -/
theorem fortInvG_schritt {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') (h : FortInvG (M.faeden f)) :
    FortInvG (M'.faeden f) := by
  have hpopS : ∀ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      (M.faeden f).stapel = caller :: rst →
      (caller.rest.2.2.2.2.fOk = true ∧ caller.rest.2.2.2.2.blockiert = false) ∧
        (∀ c ∈ rst, c.rest.2.2.2.2.fOk = true ∧ c.rest.2.2.2.2.blockiert = false) ∧
        FormG caller (M.faeden f).kopf.f ∧ FormKette caller.f rst := by
    intro caller rst hpop
    obtain ⟨_, _, hst, hkt⟩ := h
    rw [hpop] at hst hkt
    exact ⟨hst caller List.mem_cons_self, fun c hc => hst c (List.mem_cons_of_mem _ hc), hkt.1,
      hkt.2⟩
  cases hs with
  -- pops into a caller that does not wait
  | rueck caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    exact ⟨hc.1, hc.2, hr, hkt⟩
  | rueckCons caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    exact ⟨hc.1, hc.2, hr, hkt⟩
  | dannRet _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    exact ⟨hc.1, hc.2, hr, hkt⟩
  -- binding pops
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, rfl, hr, hkt⟩
    have hc1 := hc.1
    clear hr hkt hpopS h
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc1 <;>
      (revert hc1
       simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
         Bool.or_eq_true, Bool.not_eq_true']
       intro hc1
       simp_all)
  | dannRetBind _ _ _ _ _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, rfl, hr, hkt⟩
    have hc1 := hc.1
    clear hr hkt hpopS h
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc1 <;>
      (revert hc1
       simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
         Bool.or_eq_true, Bool.not_eq_true']
       intro hc1
       simp_all)
  | rueckConsBind _ _ _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, rfl, hr, hkt⟩
    have hc1 := hc.1
    clear hr hkt hpopS h
    rcases hcaller with hcaller | ⟨_, _, hcaller⟩ <;> rw [hcaller] at hc1 <;>
      (revert hc1
       simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
         Bool.or_eq_true, Bool.not_eq_true']
       intro hc1
       simp_all)
  -- reason pops
  | rueckGrund _ _ _ _ caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, rfl, hr, hkt⟩
    have hc1 := hc.1
    rw [hcaller] at hc1
    clear hr hkt hpopS h
    revert hc1
    simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', Endblock.alsBlock_terminal, Bool.or_true, and_true]
    intro hc1
    simp_all
  | rueckConsGrund _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, rfl, hr, hkt⟩
    have hc1 := hc.1
    rw [hcaller] at hc1
    clear hr hkt hpopS h
    revert hc1
    simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', Endblock.alsBlock_terminal, Bool.or_true, and_true]
    intro hc1
    simp_all
  | dannRetGrund _ _ _ _ _ _ caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller =>
    obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
    simp only [rufUpdateG_self]
    refine ⟨?_, rfl, hr, hkt⟩
    have hc1 := hc.1
    rw [hcaller] at hc1
    clear hr hkt hpopS h
    revert hc1
    simp only [GRest.fOk, GRest.nimmtAb, GRest.absorb, GRest.blockiert, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', Endblock.alsBlock_terminal, Bool.or_true, and_true]
    intro hc1
    simp_all
  -- pushes
  | ruf l Γ Λ g args hp hr rest ρ hhead =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, hr⟩, hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hk, rfl⟩
    · exact hst c hc
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, hr⟩, hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨?_, rfl⟩
      revert hk
      simp [GRest.fOk, Block.terminal, Stmt.istAbschluss]
    · exact hst c hc
  | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, by subst hg; exact hr⟩, hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨?_, rfl⟩
      revert hk
      simp [GRest.fOk, Block.terminal, Stmt.istAbschluss]
    · exact hst c hc
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, by subst hg; exact hr⟩, hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hk, rfl⟩
    · exact hst c hc
  | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_, ⟨Or.inr (Or.inl ⟨_, _, _, _, _, rest, k, ρ, rfl, he, hr⟩), hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hk, rfl⟩
    · exact hst c hc
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_, ⟨Or.inr (Or.inl ⟨_, _, _, _, _, rest, k, ρ, rfl,
      by subst hg; exact he, by subst hg; exact hr⟩), hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hk, rfl⟩
    · exact hst c hc
  | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead =>
    obtain ⟨hk, _, hst, hkt⟩ := h
    rw [hhead] at hk
    simp only [rufUpdateG_self]
    refine ⟨rfl, rfl, ?_,
      ⟨Or.inr (Or.inr ⟨_, _, _, _, _, _, err, rest, k, ρ, rfl, he, rfl⟩), hkt⟩⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨hk, rfl⟩
    · exact hst c hc
  -- a leaf in a block: it ended normally, so it was no return
  | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep =>
    have ha := Stmt.istAbschluss_ok O passes keinRuf s _ _ _ _ hstep
    simp only [rufUpdateG_self]
    obtain ⟨hk, hb, hst, hkt⟩ := h
    rw [hhead] at hk hb
    refine ⟨?_, rfl, hst, hkt⟩
    revert hk
    simp only [GRest.fOk, Block.terminal, ha, Bool.false_or, imp_self]
  | _ => kopfLokal

/-- Every rule keeps `FortInvG` at every thread. -/
theorem fortInvG_schritt_alle {M M' : RufMaschineG D} {f : Faden}
    (hs : RufSchrittG P O passes M f M') (h : ∀ g, FortInvG (M.faeden g)) :
    ∀ g, FortInvG (M'.faeden g) := by
  intro g
  by_cases hg : g = f
  · subst hg
    exact fortInvG_schritt hs (h g)
  · rw [rufSchrittG_fremd hs g hg]
    exact h g

/-- **`FortInvG` holds on every reachable machine.** -/
theorem fortInvG_erreichbar (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    ∀ t, FortInvG (M.faeden t) := by
  induction hr with
  | start =>
      intro t
      rw [start_faden]
      exact ⟨rfl, rfl, fun c hc => absurd hc List.not_mem_nil, trivial⟩
  | schritt M M' u _ hs ih => exact fortInvG_schritt_alle hs ih

end Inv

/-! ## 4. Leaves -/

/-- An axiom's answer world extends the trace by accesses only (`GutO`,
    with the call's guards held). -/
theorem axiom_erw {O : Orakel D} (hO : GutO O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) {Λ : List (Res D)}
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hh : HeldIn Λ σ.haelt) :
    Erw σ (O.wirkt a σ ρ).1 := by
  obtain ⟨tabs, globs, Λe, -, -, -, -, -, -, hsp⟩ := (hO a σ ρ).2.2
    (fun t hwr L hL => hh L (hd t hwr _ hL)) (fun g hwr L hL => hh L (hgd g hwr _ hL))
  refine ⟨_, hsp, fun e he => ?_⟩
  rcases axiomSpur_mem he with ⟨t, _, _, rfl⟩ | ⟨g, _, _, rfl⟩ <;> rfl

/-- **A leaf that is no return, reason or abrupt exit** ends normally with
    a trace extended by accesses, or answers hardware, or answers `logik`. -/
theorem blatt_fall {O : Orakel D} (hO : GutO O) (passes : Nat) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (ha : s.istAbschluss = false) (W : World D) (ρ : Env D Γ) (hh : HeldIn Λ (offen W.spur)) :
    (∃ σ' ρ', execStmt O passes keinRuf s W ρ = .ok σ' ρ' ∧ Erw W σ') ∨
    (∃ h, execStmt O passes keinRuf s W ρ = .hardware h) ∨
    (∃ e, execStmt O passes keinRuf s W ρ = .logik e) := by
  cases hx : execStmt O passes keinRuf s W ρ with
  | ok σ' ρ' =>
      refine Or.inl ⟨σ', ρ', rfl, ?_⟩
      cases s with
      | axiomCall a args h hw hg hd hgd =>
          simp only [execStmt] at hx
          split at hx
          · rename_i σ1 v hax
            simp only [Ausgang.ok.injEq] at hx
            obtain ⟨rfl, -⟩ := hx
            have h1 : (O.wirkt a (W.lese Λ args.orte)
                (evalArgs (W.lese Λ args.orte) args (W.lese Λ args.orte) ρ)).1 = σ1 := by
              have := congrArg Prod.fst hax
              simpa [axiomAntwort] using this
            rw [← h1]
            refine (Erw.lese W Λ args.orte).trans (axiom_erw hO a _ _ hd hgd ?_)
            show HeldIn Λ (offen _)
            rw [(Erw.lese W Λ args.orte).offen]
            exact hh
          · cases hx
      | _ =>
          first
          | (simp [Stmt.istAbschluss] at ha; done)
          | (simp [Stmt.istBlatt] at hb; done)
          | exact BlattG.erw O passes keinRuf (by constructor) W σ' ρ ρ' hx
  | hardware h => exact Or.inr (Or.inl ⟨h, rfl⟩)
  | logik e => exact Or.inr (Or.inr ⟨e, rfl⟩)
  | zurueck σ' v =>
      exfalso
      cases s <;> simp [Stmt.istBlatt, Stmt.istAbschluss] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx
  | grund σ' r =>
      exfalso
      cases s <;> simp [Stmt.istBlatt, Stmt.istAbschluss] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx
  | leave hl σ' ρ' =>
      exfalso
      cases s <;> simp [Stmt.istBlatt, Stmt.istAbschluss] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx
  | next hl σ' ρ' =>
      exfalso
      cases s <;> simp [Stmt.istBlatt, Stmt.istAbschluss] at hb ha <;>
        simp only [execStmt] at hx <;> (try split at hx) <;> cases hx

/-! ## 5. The case analysis -/

/-- The lock a `locks` head takes. -/
def Stmt.sperreVon {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Option D.Lock
  | .locks L _ _ => some L
  | _ => none

def Block.sperreVon {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → Option D.Lock
  | .cons s _ => s.sperreVon
  | _ => none

def GRest.kopfSperre {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Option D.Lock
  | .dann b _ => b.sperreVon
  | _ => none

theorem anSperre_kopf {M : RufMaschineG D} {t : Faden} {L : D.Lock} (h : AnSperre M t L) :
    (M.faeden t).kopf.rest.2.2.2.2.kopfSperre = some L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hh⟩ := h
  rw [hh]
  rfl

/-- **The float range checks of G pass for thread `t` of `M`** (2026-09-15, verdict F1): at a
    head `gleit`, float literal or `gleitVon`, the result lies in its declared range at the
    thread's world. Where it does not, G has no rule, and the sequential semantics answers
    `logik bereich` -- which the user's obligation excludes (`fadenS_bereich`). -/
def BereichG (M : RufMaschineG D) (t : Faden) : Prop :=
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (op : GleitOp)
      (l1 h1 l2 h2 lo hi : Int × Int) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2))
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleit op a b lo hi rest) k⟩ →
    gleitPasst lo hi (gleitRechne op
      (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) a
        ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x
      (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) b
        ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x) ≠ none) ∧
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (q lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleitLit q lo hi rest) k⟩ →
    gleitPasst lo hi (bruch q) ≠ none) ∧
  (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (l1 h1 : Int)
      (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int)
      (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.fl lo hi :: Γ) Λ Λ')
      (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.gleitVon e lo hi rest) k⟩ →
    gleitPasst lo hi (gleitAusInt
      (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n) ≠ none)

section Fort

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- What progress says about one thread. -/
def FortFaden (P : Programm D) (O : Orakel D) (passes : Nat) (M : RufMaschineG D) (t : Faden) :
    Prop :=
  FertigG M t ∨ WartetG M t ∨ Zielsatz.HaltBenannt O passes M .flagge t ∨
    Zielsatz.HaltBenannt O passes M .budget t ∨ Zielsatz.HaltBenannt O passes M .hardware t ∨
    Zielsatz.HaltBenannt O passes M .nieZurueck t ∨ ∃ M', RufSchrittG P O passes M t M'

theorem fort_hw {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .hardware t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem fort_flagge {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .flagge t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inl h))

theorem fort_budget {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .budget t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem fort_schritt {M : RufMaschineG D} {t : Faden} {X : RufMaschineG D → Prop}
    (h : ∃ M', RufSchrittG P O passes M t M' ∧ X M') : FortFaden P O passes M t := by
  obtain ⟨M', hs, _⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨M', hs⟩)))))

theorem fort_schritt' {M : RufMaschineG D} {t : Faden}
    (h : ∃ M', RufSchrittG P O passes M t M') : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem fort_nie {M : RufMaschineG D} {t : Faden}
    (h : Zielsatz.HaltBenannt O passes M .nieZurueck t) : FortFaden P O passes M t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- **The caller receives a value** (`FormG`, the invariant of the pop). -/
theorem popArt_von {M : RufMaschineG D} {t : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hst : (M.faeden t).stapel = caller :: rst)
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) :
    ∃ ziel, PopArt (M.faeden t).kopf.f caller ziel := by
  rw [hst] at hkt
  rcases hkt.1 with ⟨hnw, _⟩ | ⟨_, _, _, _, _, restb, k, ρc, hc, he, _⟩ |
      ⟨_, _, _, _, _, n, err, restb, k, ρc, hc, he, _⟩
  · exact ⟨_, PopArt.wie hnw⟩
  · exact ⟨_, PopArt.bind restb k ρc hc he⟩
  · exact ⟨_, PopArt.bindSonst n err restb k ρc hc he⟩

/-- **The caller receives a reason** (`FormG`): only a caller in `let … else`
    can be below a frame that has a reason to answer. -/
theorem popGrund_von {M : RufMaschineG D} {t : Faden} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (hst : (M.faeden t).stapel = caller :: rst)
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel)
    (r : Fin (vertragVon D (M.faeden t).kopf.f).gruende) :
    ∃ zielG, PopGrund (M.faeden t).kopf.f caller zielG := by
  rw [hst] at hkt
  have hr : r.val < D.gruende (M.faeden t).kopf.f := r.2
  rcases hkt.1 with ⟨_, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, _, h0⟩ |
      ⟨_, _, _, _, _, n, err, restb, k, ρc, hc, _, hn⟩
  · omega
  · omega
  · subst hn
    exact ⟨_, PopGrund.sonst err restb k ρc hc⟩

/-- **`leave`/`next` at a loop-flagged head** whose continuation absorbs:
    a loop shim fires, or a layer is peeled. -/
theorem fort_abb {M : RufMaschineG D} {t : Faden} (hP : PrueftG O passes M t) (w : Bool)
    {Γ : Ctx} {Λ Λ1 : List (Res D)} (ρ : Env D Γ)
    (rest : Block D (vertragVon D (M.faeden t).kopf.f) true Γ Λ Λ1)
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) true Γ Λ1)
    (hx : (M.faeden t).kopf.rest = ⟨true, Γ, Λ, ρ, .dann (.cons (abbS rfl w) rest) k⟩)
    (habs : k.absorb = true) (hΛ : HeldIn Λ (offen (M.faeden t).spur)) :
    ∃ M', RufSchrittG P O passes M t M' := by
  cases k with
  | travRest tb inv body is k' =>
      cases ρ with
      | cons i ρ₀ =>
          cases w with
          | true =>
              have hw := hP.2.2.1 _ _ _ _ ρ₀ tb inv body is k' rest rfl i hx
              obtain ⟨M', hs, _⟩ := w_leaveTrav (P := P) rfl tb inv body is k' rest i ρ₀ hx hw hΛ
              exact ⟨M', hs⟩
          | false =>
              obtain ⟨M', hs, _⟩ := w_nextTrav (P := P) (O := O) (passes := passes) rfl tb inv body
                is k' rest i ρ₀ hx hΛ
              exact ⟨M', hs⟩
  | wiederRest n bis body ueber k' =>
      obtain ⟨M', hs, _⟩ := w_abbWieder (P := P) (O := O) (passes := passes) rfl w n bis body ueber
        k' rest ρ hx hΛ
      exact ⟨M', hs⟩
  | ewigRest a n inv body k' =>
      obtain ⟨M', hs, _⟩ := w_abbEwig (P := P) (O := O) (passes := passes) rfl w a n inv body k'
        rest ρ hx hΛ
      exact ⟨M', hs⟩
  | dann b k' =>
      obtain ⟨M', hs, _⟩ := w_peelDann (P := P) (O := O) (passes := passes) rfl w rest b k' ρ hx
      exact ⟨M', hs⟩
  | schrumpf k' =>
      cases ρ with
      | cons v ρ₀ =>
          obtain ⟨M', hs, _⟩ := w_peelSchrumpf (P := P) (O := O) (passes := passes) rfl w rest k' v
            ρ₀ hx
          exact ⟨M', hs⟩
  | frei L k' =>
      obtain ⟨M', hs, _⟩ := w_peelFrei (P := P) (O := O) (passes := passes) rfl w L rest k' ρ hx
      exact ⟨M', hs⟩
  | abbruch k' =>
      obtain ⟨M', hs, _⟩ := w_peelAbbruch (P := P) (O := O) (passes := passes) rfl w rest k' ρ hx
      exact ⟨M', hs⟩
  | _ => simp [GRest.absorb] at habs

/-- **An `ende` head**: a leaf, an unfold, a call, a pop, or a finished
    thread; `leave`/`next` cannot stand there (`fOk`: no `ende` node in a
    loop). -/
theorem fort_ende (hO : GutO O) {M : RufMaschineG D} {t : Faden}
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) (hP : PrueftG O passes M t)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (e : Endblock D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .ende e⟩) (hl : l = false)
    (hΛ : HeldIn Λ (offen (M.faeden t).spur)) : FortFaden P O passes M t := by
  cases e with
  | ret e hp =>
      cases hst : (M.faeden t).stapel with
      | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
      | cons caller rst =>
          obtain ⟨ziel, hart⟩ := popArt_von hst hkt
          exact fort_schritt (w_rueckP rfl caller rst hst hart e hp ρ hx hΛ)
  | retGrund r hp =>
      cases hst : (M.faeden t).stapel with
      | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
      | cons caller rst =>
          obtain ⟨zielG, hart⟩ := popGrund_von hst hkt r
          exact fort_schritt (w_rueckGrundP rfl caller rst hst hart r hp ρ hx hΛ)
  | leave h => exact absurd (hl.symm.trans h) Bool.false_ne_true
  | next h => exact absurd (hl.symm.trans h) Bool.false_ne_true
  | bind e rest => exact fort_schritt (w_endeBind rfl e rest ρ hx hΛ)
  | cons s rest =>
      by_cases hbl : s.istBlatt = true ∧ s.istAbschluss = false
      · rcases blatt_fall hO passes s hbl.1 hbl.2 (M.weltVon t) ρ hΛ with
          ⟨σ', ρ', hst, herw⟩ | ⟨h, hh⟩ | ⟨e, he⟩
        · exact fort_schritt (w_blatt rfl s rest ρ hbl.1 hx hΛ σ' ρ' hst herw)
        · exact fort_hw ⟨l, Γ, Λ, ρ, _, hx, hbl.1, h, hh⟩
        · exact absurd he (hP.2.2.2.1 l Γ Λ _ ρ s rest hbl.1 hx e)
      · cases s with
        | call g args hp hr => exact fort_schritt (w_rufEnde rfl g args hp hr rest ρ hx hΛ)
        | callInd p args hp hr =>
            obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
            exact fort_schritt' ⟨_, RufSchrittG.rufCallInd M t l Γ Λ _ p args hp hr rest ρ hx hΛ
              _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
                ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
        | ret e hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨ziel, hart⟩ := popArt_von hst hkt
                exact fort_schritt (w_rueckConsP rfl caller rst hst hart e hp rest ρ hx hΛ)
        | retGrund r hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨zielG, hart⟩ := popGrund_von hst hkt r
                exact fort_schritt (w_rueckConsGrundP rfl caller rst hst hart r hp rest ρ hx hΛ)
        | leave h => exact absurd (hl.symm.trans h) Bool.false_ne_true
        | next h => exact absurd (hl.symm.trans h) Bool.false_ne_true
        | _ =>
            first
            | exact absurd ⟨rfl, rfl⟩ hbl
            | exact fort_schritt (w_endeEntf rfl _ rest ρ rfl hx)

/-- **A `dann` head**: every block form fires, waits for a lock, or stops
    at its hardware answer; `leave`/`next` find an absorbing continuation
    (`fOk`). An empty answer type stops the head only at an axiom `-> never`
    (`nieZurueck`): the head's answer sites are admissible (`hAnt`, from the
    checker's `antworten` through `kopf_ants`; round-6 finding W1). -/
theorem fort_dann (hO : GutO O) {w0 : D.Fn} {M : RufMaschineG D} {t : Faden}
    (hkt : FormKette (M.faeden t).kopf.f (M.faeden t).stapel) (hP : PrueftG O passes M t)
    (hB : BereichG M t)
    (hR : RangInvG w0 (M.faeden t))
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (b : Block D (vertragVon D (M.faeden t).kopf.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ')
    (hx : (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann b k⟩) (hnimmt : k.nimmtAb = true)
    (hΛ : HeldIn Λ (offen (M.faeden t).spur)) (hAnt : b.ants.all (stelleC D) = true) :
    FortFaden P O passes M t := by
  cases b with
  | nil => exact fort_schritt (w_dannLeer rfl k ρ hx)
  | bind e rest => exact fort_schritt (w_dannBind rfl e rest k ρ hx hΛ)
  | bindCall g args he hp hr rest => exact fort_schritt (w_bindCall rfl g args he hp hr rest k ρ hx hΛ)
  | bindCallInd p args he hp hr rest =>
      obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
      exact fort_schritt' ⟨_, RufSchrittG.dannBindCallInd M t l Γ Λ _ Λ _ _ p args he hp hr rest k
        ρ hx hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
          ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
  | bindCallElse g args he hp hr err rest =>
      exact fort_schritt (w_bindCallElse rfl g args he hp hr err rest k ρ hx hΛ)
  | bindAxiom a args he hw hg hd hgd rest =>
      rcases hax : axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ) with
        ⟨σ₂, _ | v⟩
      · by_cases hleer : AntwortLeer D (D.aerg a)
        · -- the checker admits an empty answer type at an axiom only for `-> never` (W1)
          simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
          exact fort_nie ⟨l, Γ, Λ, ρ, _, hx,
            (stelleC_iff.mp hAnt.1).resolve_right fun h => h hleer⟩
        refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, ?_, hleer⟩
        show (axiomAntwort O a ((M.weltVon t).lese Λ args.orte)
          (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte) ρ)).2
            = none
        rw [hax]
      · have hσ : (O.wirkt a ((M.weltVon t).lese Λ args.orte)
            (evalArgs ((M.weltVon t).lese Λ args.orte) args ((M.weltVon t).lese Λ args.orte)
              ρ)).1 = σ₂ := by
          have := congrArg Prod.fst hax
          simpa [axiomAntwort] using this
        have hh : HeldIn Λ ((M.weltVon t).lese Λ args.orte).haelt := by
          show HeldIn Λ (offen _)
          rw [(Erw.lese (M.weltVon t) Λ args.orte).offen]
          exact hΛ
        have herw := (Erw.lese (M.weltVon t) Λ args.orte).trans
          (axiom_erw hO a _ (evalArgs ((M.weltVon t).lese Λ args.orte) args
            ((M.weltVon t).lese Λ args.orte) ρ) hd hgd hh)
        rw [hσ] at herw
        obtain ⟨neu, hneu, -⟩ := herw
        exact fort_schritt' ⟨_, RufSchrittG.dannBindAxiom M t l Γ Λ _ _ a args he hw hg hd hgd rest
          k ρ hx _ rfl σ₂ v hax neu hneu hΛ⟩
  | regLies r hk rest =>
      by_cases hex : ∃ v, einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r (M.weltVon t)) = some v ∧
          D.rzusage r v = true
      · obtain ⟨v, hv, hz⟩ := hex
        exact fort_schritt (w_regLies rfl r hk rest k ρ hx v hv hz hΛ)
      · by_cases hleer : AntwortLeer D (some (D.rtyp r))
        · -- the checker refuses a register with an empty type (W1)
          simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
          exact absurd hleer (stelleC_iff.mp hAnt.1)
        refine fort_hw ⟨l, Γ, Λ, ρ, _, hx, fun v hv => ?_, hleer⟩
        cases hz : D.rzusage r v
        · rfl
        · exact absurd ⟨v, hv, hz⟩ hex
  | regLiesElse r hk zusage sonst rest =>
      cases hv : einpassen (D := D) O.zeiger (D.rtyp r) (O.regLies r (M.weltVon t)) with
      | none =>
          by_cases hleer : AntwortLeer D (some (D.rtyp r))
          · simp only [Block.ants, List.all_cons, Bool.and_eq_true] at hAnt
            exact absurd hleer (stelleC_iff.mp hAnt.1)
          · exact fort_hw ⟨l, Γ, Λ, ρ, _, hx, hv, hleer⟩
      | some v =>
          cases hw : wahr? (eval ((M.weltVon t).lese Λ zusage.orte) zusage
              ((M.weltVon t).lese Λ zusage.orte) (.cons v ρ)) with
          | true => exact fort_schritt (w_regLiesElseWahr rfl r hk zusage sonst rest k ρ hx v hv hw hΛ)
          | false =>
              exact fort_schritt (w_regLiesElseFalsch rfl r hk zusage sonst rest k ρ hx v hv hw hΛ)
  | awaits g payload hp hL rest =>
      cases hvis : O.sichtbar g (M.weltVon t) with
      | false => exact fort_flagge ⟨l, Γ, Λ, ρ, _, hx, hvis⟩
      | true => exact fort_schritt (w_awaits rfl g payload hp hL rest k ρ hx hvis hΛ)
  | exchange g neuE hw hL rest => exact fort_schritt (w_exchange rfl g neuE hw hL rest k ρ hx hΛ)
  | narrow e lo' hi' sonst rest =>
      by_cases h : lo' ≤ (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n ∧
          (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n ≤ hi'
      · exact fort_schritt (w_narrowOk rfl lo' hi' e sonst rest k ρ hx rfl h hΛ)
      · exact fort_schritt (w_narrowElse rfl lo' hi' e sonst rest k ρ hx h hΛ)
  | pruefung c sonst rest =>
      cases hw : wahr? (eval ((M.weltVon t).lese Λ c.orte) c ((M.weltVon t).lese Λ c.orte) ρ) with
      | true => exact fort_schritt (w_pruefWahr rfl c sonst rest k ρ hx hw hΛ)
      | false => exact fort_schritt (w_pruefFalsch rfl c sonst rest k ρ hx hw hΛ)
  | gleit op a b lo hi rest =>
      cases hv : gleitPasst lo hi (gleitRechne op
          (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) a
            ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x
          (eval ((M.weltVon t).lese Λ (a.orte ++ b.orte)) b
            ((M.weltVon t).lese Λ (a.orte ++ b.orte)) ρ).x) with
      | none => exact absurd hv (hB.1 l Γ Λ _ ρ op _ _ _ _ lo hi a b rest k hx)
      | some v => exact fort_schritt (w_gleit rfl op a b lo hi rest k ρ hx v hv hΛ)
  | gleitLit q lo hi rest =>
      cases hv : gleitPasst lo hi (bruch q) with
      | none => exact absurd hv (hB.2.1 l Γ Λ _ ρ q lo hi rest k hx)
      | some v => exact fort_schritt (w_gleitLit rfl q lo hi rest k ρ hx v hv)
  | gleitVon e lo hi rest =>
      cases hv : gleitPasst lo hi (gleitAusInt
          (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n) with
      | none => exact absurd hv (hB.2.2 l Γ Λ _ ρ _ _ e lo hi rest k hx)
      | some v => exact fort_schritt (w_gleitVon rfl e lo hi rest k ρ hx v hv hΛ)
  | gleitNarrow e lo hi sonst rest =>
      cases hv : gleitPasst lo hi
          (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).x with
      | none => exact fort_schritt (w_gleitNarrowElse rfl e lo hi sonst rest k ρ hx hv hΛ)
      | some v => exact fort_schritt (w_gleitNarrowOk rfl e lo hi sonst rest k ρ hx v hv hΛ)
  | cons s rest =>
      by_cases hbl : s.istBlatt = true ∧ s.istAbschluss = false
      · rcases blatt_fall hO passes s hbl.1 hbl.2 (M.weltVon t) ρ hΛ with
          ⟨σ', ρ', hst, herw⟩ | ⟨h, hh⟩ | ⟨e, he⟩
        · exact fort_schritt (w_dannBlatt rfl s rest k ρ hbl.1 hx hΛ σ' ρ' hst herw)
        · exact fort_hw ⟨l, Γ, Λ, ρ, _, hx, hbl.1, h, hh⟩
        · exact absurd he (hP.2.2.2.2 l Γ Λ _ _ ρ s rest k hbl.1 hx e)
      · cases s with
        | ite c tb eb =>
            cases hw : wahr? (eval ((M.weltVon t).lese Λ c.orte) c ((M.weltVon t).lese Λ c.orte) ρ) with
            | true => exact fort_schritt (w_iteWahr rfl c tb eb rest k ρ hx hw hΛ)
            | false => exact fort_schritt (w_iteFalsch rfl c tb eb rest k ρ hx hw hΛ)
        | onOption o p a =>
            cases hv : eval ((M.weltVon t).lese Λ o.orte) o ((M.weltVon t).lese Λ o.orte) ρ with
            | none => exact fort_schritt (w_optNone rfl o p a rest k ρ hx hv hΛ)
            | some v => exact fort_schritt (w_optSome rfl o p a rest k ρ hx v hv hΛ)
        | onTag v arms =>
            match hw : armWahlG arms (eval ((M.weltVon t).lese Λ v.orte) v
                ((M.weltVon t).lese Λ v.orte) ρ) with
            | ⟨none, b', nutz⟩ => exact fort_schritt (w_tagNone rfl v arms rest k ρ hx b' nutz hw hΛ)
            | ⟨some (lo, hi), b', nutz⟩ =>
                exact fort_schritt (w_tagSome rfl v arms rest k ρ hx lo hi b' nutz hw hΛ)
        | onGrund r arms => exact fort_schritt (w_grund rfl r arms rest k ρ hx hΛ)
        | call g args hp hr => exact fort_schritt (w_rufDann rfl g args hp hr rest k ρ hx hΛ)
        | callInd p args hp hr =>
            obtain ⟨neu, hneu, -⟩ := Erw.lese (M.weltVon t) Λ (p.orte ++ args.orte)
            exact fort_schritt' ⟨_, RufSchrittG.dannCallInd M t l Γ Λ Λ _ _ p args hp hr rest k ρ hx
              hΛ _ rfl _ (eval ((M.weltVon t).lese Λ (p.orte ++ args.orte)) p
                ((M.weltVon t).lese Λ (p.orte ++ args.orte)) ρ).2 rfl _ rfl neu hneu⟩
        | locks L hr body =>
            have hA : AnSperre M t L := ⟨l, Γ, Λ, _, ρ, hr, body, rest, k, hx⟩
            by_cases hfrei : RufFreiG M t L
            · exact fort_schritt' (schritt_an_sperre hR hA hfrei)
            · refine Or.inr (Or.inl ⟨⟨L, hA⟩, fun L' hA' => ?_⟩)
              have e1 := anSperre_kopf hA'
              rw [hx] at e1
              have hLL : L = L' := by
                simpa [GRest.kopfSperre, Block.sperreVon, Stmt.sperreVon] using e1
              subst hLL
              exact Classical.byContradiction fun hno => hfrei fun g hg hLg => hno ⟨g, hg, hLg⟩
        | breaking i body => exact fort_schritt (w_breaking rfl i body rest k ρ hx)
        | traverse tb inv body => exact fort_schritt (w_dannTrav rfl tb inv body rest k ρ hx)
        | retry n bis body ueber => exact fort_schritt (w_dannRetry rfl n bis body ueber rest k ρ hx)
        | forever a inv body => exact fort_schritt (w_dannForever rfl a inv body rest k ρ hx)
        | ret e hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨ziel, hart⟩ := popArt_von hst hkt
                exact fort_schritt (w_dannRetP rfl caller rst hst hart e hp rest k ρ hx hΛ)
        | retGrund r hp =>
            cases hst : (M.faeden t).stapel with
            | nil => exact Or.inl ⟨hst, by rw [hx]; rfl⟩
            | cons caller rst =>
                obtain ⟨zielG, hart⟩ := popGrund_von hst hkt r
                exact fort_schritt (w_dannRetGrundP rfl caller rst hst hart r hp rest k ρ hx hΛ)
        | leave h =>
            subst h
            have habs : k.absorb = true := by simpa [GRest.nimmtAb] using hnimmt
            exact fort_schritt' (fort_abb hP true ρ rest k hx habs hΛ)
        | next h =>
            subst h
            have habs : k.absorb = true := by simpa [GRest.nimmtAb] using hnimmt
            exact fort_schritt' (fort_abb hP false ρ rest k hx habs hΛ)
        | _ => exact absurd ⟨rfl, rfl⟩ hbl

/-- **The progress case analysis for one thread**: finished, waiting for a
    lock another thread holds, at a named hardware stop, or it can step. -/
theorem fortschritt_faden (hO : GutO O) {w0 : D.Fn} {M : RufMaschineG D} {t : Faden}
    (hI : FortInvG (M.faeden t)) (hnw : (M.faeden t).kopf.wartend = false)
    (hH : HeldIn (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur))
    (hP : PrueftG O passes M t) (hB : BereichG M t) (hR : RangInvG w0 (M.faeden t))
    (hA : (M.faeden t).kopf.rest.2.2.2.2.aR (stelleC D)) :
    FortFaden P O passes M t := by
  obtain ⟨hk, hb, _, hkt⟩ := hI
  have hnw' : (M.faeden t).kopf.rest.2.2.2.2.wartend = false := hnw
  generalize hx : (M.faeden t).kopf.rest = x at hk hb hH hnw' hA
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  have hΛ : HeldIn Λ (offen (M.faeden t).spur) := hH
  cases r with
  | ende e =>
      have hl : l = false := by simpa [GRest.fOk] using hk
      exact fort_ende hO hkt hP ρ e hx hl hΛ
  | dann b k =>
      have hn : k.nimmtAb = true := by
        revert hk
        simp only [GRest.fOk, Bool.and_eq_true]
        intro hk
        exact hk.1.2
      exact fort_dann hO hkt hP hB hR ρ b k hx hn hΛ hA.1
  | schrumpf k =>
      cases ρ with
      | cons v ρ₀ => exact fort_schritt (w_schrumpf rfl k v ρ₀ hx)
  | frei L k => exact fort_schritt (w_freiGib rfl L k ρ hx)
  | trav tb inv body ks k =>
      have hw := hP.1 l Γ Λ ρ tb inv body ks k hx
      cases ks with
      | nil => exact fort_schritt (w_travDone rfl tb inv body k ρ hx hw hΛ)
      | cons i is => exact fort_schritt (w_travNext rfl tb inv body i is k ρ hx hw hΛ)
  | travRest tb inv body is k =>
      cases ρ with
      | cons i ρ₀ => exact fort_schritt (w_travFort rfl tb inv body is k i ρ₀ hx)
  | wieder n bis body ueber k =>
      cases n with
      | zero => exact fort_schritt (w_wiederUeber rfl bis body ueber k ρ hx)
      | succ n =>
          cases hw : wahr? (eval ((M.weltVon t).lese Λ bis.orte) bis
              ((M.weltVon t).lese Λ bis.orte) ρ) with
          | true => exact fort_schritt (w_wiederWeiter rfl n bis body ueber k ρ hx hw hΛ)
          | false => exact fort_schritt (w_wiederSchritt rfl n bis body ueber k ρ hx hw hΛ)
  | wiederRest n bis body ueber k => exact fort_schritt (w_wiederFort rfl n bis body ueber k ρ hx)
  | ewig a n inv body k =>
      cases n with
      | zero => exact fort_budget ⟨l, Γ, Λ, ρ, _, hx, trivial⟩
      | succ n =>
          exact fort_schritt (w_ewigWeiter rfl a n inv body k ρ hx
            (hP.2.1 l Γ Λ ρ a n inv body k hx) hΛ)
  | ewigRest a n inv body k => exact fort_schritt (w_ewigFort rfl a n inv body k ρ hx)
  | wartet rest k => simp [GRest.wartend] at hnw'
  | wartetSonst n err rest k => simp [GRest.wartend] at hnw'
  | abbruch k => simp [GRest.blockiert] at hb

end Fort

/-! ## 6. The float range checks pass (verdict F1) -/

section Bereich

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **A replayed thread passes every float range check at its head** (as `fadenS_prueft` for
    the `logik` checks): a failing check makes the head predict `logik bereich` at the
    replay's sequential world (the operands read stable carriers, so the check reads the same
    there), which `KoerperGutS` excludes. -/
theorem fadenS_bereich (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f) {M : RufMaschineG D}
    (t : Faden) (hF : FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) :
    BereichG M t := by
  refine ⟨fun l Γ Λ Λ' ρ op l1 h1 l2 h2 lo hi a b rest k hr hv => ?_,
    fun l Γ Λ Λ' ρ q lo hi rest k hr hv => ?_,
    fun l Γ Λ Λ' ρ l1 h1 e lo hi rest k hr hv => ?_⟩
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    have hab : a.orte ++ b.orte ⊆ fussOrteG P (M.faeden t).kopf.f :=
      fun _ h => hok.2.1 (List.mem_append_left _ h)
    have hgl := hg.lese Λ Λ (a.orte ++ b.orte) (a.orte ++ b.orte)
    have ea := eval_gleichAuf a (fun _ h => expr_stabil (hFS _) a
      (fun _ h' => hab (List.mem_append_left _ h')) h) hgl ρ
    have eb := eval_gleichAuf b (fun _ h => expr_stabil (hFS _) b
      (fun _ h' => hab (List.mem_append_right _ h')) h) hgl ρ
    have hv' : gleitPasst lo hi (gleitRechne op
        (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
        (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = none := by
      rw [ea, eb]; exact hv
    refine hno .bereich ?_
    rw [semH_dann]
    simp only [execBlockH, hv']
    exact weiterH_logik _ _ _ _ _ _ _
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    refine hno .bereich ?_
    rw [semH_dann]
    simp only [execBlockH, hv]
    exact weiterH_logik _ _ _ _ _ _ _
  · obtain ⟨H, HA, HU, σ, hg, hok, hno⟩ := kopfS_keineLogik' hO hRL hQ hS hsp hK hF.1 hr
    have he : e.orte ⊆ fussOrteG P (M.faeden t).kopf.f :=
      fun _ h => hok.2.1 (List.mem_append_left _ h)
    have ee := eval_gleichAuf e (fun _ h => expr_stabil (hFS _) e (fun _ h' => he h') h)
      (hg.lese Λ Λ e.orte e.orte) ρ
    have hv' : gleitPasst lo hi (gleitAusInt
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n) = none := by
      rw [ee]; exact hv
    refine hno .bereich ?_
    rw [semH_dann]
    simp only [execBlockH, hv']
    exact weiterH_logik _ _ _ _ _ _ _

/-- **On every reachable machine every thread passes its float range checks**, for any set
    of local carriers with the rely `LokOk` (the premises of `zielInvS_erreichbarL`). -/
theorem bereichG_erreichbarL (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (lok : D.Tab ⊕ D.Glob → Bool) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussS P S lok f) (hLok : LokOk P O passes lok sp init)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hsp : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (M : RufMaschineG D)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : ∀ t, BereichG M t := fun t =>
  fadenS_bereich hO hRL hQ hS hsp hK hFS t
    ((zielInvS_erreichbarL P O passes Q S lok sp init hO hRL hQ hlok hS hFragS hFS hLok hK
      hStart hsp hex M hr).1.1 t)

/-- The same for thread-local carriers of the call graphs `K` (the premises of
    `ziel_ort_mehrfaden_bei`). -/
theorem bereichG_mehrfaden (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init) (M : RufMaschineG D)
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) : ∀ t, BereichG M t :=
  bereichG_erreichbarL P O passes Q S (lokK P K) sp init hO hRL hQ hlok hS
    (programmImFragmentS_ok P S hvoll hFrag hFuss) hFuss
    (lokOk_mehr hO hvoll sp init K hAbg hWurzel) hK hStart hSstart hex M hr

end Bereich

/-! ## 7. The theorem -/

/-- **`FortschrittG` on every reachable machine at which no `logik` check
    fails.** From `GutO`, the lock floors (`StufenM`) and a duplicate-free
    start trace, on every reachable machine with `KeinLogikHaltG`: every
    thread is finished, waits for a lock another thread holds, stands at a
    named hardware stop, or can step. -/
theorem fortschrittG_aus {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (hSt : StufenM P) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup) {M : RufMaschineG D}
    (hr : RufErreichbarG P O passes (RufStartG P sp init) M) (hL : KeinLogikHaltG O passes M)
    (hB : ∀ t, BereichG M t) (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    Zielsatz.FortschrittG P O passes M := fun t =>
  fortschritt_faden hO (fortInvG_erreichbar sp init hr t)
    (rufG_nie_wartend P O passes sp init M hr t)
    (fun L hL' => rufG_haelt_statisch hO sp init hr t _ List.mem_cons_self L hL') (hL t) (hB t)
    (rangInvG_erreichbar hO hSt sp init hND hr t) (kopf_ants hAnt sp init hr t)

/-- **Progress up to named stops under the premises of the flagship**
    (`ziel_ort_sperre`, whose conclusion supplies `KeinLogikHaltG`), the
    lock floors, and a duplicate-free start trace. -/
theorem fortschrittG_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true) (hFuss : fussSperreB P S fs = true)
    (hK : ∀ f : D.Fn, KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hSt : StufenM P) (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup)
    (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.FortschrittG P O passes M := fun M hr =>
  fortschrittG_aus hO hSt sp init hND hr
    (ziel_ort_sperre P O passes Q S fs sp init hO hRL hQ hlok hS hvoll hFrag hFuss hK hStart
      hSstart hex M hr).2.2.1
    (bereichG_erreichbarL P O passes Q S (freiB fs) sp init hO hRL hQ hlok hS
      (programmImFragmentS_ok P S hvoll hFrag (fussSperreB_ok hvoll hFuss))
      (fussSperreB_ok hvoll hFuss) (lokOk_frei hO hvoll sp init) hK hStart hSstart hex M hr)
    hAnt

/-- **Progress up to named stops under the premises of `ziel_ort_mehrfaden`**
    (several active threads with thread-local carriers, every budget), the
    lock floors and a duplicate-free start trace. -/
theorem fortschrittG_mehrfaden (P : Programm D) (O : Orakel D) (Q : AxEns D)
    (S : SperrInv D) (fs : List D.Fn) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (K : Faden → D.Fn → Bool)
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFrag : programmImFragmentG P fs = true)
    (hAbg : ∀ t, AbgK P fs (K t)) (hWurzel : ∀ t, K t (init t).1 = true)
    (hFuss : ∀ f, FussS P S (lokK P K) f)
    (hK : ∀ (passes : Nat) (f : D.Fn), KoerperGutS P passes Q S f) (hStart : StartGut P sp init)
    (hSstart : ∀ L, S.inv L sp = true) (hex : StartExklusiv init)
    (hI : ∀ (passes : Nat) (f : D.Fn), InvGutS P passes Q S f)
    (hSt : StufenM P) (hND : ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup)
    (hAnt : ∀ g, ∀ x ∈ (P.rumpf g).ants, StelleOk D x) :
    ∀ (passes : Nat) (M : RufMaschineG D), RufErreichbarG P O passes (RufStartG P sp init) M →
      Zielsatz.FortschrittG P O passes M := fun passes M hr =>
  fortschrittG_aus hO hSt sp init hND hr
    (ziel_ort_mehrfaden P O Q S fs sp init K hO hRL hQ hlok hS hvoll hFrag hAbg hWurzel hFuss hK
      hStart hSstart hex hI passes M hr).1.2.2.1
    (bereichG_mehrfaden P O passes Q S fs sp init K hO hRL hQ hlok hS hvoll hFrag hAbg hWurzel
      hFuss (hK passes) hStart hSstart hex M hr) hAnt

/-- Starts without signature locks (the declared starts of `AkzeptiertSpec`
    and every idle start, `Zielsatz.Ruhig`) have a duplicate-free start
    trace. -/
theorem startSpur_nodup_leer (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (h : ∀ t, D.haelt (init t).1 = []) :
    ∀ t, (offen (startSpur (D := D) (init t).1)).Nodup := fun t => by
  rw [startSpur, h t]
  exact List.nodup_nil

#print axioms Gabbro.Grammatik.Endblock.alsBlock_terminal
#print axioms Gabbro.Grammatik.fortInvG_schritt
#print axioms Gabbro.Grammatik.fortInvG_erreichbar
#print axioms Gabbro.Grammatik.axiom_erw
#print axioms Gabbro.Grammatik.blatt_fall
#print axioms Gabbro.Grammatik.fort_abb
#print axioms Gabbro.Grammatik.fort_ende
#print axioms Gabbro.Grammatik.fort_dann
#print axioms Gabbro.Grammatik.fortschritt_faden
#print axioms Gabbro.Grammatik.fortschrittG_aus
#print axioms Gabbro.Grammatik.fortschrittG_sperre
#print axioms Gabbro.Grammatik.fortschrittG_mehrfaden
#print axioms Gabbro.Grammatik.startSpur_nodup_leer

end Gabbro.Grammatik
