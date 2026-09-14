/-
  Gabbro/Grammatik/Fortschritt.lean

  **Progress up to named stops** (`Zielsatz.FortschrittG`, SATZKARTE §19.2).

  On every reachable machine of G, every thread is finished, waits for a
  lock another thread holds, stands at a named hardware stop
  (`Zielsatz.HaltBenannt`), or can step. The proof is a case analysis over
  every head shape of a frame residue against the rules of G
  (`RufMaschineG.lean`): at each shape either some rule fires (the `w_*`
  step builders of `RufAdaequatG.lean`/`RufAdaequatRufG.lean`) or one of
  the three stops applies.

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
  no `logik` check fails (loop invariants, `state` transitions).
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

#print axioms Gabbro.Grammatik.Endblock.alsBlock_terminal
#print axioms Gabbro.Grammatik.fortInvG_schritt
#print axioms Gabbro.Grammatik.fortInvG_erreichbar

end Gabbro.Grammatik
