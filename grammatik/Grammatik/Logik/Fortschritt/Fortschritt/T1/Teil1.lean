module

public import Grammatik.Zielsatz.Kern.Spec
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Shapes -/

section Formen

variable {V : Vertrag D}

/-- A statement that never ends normally: a return, a reason, `leave`, `next`. -/
def Stmt.istAbschluss {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ret .. => true
  | .retWhy .. => true
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
  | .bindAxiomElse _ _ _ _ _ _ _ _ _ rest => rest.terminal
  | .regRead _ _ rest => rest.terminal
  | .regReadElse _ _ _ _ rest => rest.terminal
  | .awaits _ _ _ _ _ rest => rest.terminal
  | .exchange _ _ _ _ rest => rest.terminal
  | .narrow _ _ _ _ rest => rest.terminal
  | .check _ _ rest => rest.terminal
  | .float _ _ _ _ _ rest => rest.terminal
  | .floatLit _ _ _ rest => rest.terminal
  | .floatOf _ _ _ rest => rest.terminal
  | .floatNarrow _ _ _ _ rest => rest.terminal

/-- An end block run as a block never ends normally. -/
theorem Endblock.alsBlock_terminal {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), e.alsBlock.2.terminal = true
  | _, _, .ret _ _ => rfl
  | _, _, .retWhy _ _ => rfl
  | _, _, .leave _ => rfl
  | _, _, .next _ => rfl
  | _, _, .cons _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest, Bool.or_true]
  | _, _, .bind _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCall _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindAxiom _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCallElse _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindAxiomElse _ _ _ _ _ _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .regRead r hk rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .regReadElse r hk z sonst rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .awaits g pl hp hL hat rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .bindCallInd p args he hp hr rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .narrow _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .exchange _ _ _ _ rest => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal rest]
  | _, _, .ite _ t _ => by
      simp only [Endblock.alsBlock, Block.terminal, Endblock.alsBlock_terminal t]

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
  | .leer => true
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
  | _, _, _, .leer => true

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
      (err : Endblock D (vertragVon D c.f) l (.why n :: Γ) Λ)
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
  cases s <;> first | rfl | (simp only [execStmt, reduceCtorEq] at h)

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
  | g1 hs =>
    cases hs with
    | rueck caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨hc.1, hc.2, hr, hkt⟩
    | ruf l Γ Λ g args hp hr rest ρ hhead =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨hk, rfl⟩
      · exact hst c hc
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf hhead hΛ σ' ρ' neu hstep =>
      have ha := Stmt.istAbschluss_ok O passes keinRuf s _ _ _ _ hstep
      simp only [rufUpdateG_self]
      obtain ⟨hk, hb, hst, hkt⟩ := h
      rw [hhead] at hk hb
      refine ⟨?_, rfl, hst, hkt⟩
      revert hk
      simp only [GRest.fOk, Block.terminal, ha, Bool.false_or, imp_self]
    | _ => kopfLokal
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨?_, rfl⟩
        revert hk
        simp only [GRest.fOk, Block.terminal, Stmt.istAbschluss, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, imp_self]
      · exact hst c hc
    | _ => kopfLokal
  | g3 hs =>
    cases hs with
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
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, (D.passt_sig hg).gruende.trans hr⟩, hkt⟩⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨?_, rfl⟩
        revert hk
        simp only [GRest.fOk, Block.terminal, Stmt.istAbschluss, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, imp_self]
      · exact hst c hc
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg =>
      obtain ⟨hk, _, hst, hkt⟩ := h
      rw [hhead] at hk
      simp only [rufUpdateG_self]
      refine ⟨rfl, rfl, ?_, ⟨Or.inl ⟨rfl, (D.passt_sig hg).gruende.trans hr⟩, hkt⟩⟩
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
        ergSig hg he, (D.passt_sig hg).gruende.trans hr⟩), hkt⟩⟩
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
    | _ => kopfLokal
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨hc.1, hc.2, hr, hkt⟩
    | dannRet _ _ _ _ _ _ _ _ _ _ caller rst hpop _ _ _ _ _ _ _ _ _ _ _ _ _ hnw =>
      obtain ⟨hc, hr, _, hkt⟩ := hpopS caller rst hpop
      simp only [rufUpdateG_self]
      exact ⟨hc.1, hc.2, hr, hkt⟩
    -- binding pops
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
    | _ => kopfLokal
  | g5 hs =>
    cases hs with
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
    | _ => kopfLokal
  | g6 hs =>
    cases hs with
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

end Gabbro.Grammatik
