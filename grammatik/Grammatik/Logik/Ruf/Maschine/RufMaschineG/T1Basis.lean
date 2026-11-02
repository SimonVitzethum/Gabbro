/-
  File:      Grammatik/RufMaschineG.lean
  Subject:   THE CALL MACHINE WITH COMPOUND STATEMENTS (attempt G) -- the F
              machine (frames with stored environments, call-log fidelity
              `rufF_treu`) extended with a residue that can hold
              "block, then rest", so every compound statement form unfolds
              step by step instead of getting stuck.

  Why: `RufMaschineF.lean` steps only leaves (`blatt`), calls (`ruf`) and
  returns (`rueck`); a body with `if`, `match`, a `let` binding, a `locks`
  block or a loop cannot advance (see its CUTS). Here the frame residue is
  a `GRest`: an `Endblock` (`ende`), a `Block` followed by a rest (`dann`),
  an environment shrink (`schrumpf`), a lock release marker (`frei`), and
  bounded-loop states (`trav`/`wieder`/`ewig` with their remaining bound),
  and the residues of a caller waiting for a bound value (`wartet`, and
  `wartetSonst`, which keeps the else block of `let x = g(…) else { … }`).
  New steps unfold compounds into that residue; only pushes and pops touch
  the call log (`eintritt`, `rueck`, and `grund` for the error channel), so
  fidelity (`rufG_treu`) follows the F proof pattern. A waiting caller is
  resumed only by a binding pop: no reachable head waits
  (`rufG_nie_wartend`).
-/
module
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Residues with continuations -/

/-- An end block as a block, with the holdings it ends at. An end block
    never falls through (it ends in `return`, a reason, `leave` or `next`),
    so the block's end holdings are those of its last statement. The
    residue of an `else` branch runs it in BLOCK position, so that a
    `leave`/`next` in it reaches the enclosing loop (`GRest.abbruch`,
    2026-09-13; before, the else branch replaced the residue and dropped the
    loop's continuation). -/
def Endblock.alsBlock {V : Vertrag D} {l : Bool} : {Γ : Ctx} → {Λ : List (Res D)} →
    Endblock D V l Γ Λ → Σ Λ' : List (Res D), Block D V l Γ Λ Λ'
  | _, Λ, .ret e h => ⟨Λ, .cons (.ret e h) .nil⟩
  | _, Λ, .retWhy r h => ⟨Λ, .cons (.retWhy r h) .nil⟩
  | _, Λ, .leave h => ⟨Λ, .cons (.leave h) .nil⟩
  | _, Λ, .next h => ⟨Λ, .cons (.next h) .nil⟩
  | _, _, .cons s rest => ⟨rest.alsBlock.1, .cons s rest.alsBlock.2⟩
  | _, _, .bind e rest => ⟨rest.alsBlock.1, .bind e rest.alsBlock.2⟩
  | _, _, .bindCall f args he hp hr rest =>
      ⟨rest.alsBlock.1, .bindCall f args he hp hr rest.alsBlock.2⟩
  | _, _, .bindCallElse f args he hp hr err rest =>
      ⟨rest.alsBlock.1, .bindCallElse f args he hp hr err rest.alsBlock.2⟩
  | _, _, .bindAxiom a args he hw hg hd hgd rest =>
      ⟨rest.alsBlock.1, .bindAxiom a args he hw hg hd hgd rest.alsBlock.2⟩
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest =>
      ⟨rest.alsBlock.1, .bindAxiomElse a args he hr hw hg hd hgd err rest.alsBlock.2⟩
  | _, _, .regRead r hk rest => ⟨rest.alsBlock.1, .regRead r hk rest.alsBlock.2⟩
  | _, _, .regReadElse r hk z sonst rest => ⟨rest.alsBlock.1, .regReadElse r hk z sonst rest.alsBlock.2⟩
  | _, _, .awaits g pl hp hL hat rest => ⟨rest.alsBlock.1, .awaits g pl hp hL hat rest.alsBlock.2⟩
  | _, _, .bindCallInd p args he hp hr rest => ⟨rest.alsBlock.1, .bindCallInd p args he hp hr rest.alsBlock.2⟩
  | _, _, .bindCallIndElse p args he hp hr err rest =>
      ⟨rest.alsBlock.1, .bindCallIndElse p args he hp hr err rest.alsBlock.2⟩
  | _, _, .narrow e lo' hi' sonst rest => ⟨rest.alsBlock.1, .narrow e lo' hi' sonst rest.alsBlock.2⟩
  | _, _, .narrowRequired e lo' hi' rest => ⟨rest.alsBlock.1, .narrowRequired e lo' hi' rest.alsBlock.2⟩
  | _, _, .retScoped e R => ⟨Λ, .cons (.retScoped e R) .nil⟩
  | _, _, .retWhyScoped r R => ⟨Λ, .cons (.retWhyScoped r R) .nil⟩
  | _, _, .exchange g neu hw hL rest => ⟨rest.alsBlock.1, .exchange g neu hw hL rest.alsBlock.2⟩
  -- an `if` of two end blocks is a check: true runs `t`, false the end block `e` (`Block.check`)
  | _, _, .ite c t e => ⟨t.alsBlock.1, .check c e t.alsBlock.2⟩

/-- The residue of a running frame: what is left to do. `ende` is a plain
    end block; `dann b k` runs the block `b` first, then `k`; `schrumpf`
    drops one bound value from the environment; `frei L` releases the lock
    `L` (taken by a `locks` unfold) and continues; `trav`/`wieder`/`ewig`
    are bounded loops with their remaining indices/tries/budget, each with
    a `Rest` shim that runs one body iteration at the loop context and
    then resumes the loop. -/
inductive GRest (D : Deklaration) (V : Vertrag D) : Bool → Ctx → List (Res D) → Type where
  | ende {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      Endblock D V l Γ Λ → GRest D V l Γ Λ
  | dann {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
      Block D V l Γ Λ Λ' → GRest D V l Γ Λ' → GRest D V l Γ Λ
  | schrumpf {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} :
      GRest D V l Γ Λ → GRest D V l (τ :: Γ) Λ
  | frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      (L : D.Lock) → GRest D V l Γ Λ → GRest D V l Γ (Res.held L :: Λ)
  | trav {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count t)))) :
      GRest D V l Γ Λ → GRest D V l Γ Λ
  | travRest {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
      (inv : Expr D Γ Λ .bool)
      (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
      (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) :
      GRest D V true (.index (D.count t) :: Γ) Λ
  | wieder {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (n : Nat)
      (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) :
      GRest D V l Γ Λ → GRest D V l Γ Λ
  | wiederRest {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (n : Nat)
      (bis : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ) : GRest D V true Γ Λ
  | ewig {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ) :
      GRest D V l Γ Λ → GRest D V l Γ Λ
  | ewigRest {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme) (n : Nat)
      (inv : Expr D Γ Λ .bool) (body : Block D V true Γ Λ Λ)
      (k : GRest D V l Γ Λ) : GRest D V true Γ Λ
  | wartet {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
      (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') :
      GRest D V l Γ Λ
  /-- A caller waiting in `let x = g(…) else { err }`: a normal return binds
      `x` and runs `rest` (as `wartet`); a reason `r : Fin n` runs `err`
      with `r` bound. -/
  | wartetSonst {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (n : Nat)
      (err : Endblock D V l (.why n :: Γ) Λ)
      (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') :
      GRest D V l Γ Λ
  /-- The continuation behind an `else` branch (and behind the reason
      block of `let … else`): the branch never falls through; a `leave` or
      `next` in it reaches `k` (`peelAbbruchLeave`/`peelAbbruchNext`), a
      return pops the frame. Its holdings index is free. -/
  | abbruch {l : Bool} {Γ : Ctx} {Λ Λk : List (Res D)} :
      GRest D V l Γ Λk → GRest D V l Γ Λ
  /-- Nothing is left to run: the base of the continuation behind an end block that was unfolded
      into block position (`endeForm`: `.dann e.alsBlock.2 (.abbruch .leer)`). No step rule has
      it at the head and the block in front never falls off, so it is never reached and carries
      no obligation (Track P, 2026-10-18). -/
  | leer {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : GRest D V l Γ Λ
  /-- C11 pending return: unwind `scopes` innermost first before the outer
      contract/return epilogue. Inert placeholder: no step rule consumes it
      yet; the saved result span, per-scope invariant checks and the
      sequential/replay equality are OPEN. Exact return is `scopes = []`. -/
  | rueckBereit {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
      (scopes : List D.Lock) → GRest D V l Γ Λ → GRest D V l Γ (scopes.map Res.held ++ Λ)

/-- **An end block run as a block means what it meant**: its outcome is
    the end block's, as an `Ausgang` (it never ends normally). -/
theorem Endblock.execBlock_alsBlock (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool} :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
      execBlock O passes R e.alsBlock.2 σ ρ = (execEnd O passes R e σ ρ).zuAusgang
  | _, _, .ret _ _, _, _ => rfl
  | _, _, .retWhy _ _, _, _ => rfl
  | _, _, .leave _, _, _ => rfl
  | _, _, .next _, _, _ => rfl
  | _, _, .cons s rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      cases execStmt O passes R s σ ρ with
      | ok σ' ρ' => exact Endblock.execBlock_alsBlock O passes R rest σ' ρ'
      | _ => rfl
  | _, _, .bind e rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      rw [Endblock.execBlock_alsBlock O passes R rest]
      cases execEnd O passes R rest _ _ <;> rfl
  | _, _, .bindCall f args he hp hr rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rfl
      · rfl
  | _, _, .bindCallElse f args he hp hr err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · cases execEnd O passes R err _ _ <;> rfl
      · rfl
      · rfl
  | _, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · cases execEnd O passes R err _ _ <;> rfl
      · rfl
  | _, _, .regRead r hk rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · split
        · rw [Endblock.execBlock_alsBlock O passes R rest]
          cases execEnd O passes R rest _ _ <;> rfl
        · rfl
      · rfl
  | _, _, .regReadElse r hk z sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · split
        · rw [Endblock.execBlock_alsBlock O passes R rest]
          cases execEnd O passes R rest _ _ <;> rfl
        · rfl
      · rfl
  | _, _, .awaits g pl hp hL hat rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      rename_i f hf _
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rename_i r _
        exact keinGrundSig hf hr r
      · rfl
      · rfl
  | _, _, .bindCallIndElse p args he hp hr err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      rename_i f hf _
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · cases execEnd O passes R err _ _ <;> rfl
      · rfl
      · rfl
  | _, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rfl
  | _, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      rw [Endblock.execBlock_alsBlock O passes R rest]
      cases execEnd O passes R rest _ _ <;> rfl
  | _, _, .ite c t e, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · exact Endblock.execBlock_alsBlock O passes R t _ _
      · rfl
  | _, _, .narrowRequired e lo' hi' rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlock, execEnd]
      split
      · rw [Endblock.execBlock_alsBlock O passes R rest]
        cases execEnd O passes R rest _ _ <;> rfl
      · rfl
  | _, _, .retScoped _ _, _, _ => rfl
  | _, _, .retWhyScoped _ _, _, _ => rfl

end Gabbro.Grammatik
