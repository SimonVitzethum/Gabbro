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
public import Grammatik.Kern.Syntax.Typen.Fall
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1Basis
import all Grammatik.Logik.Ruf.Maschine.RufMaschineG.T1Basis
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Logik.Vertraege.Locations.VertragOrtB
public import Grammatik.Logik.Ruf.Maschine.RufMaschineF
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- A residue that waits for a callee's answer (`wartet`/`wartetSonst`):
    only a BINDING pop may resume it. -/
def GRest.wartend {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    GRest D V l Γ Λ → Bool
  | .wartet .. => true
  | .wartetSonst .. => true
  | _ => false

/-- One frame: as in F, but the residue is a `GRest`. -/
structure RufRahmenG (D : Deklaration) where
  f : D.Fn
  rho : Env D (D.params f)
  s0 : World D
  rest :
    Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D),
      Env D Γ × GRest D (vertragVon D f) l Γ Λ

/-- The frame waits for a callee's answer. -/
def RufRahmenG.wartend (r : RufRahmenG D) : Bool := r.rest.2.2.2.2.wartend

structure RufFadenG (D : Deklaration) where
  stapel : List (RufRahmenG D)
  kopf : RufRahmenG D
  spur : List (Ereignis D)
  log : List (RufEreignisF D)

structure RufMaschineG (D : Deklaration) where
  speicher : Speicher D
  faeden : Faden → RufFadenG D
  lauf : Lauf D
  start : World D

/-- Resume a caller with an already evaluated answer. Both the G and K
    machines use this operation, including the signature equality checks. -/
def antwortRestG {V : Vertrag D} (g : D.Fn)
    (antwort : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) :
    Option (Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ) :=
  match antwort, c with
  | .inl v, ⟨l, Γ, Λ, ρ, .wartet (τ := τ) rest k⟩ =>
      if he : (vertragVon D g).erg = some τ then
        some ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .dann rest (.schrumpf k)⟩
      else none
  | .inl v, ⟨l, Γ, Λ, ρ, .wartetSonst (τ := τ) _ _ rest k⟩ =>
      if he : (vertragVon D g).erg = some τ then
        some ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρ, .dann rest (.schrumpf k)⟩
      else none
  | .inl _, c => some c
  | .inr r, ⟨l, Γ, Λ, ρ, .wartetSonst n err _ k⟩ =>
      if hn : (vertragVon D g).gruende = n then
        some ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn r) ρ,
          .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩
      else none
  | .inr _, _ => none

/-- Resuming either answer channel keeps the caller's static resources. -/
theorem antwortRestG_ressourcen {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (h : antwortRestG g a c = some c') : c'.2.2.1 = c.2.2.1 := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a <;> cases r <;> simp_all [antwortRestG]
  all_goals split at h <;> simp_all

/-- Return after cleanup. A root keeps its entry record and a completed
    residue; a callee pops and records its answer at the released world.
    The returned value is supplied, never re-evaluated after a release. -/
def rufAntwortG (z : RufFadenG D) (vor σ : World D)
    (antwort : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende) :
    Option (RufFadenG D) :=
  match z.stapel with
  | [] => some ⟨[],
      ⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
        ⟨false, D.params z.kopf.f, (vertragVon D z.kopf.f).ende,
          z.kopf.rho, .zurueckgekehrt ⟨antwort, vor⟩⟩⟩, σ.spur, z.log⟩
  | c :: st => do
      let rest ← antwortRestG z.kopf.f antwort c.rest
      let ev := match antwort with
        | .inl v => RufEreignisF.rueck z.kopf.f z.kopf.rho v z.kopf.s0 σ
        | .inr r => RufEreignisF.why z.kopf.f z.kopf.rho r z.kopf.s0 σ
      pure ⟨st, ⟨c.f, c.rho, c.s0, rest⟩, σ.spur, ev :: z.log⟩

/-- Both answer channels retain exactly the cleanup trace. -/
theorem rufAntwortG_spur {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (h : rufAntwortG z vor σ a = some z') : z'.spur = σ.spur := by
  cases hs : z.stapel with
  | nil => simp only [rufAntwortG, hs, Option.some.injEq] at h; subst z'; rfl
  | cons c st =>
      simp only [rufAntwortG, hs] at h
      cases hr : antwortRestG z.kopf.f a c.rest <;>
        simp_all [Option.bind]

/-- Answering either keeps an empty root stack or removes its first frame. -/
theorem rufAntwortG_stapel {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (h : rufAntwortG z vor σ a = some z') : z'.stapel = z.stapel.tail := by
  cases hs : z.stapel with
  | nil => simp only [rufAntwortG, hs, Option.some.injEq] at h; subst z'; rfl
  | cons c st =>
      simp only [rufAntwortG, hs] at h
      cases hr : antwortRestG z.kopf.f a c.rest <;>
        simp_all [Option.bind]

/-- Cleanup changes only the trace, including for an empty scope list. -/
theorem World.gibt_foldl_mem (σ : World D) (Ls : List D.Lock) :
    (Ls.foldl World.gibt σ).speicher = σ.speicher := by
  obtain ⟨hs, hg⟩ := World.gibt_foldl_speicher σ Ls
  simp only [World.speicher, hs, hg]

/-- Releasing several locks cannot introduce a held lock. -/
theorem mem_of_mem_eraseScopes (Ls : List D.Lock) (held : List D.Lock) {K : D.Lock}
    (h : K ∈ Ls.foldl (fun h L => h.erase L) held) : K ∈ held := by
  induction Ls generalizing held with
  | nil => exact h
  | cons L Ls ih => exact List.mem_of_mem_erase (ih _ h)

/-- A lock outside the cleanup list survives every release. -/
theorem mem_eraseScopes_of_not_mem (Ls : List D.Lock) (held : List D.Lock) {K : D.Lock}
    (hn : K ∉ Ls) (h : K ∈ held) : K ∈ Ls.foldl (fun h L => h.erase L) held := by
  induction Ls generalizing held with
  | nil => exact h
  | cons L Ls ih =>
      apply ih _ (fun hm => hn (List.mem_cons_of_mem _ hm))
      exact (List.mem_erase_of_ne (fun he => hn (List.mem_cons.mpr (Or.inl he)))).mpr h

/-- The current world of thread `f`: live shared memory plus its own trace. -/
def RufMaschineG.weltVon (M : RufMaschineG D) (f : Faden) : World D :=
  M.speicher.welt (M.faeden f).spur

/-- No thread other than `f` holds `L` right now -- the scheduler rule side. -/
def RufFreiG (M : RufMaschineG D) (f : Faden) (L : D.Lock) : Prop :=
  ∀ g, g ≠ f → L ∉ offen (M.faeden g).spur

/-- The new run events of one step, all attributed to the acting thread. -/
def rufEigenG (f : Faden) (neu : List (Ereignis D)) : Lauf D :=
  neu.reverse.map fun e => Schritt.mk f e

/-- One thread state replaced, all others kept. -/
def rufUpdateG (m : Faden → RufFadenG D) (f : Faden) (z : RufFadenG D) :
    Faden → RufFadenG D :=
  fun g => if g = f then z else m g

theorem rufUpdateG_self (m : Faden → RufFadenG D) (f : Faden) (z : RufFadenG D) :
    rufUpdateG m f z f = z := by
  simp only [rufUpdateG, ↓reduceIte]

theorem rufUpdateG_noteq (m : Faden → RufFadenG D) (f g : Faden) (h : g ≠ f)
    (z : RufFadenG D) :
    rufUpdateG m f z g = m g := by
  simp only [rufUpdateG, h, ↓reduceIte]

/-! ## 2. Which compounds unfold -/

/-- Compounds with an unfold step: `ite`, `onOption`, `onTag`, `onGrund`,
    `locks`, `breaking` and the bounded loops. `call`/`callInd` are excluded
    (the `ruf`/`rufDann` and `callInd` steps handle them); the bind-call and
    register/atomic/float `Block` forms have their own `dann` steps.
    `callIndElse` unfolds through `endeEntf` into `bindCallIndElse` with an
    empty success tail (`dannCallIndElse`), so both statement positions share
    the one dispatch. -/
def GEntfaltbar {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → Bool
  | .ite .. => true
  | .onOption .. => true
  | .onTag .. => true
  | .onWhy .. => true
  | .callIndElse .. => true
  | .locks .. => true
  | .breaking .. => true
  | .axiomCallElse .. => true
  | .traverse .. => true
  | .retry .. => true
  | .forever .. => true
  /- C11 consuming traversal unfolds through `dannVerbrauch` into the
      `verbrauch`/`verbrauchRest` selection continuations of group 7, which
      re-select in the current world round by round like `execStmt`. -/
  | .consumeTraverse .. => true
  | _ => false

/-- The end-block formers that the machine unfolds into block position (`endeForm`): the
    residue `.ende e` becomes `.dann e.alsBlock.2 (.abbruch .leer)`, and the BLOCK steps run it
    (the fall-through is never reached: an end block does not fall off). The formers
    with a step of their own (`cons`, `bind`, `bindAxiom`, `bindAxiomElse`, the returns) are not
    listed. Written without a wildcard, so a new `Endblock` former must be placed here. -/
def EndEntfaltbar {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → Bool
  | .ret .. => false
  | .retWhy .. => false
  | .leave .. => false
  | .next .. => false
  | .cons .. => false
  | .bind .. => false
  | .bindCall .. => true
  | .bindCallElse .. => true
  | .bindAxiom .. => false
  | .bindAxiomElse .. => false
  | .bindAxiomOpt .. => false
  | .bindAxiomOptElse .. => false
  | .regRead .. => true
  | .regReadElse .. => true
  | .awaits .. => true
  | .bindCallInd .. => true
  | .bindCallIndElse .. => true
  | .narrow .. => true
  | .narrowRequired .. => true
  | .exchange .. => true
  | .ite .. => true
  /- C11 scoped returns are terminal in the placeholder: they do not unfold
      into block position beyond `alsBlock`, and no step rule consumes the
      pending scope unwinding yet. -/
  | .retScoped .. => false
  | .retWhyScoped .. => false

/-- Arm selection for `onTag`: the VALUE's index chooses the arm and the
    VALUE's payload feeds it (like `execArms`, but returning the chosen arm
    instead of running it). The `nil` case cannot fire (`Fin 0` is empty). -/
def armWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) →
      Σ c : Option Ty, Block D V l (ArmCtx Γ c) Λ Λ' × Nutzlast D.Fn D.passt c
  | .nil, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨⟨0, _⟩, nutz⟩ => ⟨_, b, Fall.toNutzlast _ _ _ _ nutz⟩
  | .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩ =>
      armWahlG rest ⟨⟨n, Nat.lt_of_succ_lt_succ h⟩, nutz⟩

/-- Arm selection for `onGrund`: the VALUE's index chooses the arm
    (like `execGrund`, but returning the chosen arm instead of running it). -/
def grundWahlG {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → Block D V l Γ Λ Λ'
  | .nil, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨0, _⟩ => b
  | .cons _ rest, ⟨k + 1, h⟩ =>
      grundWahlG rest ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-! ## 3. The step relation: F steps plus compound unfolds -/


end Gabbro.Grammatik
