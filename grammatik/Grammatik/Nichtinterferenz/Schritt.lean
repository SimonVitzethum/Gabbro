/-
  File:      Grammatik/Nichtinterferenz/Schritt.lean
  Subject:   THE STEP OF ONE THREAD AS A FUNCTION OF ITS GHOST-FREE STATE --
             `kSchrittK`, and every rule of machine G computes it
             (`schrittK_von`).

  Why: step consistency compares a step of thread `f` in TWO machines. The
  rules of G are stated over `M.faeden f`, and the types of their premises
  mention `(M.faeden f).kopf.f`; two derivations over two machines cannot
  be compared rule by rule without casts. A FUNCTION of the ghost-free
  state `k : KFaden D` and the memory has no such problem: the two runs
  have the SAME `k` (low-equivalence), and the relational lemma
  (`Lokal.lean`) is one case analysis over `k`'s residue.

  `kSchrittK P O passes k sp` is the new ghost-free state and memory of a
  step of a thread in state `k` over memory `sp` -- the premises of the
  rule that are side conditions (`HeldIn`, `RufFreiG`, rank and
  self-deadlock) are not checked: the function is an over-approximation of
  the rules (`schrittK_von` is one direction), which is all both uses
  need.
-/
module

public import Grammatik.Nichtinterferenz.SchrittBasis
import all Grammatik.Nichtinterferenz.SchrittBasis
public import Grammatik.Nichtinterferenz.Grundlagen
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The result of a step of one thread: its new ghost-free state and the
    new memory, or `none` (no step). -/
abbrev KErg (D : Deklaration) := Option (KFaden D × Speicher D)

section Fn
/-- A statement at the head of a `dann` residue. -/
def kDannCons (P : Programm D) (O : Orakel D) (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Block D (vertragVon D f) l Γ Λ' Λ'')
    (k : GRest D (vertragVon D f) l Γ Λ'') : KErg D :=
  if GEntfaltbar s = true then kEntf passes st f rho spur sp ρ s rest k
  else if s.istBlatt = true then
    kAusDann st f rho rest k (execStmt O passes keinRuf s (sp.welt spur) ρ)
  else kRufDann P st f rho spur sp ρ s rest k

/-- A statement at the head of an `ende` residue. -/
def kEndeCons (P : Programm D) (O : Orakel D) (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (s : Stmt D (vertragVon D f) l Γ Λ Λ') (rest : Endblock D (vertragVon D f) l Γ Λ') : KErg D :=
  if GEntfaltbar s = true then kLokal st f rho ρ (.dann (.cons s .nil) (.ende rest)) spur sp
  else if s.istBlatt = true then
    kAusEnde st f rho rest (execStmt O passes keinRuf s (sp.welt spur) ρ)
  else kRufEnde P st f rho spur sp ρ s rest

/-- An `ende` residue. -/
def kEnde (P : Programm D) (O : Orakel D) (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Env D Γ →
    Endblock D (vertragVon D f) l Γ Λ → KErg D
  | _, _, _, ρ, .cons s rest => kEndeCons P O passes st f rho spur sp ρ s rest
  | _, _, Λ, ρ, .bind e rest =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      kLokal st f rho (.cons (eval σ₁ e σ₁ ρ) ρ) (.ende rest) σ₁.spur sp
  | l, _, Λ, ρ, .bindCall g args he hp hr rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.bindCall g args he hp hr rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .bindCallElse g args he hp hr err rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.bindCallElse g args he hp hr err rest).alsBlock.2
          (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | _, _, Λ, ρ, .bindAxiom a args he _ _ _ _ rest =>
      let σ₁ := (sp.welt spur).lese Λ args.orte
      match axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some v) => kLokal st f rho (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur σ₂.speicher
      | (_, none) => none
  | _, _, Λ, ρ, .bindAxiomElse a args he _ _ _ _ _ err rest =>
      let σ₁ := (sp.welt spur).lese Λ args.orte
      match axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some (Sum.inl v)) => kLokal st f rho (.cons (ergWert he v) ρ) (.ende rest) σ₂.spur σ₂.speicher
      | (σ₂, some (Sum.inr r)) =>
          kLokal st f rho (Env.cons (τ := .why (D.agruende a)) r ρ) (.ende err) σ₂.spur σ₂.speicher
      | (_, none) => none
  | l, _, Λ, ρ, .regRead r hk rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.regRead r hk rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .regReadElse r hk z sonst rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.regReadElse r hk z sonst rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .awaits g pl hp hL hat rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.awaits g pl hp hL hat rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .bindCallInd p args he hp hr rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.bindCallInd p args he hp hr rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .bindCallIndElse p args he hp hr err rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.bindCallIndElse p args he hp hr err rest).alsBlock.2
          (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .narrow e lo' hi' sonst rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.narrow e lo' hi' sonst rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .narrowRequired e lo' hi' rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.narrowRequired e lo' hi' rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .exchange g neu hw hL rest =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.exchange g neu hw hL rest).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | l, _, Λ, ρ, .ite c t e =>
      if l = false then
        kLokal st f rho ρ (.dann (Endblock.ite c t e).alsBlock.2 (.abbruch (Λk := Λ) .leer)) spur sp
      else none
  | _, _, Λ, ρ, .ret e _ =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      kPop st f σ₁ (evalErg σ₁ e σ₁ ρ)
  | _, _, Λ, ρ, .retScoped e _ =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      kPop st f σ₁ (evalErg σ₁ e σ₁ ρ)
  | _, _, _, _, .retWhy r _ => kPopGrund st f spur sp r
  | _, _, _, _, .retWhyScoped r _ => kPopGrund st f spur sp r
  | _, _, _, _, _ => none

/-- A `dann` residue. -/
def kDann (P : Programm D) (O : Orakel D) (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Env D Γ →
    Block D (vertragVon D f) l Γ Λ Λ' → GRest D (vertragVon D f) l Γ Λ' → KErg D
  | _, _, _, _, ρ, .nil, k => kLokal st f rho ρ k spur sp
  | _, _, _, _, ρ, .cons s rest, k => kDannCons P O passes st f rho spur sp ρ s rest k
  | _, _, Λ, _, ρ, .bind e rest, k =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      kLokal st f rho (.cons (eval σ₁ e σ₁ ρ) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
  | _, _, Λ, _, ρ, .bindCall g args _ _ _ rest, k =>
      let s0 := (sp.welt spur).lese Λ args.orte
      kPush P st f rho ρ (.wartet rest k) g (evalArgs s0 args s0 ρ) s0.spur sp
  | _, _, Λ, _, ρ, .bindCallInd p args _ _ _ rest, k =>
      let s0 := (sp.welt spur).lese Λ (p.orte ++ args.orte)
      match eval s0 p s0 ρ with
      | ⟨g, hg⟩ => kPush P st f rho ρ (.wartet rest k) g (umsig hg (evalArgs s0 args s0 ρ)) s0.spur sp
  | _, _, Λ, _, ρ, .bindCallIndElse (n := n) p args _ _ _ err rest, k =>
      let s0 := (sp.welt spur).lese Λ (p.orte ++ args.orte)
      match eval s0 p s0 ρ with
      | ⟨g, hg⟩ => kPush P st f rho ρ (.wartetSonst (D.sigNr n).gruende err rest k) g
          (umsig hg (evalArgs s0 args s0 ρ)) s0.spur sp
  | _, _, Λ, _, ρ, .bindCallElse g args _ _ _ err rest, k =>
      let s0 := (sp.welt spur).lese Λ args.orte
      kPush P st f rho ρ (.wartetSonst (D.gruende g) err rest k) g (evalArgs s0 args s0 ρ) s0.spur sp
  | _, _, Λ, _, ρ, .bindAxiom a args he _ _ _ _ rest, k =>
      let σ₁ := (sp.welt spur).lese Λ args.orte
      match axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some v) => kLokal st f rho (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
          σ₂.speicher
      | (_, none) => none
  | _, _, Λ, _, ρ, .bindAxiomElse a args he _ _ _ _ _ err rest, k =>
      let σ₁ := (sp.welt spur).lese Λ args.orte
      match axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some (Sum.inl v)) =>
          kLokal st f rho (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur σ₂.speicher
      | (σ₂, some (Sum.inr r)) =>
          kLokal st f rho (Env.cons (τ := .why (D.agruende a)) r ρ)
            (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σ₂.spur σ₂.speicher
      | (_, none) => none
  | _, _, _, _, ρ, .regRead r _ rest, k =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r ((sp.welt spur).fragt (.inr (.inl r)))) with
      | some v =>
          if D.rzusage r v = true then
            kLokal st f rho (.cons v ρ) (.dann rest (.schrumpf k)) ((sp.welt spur).fragt (.inr (.inl r))).spur sp
          else none
      | none => none
  | _, _, Λ, _, ρ, .regReadElse r _ zusage sonst rest, k =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r ((sp.welt spur).fragt (.inr (.inl r)))) with
      | some v =>
          let σ₁ := ((sp.welt spur).fragt (.inr (.inl r))).lese Λ zusage.orte
          if wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = true then
            kLokal st f rho (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
          else kLokal st f rho ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur sp
      | none => none
  | _, _, Λ, _, ρ, .awaits g _ _ _ _ rest, k =>
      if O.sichtbar g ((sp.welt spur).fragt (.inr (.inr g))) = true then
        let σ₁ := ((sp.welt spur).fragt (.inr (.inr g))).lese Λ [.inr g]
        kLokal st f rho (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      else none
  | _, _, Λ, _, ρ, .exchange g neuE _ _ rest, k =>
      let σ₁ := (sp.welt spur).lese Λ (.inr g :: neuE.orte)
      let σ₂ := σ₁.schreibGlob g Λ (eval σ₁ neuE σ₁ (.cons (σ₁.globs g) ρ))
      kLokal st f rho (.cons (σ₁.globs g) ρ) (.dann rest (.schrumpf k)) σ₂.spur σ₂.speicher
  | _, _, Λ, _, ρ, .narrow e lo' hi' sonst rest, k =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      if h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi' then
        kLokal st f rho (.cons (show Wert D (.int lo' hi') from ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      else kLokal st f rho ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur sp
  | _, _, Λ, _, ρ, .narrowRequired e lo' hi' rest, k =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      if h : lo' ≤ (eval σ₁ e σ₁ ρ).n ∧ (eval σ₁ e σ₁ ρ).n ≤ hi' then
        kLokal st f rho (.cons (show Wert D (.int lo' hi') from ⟨(eval σ₁ e σ₁ ρ).n, h.1, h.2⟩) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      else none
  | _, _, Λ, _, ρ, .check c sonst rest, k =>
      let σ₁ := (sp.welt spur).lese Λ c.orte
      if wahr? (eval σ₁ c σ₁ ρ) = true then kLokal st f rho ρ (.dann rest k) σ₁.spur sp
      else kLokal st f rho ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur sp
  | _, _, Λ, _, ρ, .float op a b lo hi rest, k =>
      let σ₁ := (sp.welt spur).lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      | none => none
  | _, _, _, _, ρ, .floatLit q lo hi rest, k =>
      match gleitPasst lo hi (bruch q) with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) spur sp
      | none => none
  | _, _, Λ, _, ρ, .floatOf e lo hi rest, k =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      | none => none
  | _, _, Λ, _, ρ, .floatNarrow e lo hi sonst rest, k =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      match gleitPasst lo hi (eval σ₁ e σ₁ ρ).x with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      | none => kLokal st f rho ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur sp

/-- **A residue**: the dispatcher over the head of the residue. -/
def kr (P : Programm D) (O : Orakel D) (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → Env D Γ →
    GRest D (vertragVon D f) l Γ Λ → KErg D
  | _, _, _, ρ, .ende e => kEnde P O passes st f rho spur sp ρ e
  | _, _, _, ρ, .dann b k => kDann P O passes st f rho spur sp ρ b k
  | _, _, _, .cons _ ρ, .schrumpf k => kLokal st f rho ρ k spur sp
  | _, _, _, ρ, .frei L k => kLokal st f rho ρ k (.gibt L :: spur) sp
  | _, _, Λ, ρ, .trav t inv body (i :: is) k =>
      let σ₁ := (sp.welt spur).lese Λ inv.orte
      if wahr? (eval σ₁ inv σ₁ ρ) = true then
        kLokal st f rho (.cons i ρ) (.dann body (.travRest t inv body is k)) σ₁.spur sp
      else none
  | _, _, Λ, ρ, .trav _ inv _ [] k =>
      let σ₁ := (sp.welt spur).lese Λ inv.orte
      if wahr? (eval σ₁ inv σ₁ ρ) = true then kLokal st f rho ρ k σ₁.spur sp else none
  | _, _, _, .cons _ ρ, .travRest t inv body is k => kLokal st f rho ρ (.trav t inv body is k) spur sp
  | _, _, _, ρ, .wieder 0 bis _ ueber k =>
      kLokal st f rho ρ (.dann (.cons (.ite bis .nil ueber) .nil) k) spur sp
  | _, _, Λ, ρ, .wieder (n + 1) bis body ueber k =>
      let σ₁ := (sp.welt spur).lese Λ bis.orte
      if wahr? (eval σ₁ bis σ₁ ρ) = true then kLokal st f rho ρ k σ₁.spur sp
      else kLokal st f rho ρ (.dann body (.wiederRest n bis body ueber k)) σ₁.spur sp
  | _, _, _, ρ, .wiederRest n bis body ueber k =>
      kLokal st f rho ρ (.wieder n bis body ueber k) spur sp
  | _, _, Λ, ρ, .ewig a (n + 1) inv body k =>
      let σ₁ := (sp.welt spur).lese Λ inv.orte
      if wahr? (eval σ₁ inv σ₁ ρ) = true then
        kLokal st f rho ρ (.dann body (.ewigRest a n inv body k)) σ₁.spur sp
      else none
  | _, _, _, ρ, .ewigRest a n inv body k => kLokal st f rho ρ (.ewig a n inv body k) spur sp
  | _, _, _, _, _ => none

end Fn

/-- **The step of a thread as a function of its ghost-free state** `k` and
    the memory `sp`: the new ghost-free state and the new memory. -/
def kSchrittK (P : Programm D) (O : Orakel D) (passes : Nat) (k : KFaden D) (sp : Speicher D) :
    KErg D :=
  kr P O passes k.stapel k.kopf.f k.kopf.rho k.spur sp k.kopf.rest.2.2.2.1 k.kopf.rest.2.2.2.2

end Gabbro.Grammatik
