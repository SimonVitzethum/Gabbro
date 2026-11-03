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
public import Grammatik.Nichtinterferenz.Grundlagen
@[expose] public section


noncomputable section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The result of a step of one thread: its new ghost-free state and the
    new memory, or `none` (no step). -/
abbrev KErg (D : Deklaration) := Option (KFaden D × Speicher D)

section Fn


/-- A head-local result: same stack and function, a new residue. -/
def kLokal (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D f) l Γ Λ) (spur : List (Ereignis D)) (sp : Speicher D) : KErg D :=
  some (⟨st, ⟨f, rho, ⟨l, Γ, Λ, ρ, r⟩⟩, spur⟩, sp)

/-- A push: the caller's residue suspended, the callee `g` entered. -/
def kPush (P : Programm D) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (rc : GRest D (vertragVon D f) l Γ Λ) (g : D.Fn) (rhog : Env D (D.params g))
    (spur : List (Ereignis D)) (sp : Speicher D) : KErg D :=
  some (⟨⟨f, rho, ⟨l, Γ, Λ, ρ, rc⟩⟩ :: st,
    ⟨g, rhog, ⟨false, D.params g, Signatur.anfang D (D.signatur g), rhog, .ende (P.rumpf g)⟩⟩,
    spur⟩, sp)

/-- A caller waiting for a bound value resumes with it. -/
def kBinde (f : D.Fn) (rst : List (KRahmen D)) (c : KRahmen D) (σ : World D)
    (v : ErgVal D (vertragVon D f).erg) : KErg D :=
  match c.rest with
  | ⟨l, Γ, Λ, ρc, GRest.wartet (τ := τ) restb k⟩ =>
      if he : (vertragVon D f).erg = some τ then
        some (⟨rst, ⟨c.f, c.rho, ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩,
          σ.spur⟩, σ.speicher)
      else none
  | ⟨l, Γ, Λ, ρc, GRest.wartetSonst (τ := τ) _ _ restb k⟩ =>
      if he : (vertragVon D f).erg = some τ then
        some (⟨rst, ⟨c.f, c.rho, ⟨l, τ :: Γ, Λ, .cons (ergWert he v) ρc, .dann restb (.schrumpf k)⟩⟩,
          σ.spur⟩, σ.speicher)
      else none
  | _ => none

/-- A pop with a saved value: a caller resumes, bound if it waits; a root
    retains the completed answer. The root environment is explicit because
    the completed residue has no expression or live local bindings. -/
def kPop (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (σ : World D) (v : ErgVal D (vertragVon D f).erg) : KErg D :=
  match st with
  | [] => kLokal [] f rho rho (.zurueckgekehrt (l := false) ⟨.inl v, σ.ohneSnapshot⟩) σ.spur σ.speicher
  | c :: rst =>
      if c.rest.2.2.2.2.wartend = true then kBinde f rst c σ v
      else some (⟨rst, c, σ.spur⟩, σ.speicher)

/-- A pop with a reason: a caller waiting in `let … else` runs its else
    block; a root retains a completed reason (excluded for accepted starts). -/
def kPopGrund (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) (r : Fin (vertragVon D f).gruende) :
    KErg D :=
  match st with
  | [] => kLokal [] f rho rho (.zurueckgekehrt (l := false) ⟨.inr r, (sp.welt spur).ohneSnapshot⟩) spur sp
  | c :: rst =>
      match c.rest with
      | ⟨l, Γ, Λ, ρc, GRest.wartetSonst n err _ k⟩ =>
          if hn : (vertragVon D f).gruende = n then
            some (⟨rst, ⟨c.f, c.rho, ⟨l, .why n :: Γ, Λ, .cons (Fin.cast hn r) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩, spur⟩, sp)
          else none
      | _ => none

/-- The ghost-free return protocol shares the same empty/nonempty boundary
    as G. A nonempty list keeps the answer until its last release. -/
def kScoped (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f))
    {l : Bool} {Γ : Ctx} (ρ : Env D Γ)
    (a : ErgVal D (vertragVon D f).erg ⊕ Fin (vertragVon D f).gruende)
    (σ : World D) (remaining : List D.Lock) : KErg D :=
  match remaining with
  | [] => match a with
      | .inl v => kPop st f rho σ v
      | .inr r => kPopGrund st f rho σ.spur σ.speicher r
  | _ :: _ => kLokal st f rho ρ (.aufraeumen ⟨a, σ.ohneSnapshot⟩ remaining) σ.spur σ.speicher

/-- `leave` at the head of a `dann` residue, by the continuation behind it. -/
def kLeave (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D (vertragVon D f) l Γ Λ → l = true →
    World D → Env D Γ → KErg D
  | _, _, _, GRest.travRest (Λ := Λ₀) _ inv _ _ k, _, σ', ρ' =>
      let σ₁ := σ'.lese Λ₀ inv.orte
      if wahr? (eval σ₁ inv σ₁ ρ'.tail) = true then kLokal st f rho ρ'.tail k σ₁.spur σ₁.speicher
      else none
  | _, _, _, GRest.verbrauchRest (Λ := Λ₀) _ _ _ inv bound mass _ _ vor k, _, σ', ρ' =>
      let σm := σ'.lese Λ₀ mass.orte
      let m' := (eval σm mass σm ρ'.tail).n
      if 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor then
        let σ₁ := σm.lese Λ₀ inv.orte
        if wahr? (eval σ₁ inv σ₁ ρ'.tail) = true then
          kLokal st f rho ρ'.tail k σ₁.spur σ'.speicher
        else none
      else none
  | _, _, _, .wiederRest _ _ _ _ k, _, σ', ρ' => kLokal st f rho ρ' k σ'.spur σ'.speicher
  | _, _, _, .ewigRest _ _ _ _ k, _, σ', ρ' => kLokal st f rho ρ' k σ'.spur σ'.speicher
  | _, _, _, GRest.dann (Λ' := Λ2) _ k, h, σ', ρ' =>
      kLokal st f rho ρ' (.dann (.cons ((.leave h) : Stmt D (vertragVon D f) _ _ Λ2 Λ2) .nil) k)
        σ'.spur σ'.speicher
  | _, _, _, GRest.schrumpf (Λ := Λ1) k, h, σ', ρ' =>
      kLokal st f rho ρ'.tail (.dann (.cons ((.leave h) : Stmt D (vertragVon D f) _ _ Λ1 Λ1) .nil) k)
        σ'.spur σ'.speicher
  | _, _, _, GRest.frei (Λ := Λ1) L k, h, σ', ρ' =>
      kLokal st f rho ρ' (.dann (.cons ((.leave h) : Stmt D (vertragVon D f) _ _ Λ1 Λ1) .nil) k)
        (.gibt L :: σ'.spur) σ'.speicher
  | _, _, _, GRest.abbruch (Λk := Λk) k, h, σ', ρ' =>
      kLokal st f rho ρ' (.dann (.cons ((.leave h) : Stmt D (vertragVon D f) _ _ Λk Λk) .nil) k)
        σ'.spur σ'.speicher
  | _, _, _, _, _, _, _ => none

/-- `next` at the head of a `dann` residue, by the continuation behind it. -/
def kNext (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D (vertragVon D f) l Γ Λ → l = true →
    World D → Env D Γ → KErg D
  | _, _, _, .travRest t inv body is k, _, σ', ρ' =>
      kLokal st f rho ρ'.tail (.trav t inv body is k) σ'.spur σ'.speicher
  | _, _, _, GRest.verbrauchRest (Λ := Λ₀) t member edge inv bound mass body rest vor k, _, σ', ρ' =>
      let σm := σ'.lese Λ₀ mass.orte
      let m' := (eval σm mass σm ρ'.tail).n
      if 0 ≤ m' ∧ m' ≤ bound ∧ m' < vor then
        kLokal st f rho ρ'.tail (.verbrauch t member edge inv bound mass body rest k)
          σm.spur σ'.speicher
      else none
  | _, _, _, .wiederRest n bis body ueber k, _, σ', ρ' =>
      kLokal st f rho ρ' (.wieder n bis body ueber k) σ'.spur σ'.speicher
  | _, _, _, .ewigRest a n inv body k, _, σ', ρ' =>
      kLokal st f rho ρ' (.ewig a n inv body k) σ'.spur σ'.speicher
  | _, _, _, GRest.dann (Λ' := Λ2) _ k, h, σ', ρ' =>
      kLokal st f rho ρ' (.dann (.cons ((.next h) : Stmt D (vertragVon D f) _ _ Λ2 Λ2) .nil) k)
        σ'.spur σ'.speicher
  | _, _, _, GRest.schrumpf (Λ := Λ1) k, h, σ', ρ' =>
      kLokal st f rho ρ'.tail (.dann (.cons ((.next h) : Stmt D (vertragVon D f) _ _ Λ1 Λ1) .nil) k)
        σ'.spur σ'.speicher
  | _, _, _, GRest.frei (Λ := Λ1) L k, h, σ', ρ' =>
      kLokal st f rho ρ' (.dann (.cons ((.next h) : Stmt D (vertragVon D f) _ _ Λ1 Λ1) .nil) k)
        (.gibt L :: σ'.spur) σ'.speicher
  | _, _, _, GRest.abbruch (Λk := Λk) k, h, σ', ρ' =>
      kLokal st f rho ρ' (.dann (.cons ((.next h) : Stmt D (vertragVon D f) _ _ Λk Λk) .nil) k)
        σ'.spur σ'.speicher
  | _, _, _, _, _, _, _ => none

/-- The outcome of a leaf in `dann` position. -/
def kAusDann (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ' Λ'' : List (Res D)}
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'') :
    Ausgang (vertragVon D f) l Γ → KErg D
  | .ok σ' ρ' => kLokal st f rho ρ' (.dann rest k) σ'.spur σ'.speicher
  | .zurueck σ v => kPop st f rho σ v
  | .why σ r => kPopGrund st f rho σ.spur σ.speicher r
  | .leave h σ' ρ' => kLeave st f rho k h σ' ρ'
  | .next h σ' ρ' => kNext st f rho k h σ' ρ'
  | _ => none

/-- The outcome of a leaf in `ende` position. -/
def kAusEnde (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ' : List (Res D)}
    (rest : Endblock D (vertragVon D f) l Γ Λ') : Ausgang (vertragVon D f) l Γ → KErg D
  | .ok σ' ρ' => kLokal st f rho ρ' (.ende rest) σ'.spur σ'.speicher
  | .zurueck σ v => kPop st f rho σ v
  | .why σ r => kPopGrund st f rho σ.spur σ.speicher r
  | _ => none


/-- Calls in `ende` position (`ruf`, `rufCallInd`). -/
def kRufEnde (P : Programm D) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ Λ' : List (Res D)} → Env D Γ →
    Stmt D (vertragVon D f) l Γ Λ Λ' → Endblock D (vertragVon D f) l Γ Λ' → KErg D
  | _, _, Λ, _, ρ, .call g args _ _, rest =>
      let s0 := (sp.welt spur).lese Λ args.orte
      kPush P st f rho ρ (.ende rest) g (evalArgs s0 args s0 ρ) s0.spur sp
  | _, _, Λ, _, ρ, .callInd p args _ _, rest =>
      let s0 := (sp.welt spur).lese Λ (p.orte ++ args.orte)
      match eval s0 p s0 ρ with
      | ⟨g, hg⟩ => kPush P st f rho ρ (.ende rest) g (umsig hg (evalArgs s0 args s0 ρ)) s0.spur sp
  | _, _, Λ, _, ρ, .retScoped e R, _ =>
      let σ := (sp.welt spur).lese Λ e.orte
      kScoped st f rho ρ (.inl (evalErg σ e σ ρ)) σ R.scopes
  | _, _, _, _, ρ, .retWhyScoped r R, _ =>
      kScoped st f rho ρ (.inr r) (sp.welt spur) R.scopes
  | _, _, _, _, _, _, _ => none

/-- Calls in `dann` position (`rufDann`, `dannCallInd`). -/
def kRufDann (P : Programm D) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ Λ' Λ'' : List (Res D)} → Env D Γ →
    Stmt D (vertragVon D f) l Γ Λ Λ' → Block D (vertragVon D f) l Γ Λ' Λ'' →
    GRest D (vertragVon D f) l Γ Λ'' → KErg D
  | _, _, Λ, _, _, ρ, .call g args _ _, rest, k =>
      let s0 := (sp.welt spur).lese Λ args.orte
      kPush P st f rho ρ (.dann rest k) g (evalArgs s0 args s0 ρ) s0.spur sp
  | _, _, Λ, _, _, ρ, .callInd p args _ _, rest, k =>
      let s0 := (sp.welt spur).lese Λ (p.orte ++ args.orte)
      match eval s0 p s0 ρ with
      | ⟨g, hg⟩ => kPush P st f rho ρ (.dann rest k) g (umsig hg (evalArgs s0 args s0 ρ)) s0.spur sp
  | _, _, Λ, _, _, ρ, .retScoped e R, _, _ =>
      let σ := (sp.welt spur).lese Λ e.orte
      kScoped st f rho ρ (.inl (evalErg σ e σ ρ)) σ R.scopes
  | _, _, _, _, _, ρ, .retWhyScoped r R, _, _ =>
      kScoped st f rho ρ (.inr r) (sp.welt spur) R.scopes
  | _, _, _, _, _, _, _, _, _ => none

/-- A compound step in `dann` position. The program and oracle keep the
    fallible calls fused into the same single push or answer step as G3. -/
def kEntf (P : Programm D) (O : Orakel D) (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ Λ' Λ'' : List (Res D)} → Env D Γ →
    Stmt D (vertragVon D f) l Γ Λ Λ' → Block D (vertragVon D f) l Γ Λ' Λ'' →
    GRest D (vertragVon D f) l Γ Λ'' → KErg D
  | _, _, Λ, _, _, ρ, .ite c t e, rest, k =>
      let σ₁ := (sp.welt spur).lese Λ c.orte
      if wahr? (eval σ₁ c σ₁ ρ) = true then kLokal st f rho ρ (.dann t (.dann rest k)) σ₁.spur sp
      else kLokal st f rho ρ (.dann e (.dann rest k)) σ₁.spur sp
  | _, _, Λ, _, _, ρ, .onOption (n := n) o p a, rest, k =>
      let σ₁ := (sp.welt spur).lese Λ o.orte
      match eval σ₁ o σ₁ ρ with
      | some v => kLokal st f rho (.cons (show Wert D (.index n) from v) ρ) (.dann p (.schrumpf (.dann rest k))) σ₁.spur sp
      | none => kLokal st f rho ρ (.dann a (.dann rest k)) σ₁.spur sp
  | _, _, Λ, _, _, ρ, .onTag v arms, rest, k =>
      let σ₁ := (sp.welt spur).lese Λ v.orte
      match armWahlG arms (eval σ₁ v σ₁ ρ) with
      | ⟨some τ, b, nutz⟩ =>
          kLokal st f rho (Γ := τ :: _) (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k)))
            σ₁.spur sp
      | ⟨none, b, nutz⟩ => kLokal st f rho (armEnv nutz ρ) (.dann b (.dann rest k)) σ₁.spur sp
  | _, _, Λ, _, _, ρ, .onWhy r arms, rest, k =>
      let σ₁ := (sp.welt spur).lese Λ r.orte
      kLokal st f rho ρ (.dann (grundWahlG arms (eval σ₁ r σ₁ ρ)) (.dann rest k)) σ₁.spur sp
  | _, _, _, _, _, ρ, .locks L _ body, rest, k =>
      kLokal st f rho ρ (.dann body (.frei L (.dann rest k))) (.nimmt L (offen spur) :: spur) sp
  | _, _, _, _, _, ρ, .breaking _ body, rest, k =>
      kLokal st f rho ρ (.dann body (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .traverse t inv body, rest, k =>
      kLokal st f rho ρ (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .consumeTraverse t member edge inv bound mass body, rest, k =>
      kLokal st f rho ρ (.verbrauch t member edge inv bound mass body
        ((D.count t).toNat + bound.toNat + 1) (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .retry n bis body ueber, rest, k =>
      kLokal st f rho ρ (.wieder n bis body ueber (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .forever a inv body, rest, k =>
      kLokal st f rho ρ (.ewig a passes inv body (.dann rest k)) spur sp
  | _, _, Λ, _, _, ρ, .callIndElse (τ := τ) (n := n) p args _ _ _ err, rest, k =>
      let s0 := (sp.welt spur).lese Λ (p.orte ++ args.orte)
      match eval s0 p s0 ρ with
      | ⟨g, hg⟩ => kPush P st f rho ρ
          (.wartetSonst (τ := τ) (D.sigNr n).gruende err .nil (.dann rest k)) g
          (umsig hg (evalArgs s0 args s0 ρ)) s0.spur sp
  | _, _, Λ, _, _, ρ, .axiomCallElse _ a args _ _ _ _ _ err, rest, k =>
      let σ₁ := (sp.welt spur).lese Λ args.orte
      match axiomAntwortSonst O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some (Sum.inl _)) => kLokal st f rho ρ (.dann rest k) σ₂.spur σ₂.speicher
      | (σ₂, some (Sum.inr r)) =>
          kLokal st f rho (Env.cons (τ := reasonTy (D.agruende a)) r ρ)
            (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σ₂.spur σ₂.speicher
      | (_, none) => none
  | _, _, _, _, _, _, _, _, _ => none


end Fn
end Gabbro.Grammatik
