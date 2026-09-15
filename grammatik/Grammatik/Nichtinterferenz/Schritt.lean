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
import Grammatik.Nichtinterferenz.Grundlagen

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

/-- A pop with a value (`rueck`, `rueckBind` and their `cons`/`dann`
    forms): the caller resumes, bound if it waits. -/
def kPop (st : List (KRahmen D)) (f : D.Fn) (σ : World D) (v : ErgVal D (vertragVon D f).erg) : KErg D :=
  match st with
  | [] => none
  | c :: rst =>
      if c.rest.2.2.2.2.wartend = true then kBinde f rst c σ v
      else some (⟨rst, c, σ.spur⟩, σ.speicher)

/-- A pop with a reason (`rueckGrund` and its forms): the caller waiting in
    `let … else` runs its else block. -/
def kPopGrund (st : List (KRahmen D)) (f : D.Fn) (spur : List (Ereignis D)) (sp : Speicher D) (r : Fin (vertragVon D f).gruende) :
    KErg D :=
  match st with
  | [] => none
  | c :: rst =>
      match c.rest with
      | ⟨l, Γ, Λ, ρc, GRest.wartetSonst n err _ k⟩ =>
          if hn : (vertragVon D f).gruende = n then
            some (⟨rst, ⟨c.f, c.rho, ⟨l, .grund n :: Γ, Λ, .cons (Fin.cast hn r) ρc,
              .dann err.alsBlock.2 (.abbruch (.schrumpf k))⟩⟩, spur⟩, sp)
          else none
      | _ => none

/-- `leave` at the head of a `dann` residue, by the continuation behind it. -/
def kLeave (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) :
    {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D (vertragVon D f) l Γ Λ → l = true →
    World D → Env D Γ → KErg D
  | _, _, _, GRest.travRest (Λ := Λ₀) _ inv _ _ k, _, σ', ρ' =>
      let σ₁ := σ'.lese Λ₀ inv.orte
      if wahr? (eval σ₁ inv σ₁ ρ'.tail) = true then kLokal st f rho ρ'.tail k σ₁.spur σ₁.speicher
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
  | .zurueck σ v => kPop st f σ v
  | .grund σ r => kPopGrund st f σ.spur σ.speicher r
  | .leave h σ' ρ' => kLeave st f rho k h σ' ρ'
  | .next h σ' ρ' => kNext st f rho k h σ' ρ'
  | _ => none

/-- The outcome of a leaf in `ende` position. -/
def kAusEnde (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ' : List (Res D)}
    (rest : Endblock D (vertragVon D f) l Γ Λ') : Ausgang (vertragVon D f) l Γ → KErg D
  | .ok σ' ρ' => kLokal st f rho ρ' (.ende rest) σ'.spur σ'.speicher
  | .zurueck σ v => kPop st f σ v
  | .grund σ r => kPopGrund st f σ.spur σ.speicher r
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
  | _, _, _, _, _, _, _, _, _ => none

/-- The compound unfolds in `dann` position. -/
def kEntf (passes : Nat) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D)) (sp : Speicher D) : {l : Bool} → {Γ : Ctx} → {Λ Λ' Λ'' : List (Res D)} → Env D Γ →
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
      | ⟨some (lo, hi), b, nutz⟩ =>
          kLokal st f rho (Γ := .int lo hi :: _) (armEnv nutz ρ) (.dann b (.schrumpf (.dann rest k)))
            σ₁.spur sp
      | ⟨none, b, nutz⟩ => kLokal st f rho (armEnv nutz ρ) (.dann b (.dann rest k)) σ₁.spur sp
  | _, _, Λ, _, _, ρ, .onGrund r arms, rest, k =>
      let σ₁ := (sp.welt spur).lese Λ r.orte
      kLokal st f rho ρ (.dann (grundWahlG arms (eval σ₁ r σ₁ ρ)) (.dann rest k)) σ₁.spur sp
  | _, _, _, _, _, ρ, .locks L _ body, rest, k =>
      kLokal st f rho ρ (.dann body (.frei L (.dann rest k))) (.nimmt L (offen spur) :: spur) sp
  | _, _, _, _, _, ρ, .breaking _ body, rest, k =>
      kLokal st f rho ρ (.dann body (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .traverse t inv body, rest, k =>
      kLokal st f rho ρ (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .retry n bis body ueber, rest, k =>
      kLokal st f rho ρ (.wieder n bis body ueber (.dann rest k)) spur sp
  | _, _, _, _, _, ρ, .forever a inv body, rest, k =>
      kLokal st f rho ρ (.ewig a passes inv body (.dann rest k)) spur sp
  | _, _, _, _, _, _, _, _, _ => none

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
  | _, _, Λ, ρ, .ret e _ =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      kPop st f σ₁ (evalErg σ₁ e σ₁ ρ)
  | _, _, _, _, .retGrund r _ => kPopGrund st f spur sp r
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
  | _, _, Λ, _, ρ, .bindCallElse g args _ _ _ err rest, k =>
      let s0 := (sp.welt spur).lese Λ args.orte
      kPush P st f rho ρ (.wartetSonst (D.gruende g) err rest k) g (evalArgs s0 args s0 ρ) s0.spur sp
  | _, _, Λ, _, ρ, .bindAxiom a args he _ _ _ _ rest, k =>
      let σ₁ := (sp.welt spur).lese Λ args.orte
      match axiomAntwort O a σ₁ (evalArgs σ₁ args σ₁ ρ) with
      | (σ₂, some v) => kLokal st f rho (.cons (ergWert he v) ρ) (.dann rest (.schrumpf k)) σ₂.spur
          σ₂.speicher
      | (_, none) => none
  | _, _, _, _, ρ, .regLies r _ rest, k =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r (sp.welt spur)) with
      | some v =>
          if D.rzusage r v = true then kLokal st f rho (.cons v ρ) (.dann rest (.schrumpf k)) spur sp
          else none
      | none => none
  | _, _, Λ, _, ρ, .regLiesElse r _ zusage sonst rest, k =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r (sp.welt spur)) with
      | some v =>
          let σ₁ := (sp.welt spur).lese Λ zusage.orte
          if wahr? (eval σ₁ zusage σ₁ (.cons v ρ)) = true then
            kLokal st f rho (.cons v ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
          else kLokal st f rho ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur sp
      | none => none
  | _, _, Λ, _, ρ, .awaits g _ _ _ rest, k =>
      if O.sichtbar g (sp.welt spur) = true then
        let σ₁ := (sp.welt spur).lese Λ [.inr g]
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
  | _, _, Λ, _, ρ, .pruefung c sonst rest, k =>
      let σ₁ := (sp.welt spur).lese Λ c.orte
      if wahr? (eval σ₁ c σ₁ ρ) = true then kLokal st f rho ρ (.dann rest k) σ₁.spur sp
      else kLokal st f rho ρ (.dann sonst.alsBlock.2 (.abbruch k)) σ₁.spur sp
  | _, _, Λ, _, ρ, .gleit op a b lo hi rest, k =>
      let σ₁ := (sp.welt spur).lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ₁ a σ₁ ρ).x (eval σ₁ b σ₁ ρ).x) with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      | none => none
  | _, _, _, _, ρ, .gleitLit q lo hi rest, k =>
      match gleitPasst lo hi (bruch q) with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) spur sp
      | none => none
  | _, _, Λ, _, ρ, .gleitVon e lo hi rest, k =>
      let σ₁ := (sp.welt spur).lese Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ₁ e σ₁ ρ).n) with
      | some v => kLokal st f rho (.cons (show Wert D (.fl lo hi) from v) ρ) (.dann rest (.schrumpf k)) σ₁.spur sp
      | none => none
  | _, _, Λ, _, ρ, .gleitNarrow e lo hi sonst rest, k =>
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
