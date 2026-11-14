/- C08: the foreign question a machine head asks, and the answer facts the replay
   consumes at that question. Below the atomic replay, so its leaves can use them. -/
module

public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.Premises

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The replay key of a foreign question, including its original arguments.
    The key has exactly one new question event, as in `AxEintrag`. -/
abbrev ForeignCallKey (D : Deklaration) :=
  Σ a : D.Ax, World D × Env D (D.aparams a)

def foreignCallKey {Γ : Ctx} {Λ : List (Res D)} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (σ : World D) (ρ : Env D Γ) :
    ForeignCallKey D :=
  let σ₁ := σ.lese Λ args.orte
  ⟨a, σ₁.fragt (.inl a), evalArgs σ₁ args σ₁ ρ⟩

/-- Only the current call is inspected; calls inside a branch or continuation
    become heads when the machine reaches them. No oracle answer is needed. -/
def Stmt.foreignCallKey {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    Option (ForeignCallKey D) :=
  match s with
  | .axiomCall a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .axiomCallElse _ a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | _ => none

def Block.foreignCallKey {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    Option (ForeignCallKey D) :=
  match b with
  | .cons s _ => s.foreignCallKey σ ρ
  | .bindAxiom a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .bindAxiomElse a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .bindAxiomOpt _ a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .bindAxiomOptElse _ a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | _ => none

def Endblock.foreignCallKey {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    Option (ForeignCallKey D) :=
  match b with
  | .cons s _ => s.foreignCallKey σ ρ
  | .bindAxiom a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .bindAxiomElse a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .bindAxiomOpt _ a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | .bindAxiomOptElse _ a args .. => some (Gabbro.Grammatik.foreignCallKey a args σ ρ)
  | _ => none

def GRest.foreignCallKey {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    Option (ForeignCallKey D) :=
  match r with
  | .ende b => b.foreignCallKey σ ρ
  | .dann b _ => b.foreignCallKey σ ρ
  | _ => none

def RufMaschineG.foreignCallKey (M : RufMaschineG D) (t : Faden) :
    Option (ForeignCallKey D) :=
  (M.faeden t).kopf.rest.2.2.2.2.foreignCallKey (M.weltVon t)
    (M.faeden t).kopf.rest.2.2.2.1

/-- A head's question read through the equation of its residue. -/
theorem foreignCallKey_sigma {V : Vertrag D}
    {x : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {g : GRest D V l Γ Λ} (h : x = ⟨l, Γ, Λ, ρ, g⟩) (W : World D) :
    x.2.2.2.2.foreignCallKey W x.2.2.2.1 = g.foreignCallKey W ρ := by
  subst h
  rfl

/-- The question of thread `u` is the question of its residue. -/
theorem RufMaschineG.foreignCallKey_rest {M : RufMaschineG D} {u : Faden} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {ρ : Env D Γ} {g : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
    (h : (M.faeden u).kopf.rest = ⟨l, Γ, Λ, ρ, g⟩) :
    M.foreignCallKey u = g.foreignCallKey (M.weltVon u) ρ :=
  foreignCallKey_sigma h (M.weltVon u)

/-- **The answer fact at a question.** Whenever the question `k` is the item `a`
    asked in the question world `σ1.fragt (.inl a)` with arguments `ρ`, every
    fitting raw answer of `O` there meets `Q`. Only the asked question matters. -/
def AntwortQF (Q : ∀ a : D.Ax, World D → ErgVal D (D.aerg a) → Bool) (O : Orakel D)
    (k : Option (ForeignCallKey D)) : Prop :=
  ∀ (a : D.Ax) (σ1 : World D) (ρ : Env D (D.aparams a)),
    k = some ⟨a, σ1.fragt (.inl a), ρ⟩ →
    ∀ v : ErgVal D (D.aerg a),
      einpassenErg O.zeiger (D.aerg a) (O.wirkt a (σ1.fragt (.inl a)) ρ).2 = some v →
        Q a (O.wirkt a (σ1.fragt (.inl a)) ρ).1 v = true

/-- The answer fact at the current question of thread `t` of machine `M`. -/
def AntwortQ (Q : ∀ a : D.Ax, World D → ErgVal D (D.aerg a) → Bool) (O : Orakel D)
    (M : RufMaschineG D) (t : Faden) : Prop :=
  AntwortQF Q O (M.foreignCallKey t)

end Gabbro.Grammatik
