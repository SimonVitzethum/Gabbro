module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The atomic environment -/

/-- **An atomic environment**: the world a read of the list `X` continues from, as a function of
    `X` and the world after the read events. -/
abbrev AUmwelt (D : Deklaration) := List (D.Tab ⊕ D.Glob) → World D → World D

/-- **The class of atomic environments over the set `T`**: the trace stays, and only carriers
    that are READ (in `X`) AND in `T` may change. -/
def HavocA (T : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) : Prop :=
  ∀ X σ, (A X σ).spur = σ.spur ∧ ∀ c, ¬ (c ∈ X ∧ T c) → TraegerGleich (A X σ).speicher σ.speicher c

/-- A read through the atomic environment. -/
def leseA (A : AUmwelt D) (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    World D :=
  A X (σ.lese Λ X)

/-- The identity environment. -/
def idA : AUmwelt D := fun _ σ => σ

theorem havocA_id (T : D.Tab ⊕ D.Glob → Prop) : HavocA T (idA (D := D)) :=
  fun _ _ => ⟨rfl, fun c _ => traegerGleich_refl _ c⟩

theorem havocA_mono {T T' : D.Tab ⊕ D.Glob → Prop} (h : ∀ c, T c → T' c) {A : AUmwelt D}
    (hA : HavocA T A) : HavocA T' A :=
  fun X σ => ⟨(hA X σ).1, fun c hc => (hA X σ).2 c fun ⟨h1, h2⟩ => hc ⟨h1, h (c) h2⟩⟩

/-- **A read of carriers outside `T` is no havoc.** -/
theorem leseA_frei {T : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T A)
    {X : List (D.Tab ⊕ D.Glob)} (hX : ∀ c ∈ X, ¬ T c) (σ : World D) (Λ : List (Res D)) :
    leseA A σ Λ X = σ.lese Λ X :=
  world_ext (fun c => (hA X (σ.lese Λ X)).2 c fun ⟨h1, h2⟩ => hX c h1 h2) (hA X _).1

theorem leseA_id (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    leseA idA σ Λ X = σ.lese Λ X := by rfl

theorem leseA_spur (A : AUmwelt D) {T : D.Tab ⊕ D.Glob → Prop} (hA : HavocA T A) (σ : World D)
    (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) : (leseA A σ Λ X).spur = (σ.lese Λ X).spur :=
  (hA X _).1

/-! ## 2. The semantics -/

section RumpfA

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

mutual

/-- **`execStmt` with lock invariants**: every form as in `execStmt`, but
    `locks L { body }` runs the body from the environment's move `U L` of
    the acquire world and releases through the check `freiH`. -/
def execStmtHA {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .assignSlot t f i e _ _, σ, ρ =>
      let σ := leseA A σ Λ (i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignThru p t _ f i e _ _, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignSlotRef r t _ _ f e _ _, σ, ρ =>
      let σ := leseA A σ Λ (r.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ ((eval σ r σ ρ).zelle : Int) f (eval σ e σ ρ)) ρ
  | .assignGlob g e _ _, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .putBytes t f hf n i _ _ e _ _, σ, ρ =>
      let σ := leseA A σ Λ (i.orte ++ e.orte)
      .ok (σ.schreibBytes t f hf Λ (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)) ρ
  | .assignVar x e, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .ok σ (ρ.set x (eval σ e σ ρ))
  | .shift t f hτ i von nach hn _ _ _, σ, ρ =>
      let σ := leseA A σ Λ (.inl t :: i.orte)
      let k := (eval σ i σ ρ).n
      if (hτ ▸ σ.slots t k f : Zahl _ _).n = von
      then .ok (σ.schreibSlot t Λ k f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ
      else .logik .vorzustand
  | .ite c t e, σ, ρ =>
      let σ := leseA A σ Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlockHA t σ ρ else execBlockHA e σ ρ
  | .onOption o p a, σ, ρ =>
      let σ := leseA A σ Λ o.orte
      match eval σ o σ ρ with
      | Option.some k => (execBlockHA p σ (.cons k ρ)).schrumpf
      | Option.none => execBlockHA a σ ρ
  | .onTag v arms, σ, ρ =>
      let σ := leseA A σ Λ v.orte
      execArmsHA arms (eval σ v σ ρ) σ ρ
  | .onWhy r arms, σ, ρ =>
      let σ := leseA A σ Λ r.orte
      execGrundHA arms (eval σ r σ ρ) σ ρ
  | .call f args _ hr, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' _ => .ok σ' ρ
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callInd p args _ hr, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' _ => .ok σ' ρ
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .locks L _ body, σ, ρ => freiH S L (execBlockHA body ((U L σ).nimmt L) ρ)
  | .breaking _ body, σ, ρ => execBlockHA body σ ρ
  | .traverse t inv body, σ, ρ =>
      traverseLauf (fun σ ρ => execBlockHA body σ ρ)
        (fun σ ρ => let σ := leseA A σ Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (alleIndizes (D.count t)) σ ρ
  | .consumeTraverse t _ _ inv _ _ body, σ, ρ =>
      traverseLauf (fun σ ρ => execBlockHA body σ ρ)
        (fun σ ρ => let σ := leseA A σ Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (alleIndizes (D.count t)) σ ρ
  | .retry n bis body ueberlauf, σ, ρ =>
      retryLauf (fun σ ρ => execBlockHA body σ ρ)
        (fun σ ρ => let σ := leseA A σ Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        (fun σ ρ => execBlockHA ueberlauf σ ρ) n σ ρ
  | .forever a inv body, σ, ρ =>
      foreverLauf a (fun σ ρ => execBlockHA body σ ρ)
        (fun σ ρ => let σ := leseA A σ Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) passes σ ρ
  | .axiomCall a args _ _ _ _ _, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some _) => .ok σ' ρ
      | (_, Option.none) => .hardware (.annahme a)
  | .regWrite r _ e, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      let _ := O.regSchreib r (roh (eval σ e σ ρ))
      .ok σ ρ
  | .transition r _ m _ _ maske bits, σ, ρ =>
      let σ := σ.fragt (.inr (.inl m))
      let alt := O.regLies m σ
      let _ := O.regSchreib r (((alt.toNat &&& (Nat.xor maske.toNat (2 ^ 64 - 1))) ||| bits.toNat : Nat) : Int)
      .ok σ ρ
  | .publish g e _ _ _ _, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .advances _ _ _ _, σ, ρ => .ok σ ρ
  | .retires _ _ _ _, σ, ρ => .ok σ ρ
  | .ret e _, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retWhy r _, σ, _ => .why σ r
  | .retScoped e _, σ, ρ => let σ := leseA A σ Λ e.orte; .zurueck σ (evalErg σ e σ ρ)
  | .retWhyScoped r _, σ, _ => .why σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ

def execBlockHA {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .nil, σ, ρ => .ok σ ρ
  | .cons s rest, σ, ρ =>
      match execStmtHA s σ ρ with
      | .ok σ' ρ' => execBlockHA rest σ' ρ'
      | o => o
  | .bind e rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      (execBlockHA rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlockHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlockHA rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlockHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEndHA err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlockHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execBlockHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEndHA err σ' (.cons r ρ)).schrumpf.zuAusgang
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlockHA rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := leseA A σ Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlockHA rest σ (.cons v ρ)).schrumpf
          else (execEndHA sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inr g))
      let σ := leseA A σ Λ [.inr g]
      if O.sichtbar g σ then
        (execBlockHA rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := leseA A σ Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execBlockHA rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlockHA rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else (execEndHA sonst σ ρ).zuAusgang
  | .narrowRequired e lo' hi' rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlockHA rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else .logik .kapazitaet
  | .check c sonst rest, σ, ρ =>
      let σ := leseA A σ Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlockHA rest σ ρ else (execEndHA sonst σ ρ).zuAusgang
  | .float op a b lo hi rest, σ, ρ =>
      let σ := leseA A σ Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatOf e lo hi rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatNarrow e lo hi sonst rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEndHA sonst σ ρ).zuAusgang

def execEndHA {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retWhy r _, σ, _ => .why σ r
  | .retScoped e _, σ, ρ => let σ := leseA A σ Λ e.orte; .zurueck σ (evalErg σ e σ ρ)
  | .retWhyScoped r _, σ, _ => .why σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmtHA s σ ρ with
      | .ok σ' ρ' => execEndHA rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .why σ' r => .why σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      (execEndHA rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEndHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEndHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEndHA err σ' (.cons r ρ)).schrumpf
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execEndHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execEndHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEndHA err σ' (.cons r ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execEndHA rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := leseA A σ Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execEndHA rest σ (.cons v ρ)).schrumpf
          else (execEndHA sonst σ ρ)
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inr g))
      let σ := leseA A σ Λ [.inr g]
      if O.sichtbar g σ then
        (execEndHA rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execEndHA rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execEndHA rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else (execEndHA sonst σ ρ)
  | .narrowRequired e lo' hi' rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execEndHA rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else .logik .kapazitaet
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := leseA A σ Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execEndHA rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .ite c t e, σ, ρ =>
      let σ := leseA A σ Λ c.orte
      if wahr? (eval σ c σ ρ) then execEndHA t σ ρ else execEndHA e σ ρ

def execArmsHA {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => (execBlockHA b σ (armEnv nutz ρ)).schrumpfArm _
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsHA rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

def execGrundHA {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨0, _⟩, σ, ρ => execBlockHA b σ ρ
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => execGrundHA rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end RumpfA
/-- Visibility does not see the read events of a step (`RegLokal`'s second half). -/
theorem sichtbar_lese {O : Orakel D}
    (hRL : ∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
      O.sichtbar g σ = O.sichtbar g σ')
    (g : D.Glob) (σ : World D) (Λ : List (Res D)) (X : List (D.Tab ⊕ D.Glob)) :
    O.sichtbar g (σ.lese Λ X) = O.sichtbar g σ :=
  hRL g _ _ ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## 3. The embedding: reads outside `T` see no havoc -/

section Frei

set_option linter.unusedSectionVars false

variable (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (A : AUmwelt D)
  (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {T : D.Tab ⊕ D.Glob → Prop} (hA : HavocA T A)
  (hRL : ∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
    O.sichtbar g σ = O.sichtbar g σ')
include hA hRL

end Frei
end Gabbro.Grammatik
