/-
  File:      Grammatik/Speichermodell/AtomarSem.lean
  Subject:   THE SEQUENTIAL SEMANTICS WITH A HAVOC AT EVERY SHARED ATOMIC READ -- the "rely"
             of OFFEN O25 (Opus lane O25b, 2026-09-26). Standalone: `Zielsatz/Spec.lean` does
             not import this file.

  WHAT THE USER WOULD PROVE AGAINST. `execStmtH` (SperreSem.lean) runs a body alone; a lock
  take lets the environment move the protected carriers (`Umwelt`, `HavocOk`). On a program
  whose threads race on an UNGUARDED atomic (a flag, a counter, a per-core cell), another
  thread may change the atomic between any two reads, and machine W may even present an older
  message (`w_nicht_sc`). So a read of such an atomic may return ANY value. `execStmtHA` is
  `execStmtH` with ONE change: every read (`World.lese`, the only place a statement reads
  memory) goes through an ATOMIC ENVIRONMENT `A : AUmwelt D`, a function of the read list and
  the world after the read events, which may replace the value of every read carrier in a set
  `T` -- and nothing else (`HavocA T A`). The obligation quantifies over every such `A`
  (`KoerperGutSA`, Zielsatz/AtomarPflicht.lean): the user proves the body against every value
  another thread or the weak memory can show at a shared atomic read.

  WHY THE HAVOC SITS AT `lese`. A read list `X` of a step is recorded as read events in the
  trace, so the world after them has a trace strictly longer than any earlier one whenever `X`
  is not empty. A havoc that may change only carriers of `X` is the identity when `X` is empty
  (`HavocA`), so every POINT at which the environment may act has a fresh key -- the replay can
  record the machine's presented value there as a function of the key, as it records an
  acquire (`UEintrag`) and a callee answer.

  `awaits g` tests visibility AFTER its read of `g` here (`execStmtH` tests before): with a
  havoc the test must see the value the read returns, and under `RegLokal` (visibility depends
  on `g` only) the two orders agree (`Block.execHA_frei`).

  PROVED HERE: `leseA_frei` (a havoc over a read list outside `T` is no havoc) and the
  EMBEDDING `Stmt.execHA_frei`/`Block.execHA_frei`/`Endblock.execHA_frei`: on a body none of
  whose reads is in `T`, `execStmtHA` IS `execStmtH` for every havoc in the class; in
  particular for `T` empty or the identity havoc (`execEndHA_id`).
-/
import Grammatik.SperreSem

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
    leseA idA σ Λ X = σ.lese Λ X := rfl

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
  | .assignDurch p t _ f i e _ _, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignGlob g e _ _, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .schreibBytes t f hf n i _ _ e _ _, σ, ρ =>
      let σ := leseA A σ Λ (i.orte ++ e.orte)
      .ok (σ.schreibBytes t f hf Λ (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)) ρ
  | .assignVar x e, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .ok σ (ρ.set x (eval σ e σ ρ))
  | .uebergang t f hτ i von nach hn _ _ _, σ, ρ =>
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
  | .onGrund r arms, σ, ρ =>
      let σ := leseA A σ Λ r.orte
      execGrundHA arms (eval σ r σ ρ) σ ρ
  | .call f args _ hr, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' _ => .ok σ' ρ
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callInd p args _ hr, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' _ => .ok σ' ρ
      | .grund _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .locks L _ body, σ, ρ => freiH S L (execBlockHA body ((U L σ).nimmt L) ρ)
  | .breaking _ body, σ, ρ => execBlockHA body σ ρ
  | .traverse t inv body, σ, ρ =>
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
  | .regSchreib r _ e, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      let _ := O.regSchreib r (roh (eval σ e σ ρ))
      .ok σ ρ
  | .transition r _ m _ _ maske bits, σ, ρ =>
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
  | .retGrund r _, σ, _ => .grund σ r
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
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := leseA A σ Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlockHA rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .grund _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlockHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .grund σ' r => (execEndHA err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := leseA A σ Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlockHA rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .regLies r _ rest, σ, ρ =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlockHA rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regLiesElse r _ zusage sonst rest, σ, ρ =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := leseA A σ Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlockHA rest σ (.cons v ρ)).schrumpf
          else (execEndHA sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ rest, σ, ρ =>
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
  | .pruefung c sonst rest, σ, ρ =>
      let σ := leseA A σ Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlockHA rest σ ρ else (execEndHA sonst σ ρ).zuAusgang
  | .gleit op a b lo hi rest, σ, ρ =>
      let σ := leseA A σ Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .gleitLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .gleitVon e lo hi rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .gleitNarrow e lo hi sonst rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlockHA rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEndHA sonst σ ρ).zuAusgang

def execEndHA {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retGrund r _, σ, _ => .grund σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmtHA s σ ρ with
      | .ok σ' ρ' => execEndHA rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := leseA A σ Λ e.orte
      (execEndHA rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf

def execArmsHA {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
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

mutual

theorem Stmt.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → (∀ c ∈ stmtOrteP P s, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtHA S O U A passes R s σ ρ = execStmtH S O U passes R s σ ρ
  | .assignSlot t f i e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignDurch p t _ f i e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignGlob g e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .schreibBytes t f hf n i _ _ e _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .assignVar x e, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .uebergang t f hτ i von nach hn _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .ite c t e, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P t, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h3 : ∀ x ∈ blockOrteP P e, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1, Block.execHA_frei t h2,
        Block.execHA_frei e h3] <;> (try rfl)
  | .onOption o p a, hT, σ, ρ => by
      have h1 : ∀ x ∈ o.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P p, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h3 : ∀ x ∈ blockOrteP P a, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1, Block.execHA_frei p h2,
        Block.execHA_frei a h3] <;> (try rfl)
  | .onTag v arms, hT, σ, ρ => by
      have h1 : ∀ x ∈ v.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ armsOrteP P arms, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1, Arms.execHA_frei arms h2] <;> (try rfl)
  | .onGrund r arms, hT, σ, ρ => by
      have h1 : ∀ x ∈ r.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ grundArmsOrteP P arms, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      exact GrundArms.execHA_frei arms h2 _ _ _
  | .call f args _ hr, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1] <;> (try rfl)
  | .callInd p args _ hr, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .locks L _ body, hT, σ, ρ => by
      simp only [execStmtHA, execStmtH, Block.execHA_frei body hT] <;> (try rfl)
  | .breaking _ body, hT, σ, ρ => by
      simp only [execStmtHA, execStmtH, Block.execHA_frei body hT] <;> (try rfl)
  | .traverse t inv body, hT, σ, ρ => by
      have h1 : ∀ x ∈ inv.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
        (fun σ ρ => execBlockH S O U passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execHA_frei body h2 σ ρ]
  | .retry n bis body ueber, hT, σ, ρ => by
      have h1 : ∀ x ∈ bis.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h3 : ∀ x ∈ blockOrteP P ueber, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
          (fun σ ρ => execBlockH S O U passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execHA_frei body h2 σ ρ,
        show (fun σ ρ => execBlockHA S O U A passes R ueber σ ρ) =
          (fun σ ρ => execBlockH S O U passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execHA_frei ueber h3 σ ρ]
  | .forever a inv body, hT, σ, ρ => by
      have h1 : ∀ x ∈ inv.orte, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P body, ¬ T x := fun x h => hT x (by simp [stmtOrteP, h])
      simp only [execStmtHA, execStmtH, leseA_frei hA h1]
      rw [show (fun σ ρ => execBlockHA S O U A passes R body σ ρ) =
        (fun σ ρ => execBlockH S O U passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execHA_frei body h2 σ ρ]
  | .axiomCall a args _ _ _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .regSchreib r _ e, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .transition .., _, _, _ => rfl
  | .publish g e _ _ _ _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret e _, hT, σ, ρ => by
      simp only [stmtOrteP] at hT
      simp only [execStmtHA, execStmtH, leseA_frei hA hT] <;> (try rfl)
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → (∀ c ∈ blockOrteP P b, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockHA S O U A passes R b σ ρ = execBlockH S O U passes R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ stmtOrteP P s, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, Stmt.execHA_frei s h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bind e rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindCall f args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindCallInd p args he _ hr rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ p.orte ++ args.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .bindCallElse f args he _ _ err rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P err, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei err h3] <;> (try rfl)
  | .bindAxiom a args he _ _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ args.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .regLies r _ rest, hT, σ, ρ => by
      simp only [execBlockHA, execBlockH, Block.execHA_frei rest hT] <;> (try rfl)
  | .regLiesElse r _ zusage sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ zusage.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .awaits g _ _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ [Sum.inr g], ¬ T x := fun x h => hT x (by
        simp only [List.mem_singleton] at h; simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        sichtbar_lese hRL] <;> (try rfl)
  | .exchange g neu _ _ rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ Sum.inr g :: neu.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_cons] at h; rcases h with h | h <;> simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .narrow e lo' hi' sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .pruefung c sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ c.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)
  | .gleit op a b lo hi rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ a.orte ++ b.orte, ¬ T x := fun x h => hT x (by
        simp only [List.mem_append] at h; rcases h with h | h <;> simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .gleitLit q lo hi rest, hT, σ, ρ => by
      simp only [execBlockHA, execBlockH, Block.execHA_frei rest hT] <;> (try rfl)
  | .gleitVon e lo hi rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2] <;> (try rfl)
  | .gleitNarrow e lo hi sonst rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h2 : ∀ x ∈ blockOrteP P rest, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      have h3 : ∀ x ∈ endblockOrteP P sonst, ¬ T x := fun x h => hT x (by simp [blockOrteP, h])
      simp only [execBlockHA, execBlockH, leseA_frei hA h1, Block.execHA_frei rest h2,
        Endblock.execHA_frei sonst h3] <;> (try rfl)

theorem Endblock.execHA_frei {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → (∀ c ∈ endblockOrteP P b, ¬ T c) → ∀ (σ : World D) (ρ : Env D Γ),
      execEndHA S O U A passes R b σ ρ = execEndH S O U passes R b σ ρ
  | .ret e _, hT, σ, ρ => by
      simp only [endblockOrteP] at hT
      simp only [execEndHA, execEndH, leseA_frei hA hT] <;> (try rfl)
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ stmtOrteP P s, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, execEndH, Stmt.execHA_frei s h1, Endblock.execHA_frei rest h2] <;> (try rfl)
  | .bind e rest, hT, σ, ρ => by
      have h1 : ∀ x ∈ e.orte, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      have h2 : ∀ x ∈ endblockOrteP P rest, ¬ T x := fun x h => hT x (by simp [endblockOrteP, h])
      simp only [execEndHA, execEndH, leseA_frei hA h1, Endblock.execHA_frei rest h2] <;> (try rfl)

theorem Arms.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → (∀ c ∈ armsOrteP P a, ¬ T c) →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsHA S O U A passes R a v σ ρ = execArmsH S O U passes R a v σ ρ
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, hT, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      have h1 : ∀ x ∈ blockOrteP P b, ¬ T x := fun x h => hT x (by simp [armsOrteP, h])
      simp only [execArmsHA, execArmsH, Block.execHA_frei b h1] <;> (try rfl)
  | .cons _ rest, hT, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ => by
      have h2 : ∀ x ∈ armsOrteP P rest, ¬ T x := fun x h => hT x (by simp [armsOrteP, h])
      simp only [execArmsHA, execArmsH]
      exact Arms.execHA_frei rest h2 _ σ ρ

theorem GrundArms.execHA_frei {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → (∀ c ∈ grundArmsOrteP P a, ¬ T c) →
      ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundHA S O U A passes R a r σ ρ = execGrundH S O U passes R a r σ ρ
  | .nil, _, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, hT, ⟨0, _⟩, σ, ρ => by
      have h1 : ∀ x ∈ blockOrteP P b, ¬ T x := fun x h => hT x (by simp [grundArmsOrteP, h])
      simp only [execGrundHA, execGrundH, Block.execHA_frei b h1] <;> (try rfl)
  | .cons _ rest, hT, ⟨i + 1, h⟩, σ, ρ => by
      have h2 : ∀ x ∈ grundArmsOrteP P rest, ¬ T x := fun x h => hT x (by simp [grundArmsOrteP, h])
      simp only [execGrundHA, execGrundH]
      exact GrundArms.execHA_frei rest h2 _ σ ρ

end

end Frei

/-- **The identity environment is no havoc**: with it the semantics is `execStmtH`, on every
    body (visibility local, `RegLokal`'s second half). -/
theorem execEndHA_id (P : Programm D) (S : SperrInv D) (O : Orakel D) (U : Umwelt D)
    (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
    (hRL : ∀ (g : D.Glob) (σ σ' : World D), GleichAuf [Sum.inr g] σ σ' →
      O.sichtbar g σ = O.sichtbar g σ')
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    execEndHA S O U idA passes R b σ ρ = execEndH S O U passes R b σ ρ :=
  Endblock.execHA_frei P S O U idA passes R (T := fun _ => False) (havocA_id _) hRL b
    (fun _ _ h => h) σ ρ

#print axioms Gabbro.Grammatik.leseA_frei
#print axioms Gabbro.Grammatik.Endblock.execHA_frei
#print axioms Gabbro.Grammatik.execEndHA_id

end Gabbro.Grammatik
