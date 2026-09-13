/-
  File:      Grammatik/SperreSem.lean
  Subject:   LOCK INVARIANTS -- the sequential semantics a user proves a body
             against when shared state is protected by `locks L { … }` blocks
             (verdict item 2, `messung/URTEIL-OPUS-2026-09-13.md`).

  The shape is that of concurrent separation logic / Owicki-Gries resource
  invariants. A lock `L` protects a list of carriers `S.orte L` (each guarded
  by `L`) and carries an invariant `S.inv L` over them. In the SEQUENTIAL
  semantics of this file (`execStmtH`):
  * ACQUIRE: `locks L { body }` first lets the environment move (`U L`, an
    arbitrary `Umwelt` in the class `HavocOk S`): the protected carriers of
    `L` may take any values at which `S.inv L` holds, everything else and the
    trace stay. The body is then run from there.
  * RELEASE: when the body ends (normally, or by `leave`/`next`), `S.inv L`
    must hold; otherwise the run ends in `logik schleife` -- the invariant of
    the lock is checked at its boundary like a loop invariant.
  The user obligation stays a per-function SEQUENTIAL triple: it quantifies
  over the environment moves as it quantifies over call handlers and
  oracles (`KoerperGutS`, `SperreBeweis.lean`), and "no `logik` outcome"
  (the `KeineLogik` clause of `ziel_ort_ganz`) now also says "every release
  re-establishes the invariant".

  With the empty family (`SperrInv.leer`: no protected carriers, invariant
  `true`) every environment move is the identity and the semantics IS
  `execStmt` (`execStmtH_leer`), so today's theorem is the special case.

  This file: the family and its well-formedness (`SperrInvOk`), the class of
  environment moves (`HavocOk`), the semantics and its frame semantics
  (`weiterH`/`semH`) with the residue step lemmas, one per rule of G (copies
  of `ZielOrtVollSem.lean` §5 and `ZielOrtGeraetSem.lean` §6 for the new
  semantics, plus the acquire and release lemmas).
-/
import Grammatik.ZielOrtGanz

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Lock invariants and environment moves -/

/-- **A family of lock invariants.** `orte L`: the carriers the lock `L`
    protects for its invariant (each guarded by `L`, `SperrInvOk`);
    `inv L`: the invariant, over memory. -/
structure SperrInv (D : Deklaration) where
  orte : D.Lock → List (D.Tab ⊕ D.Glob)
  inv : D.Lock → Speicher D → Bool

/-- Well-formedness of a family: every protected carrier is guarded by its
    lock, and the invariant reads only the protected carriers. The first
    half is decidable per declaration; the second holds by construction for
    an invariant written as an expression over those carriers. -/
def SperrInvOk (S : SperrInv D) : Prop :=
  (∀ L c, c ∈ S.orte L → Bewacht c L) ∧
  (∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) → S.inv L s = S.inv L s')

/-- The empty family: no protected carriers, invariant `true`. -/
def SperrInv.leer (D : Deklaration) : SperrInv D := ⟨fun _ => [], fun _ _ => true⟩

theorem sperrInvOk_leer : SperrInvOk (SperrInv.leer D) :=
  ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ _ _ _ => rfl⟩

/-- An environment move at an acquire: the world the body of `locks L`
    starts in, as a function of the world at the acquire. -/
abbrev Umwelt (D : Deklaration) := D.Lock → World D → World D

/-- **The class of environment moves.** At an acquire of `L` the other
    threads may have changed exactly the carriers `L` protects, leaving
    `S.inv L` true (they released `L` with it); the trace is the thread's
    own. -/
def HavocOk (S : SperrInv D) (U : Umwelt D) : Prop :=
  ∀ L σ, (U L σ).spur = σ.spur ∧
    (∀ c, c ∉ S.orte L → TraegerGleich (U L σ).speicher σ.speicher c) ∧
    S.inv L (U L σ).speicher = true

/-- Membership of a carrier in a carrier list, as a Boolean. -/
def istIn (l : List (D.Tab ⊕ D.Glob)) (c : D.Tab ⊕ D.Glob) : Bool :=
  l.any fun c' => decide (c' = c)

theorem istIn_iff {l : List (D.Tab ⊕ D.Glob)} {c : D.Tab ⊕ D.Glob} : istIn l c = true ↔ c ∈ l := by
  unfold istIn
  constructor
  · intro h
    obtain ⟨c', hc', he⟩ := List.any_eq_true.mp h
    rw [← of_decide_eq_true he]
    exact hc'
  · intro h
    exact List.any_eq_true.mpr ⟨c, h, decide_eq_true rfl⟩

/-- A world with the protected carriers of `L` taken from `s` and everything
    else (the trace included) from `σ`. -/
def mischU (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D) : World D :=
  ⟨fun t => if istIn (S.orte L) (.inl t) = true then s.slots t else σ.slots t,
   fun g => if istIn (S.orte L) (.inr g) = true then s.globs g else σ.globs g, σ.spur⟩

theorem mischU_spur (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D) :
    (mischU S L σ s).spur = σ.spur := rfl

theorem mischU_aussen (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D)
    (c : D.Tab ⊕ D.Glob) (hc : c ∉ S.orte L) :
    TraegerGleich (mischU S L σ s).speicher σ.speicher c := by
  cases c with
  | inl t => exact if_neg (fun h => hc (istIn_iff.mp h))
  | inr g => exact if_neg (fun h => hc (istIn_iff.mp h))

theorem mischU_innen (S : SperrInv D) (L : D.Lock) (σ : World D) (s : Speicher D)
    (c : D.Tab ⊕ D.Glob) (hc : c ∈ S.orte L) :
    TraegerGleich (mischU S L σ s).speicher s c := by
  cases c with
  | inl t => exact if_pos (istIn_iff.mpr hc)
  | inr g => exact if_pos (istIn_iff.mpr hc)

theorem mischU_inv {S : SperrInv D} (hS : SperrInvOk S) (L : D.Lock) (σ : World D)
    (s : Speicher D) : S.inv L (mischU S L σ s).speicher = S.inv L s :=
  hS.2 L _ _ fun c hc => mischU_innen S L σ s c hc

/-- The moves `mischU` with an invariant-satisfying source are in the class. -/
theorem havocOk_misch {S : SperrInv D} (hS : SperrInvOk S) (quelle : D.Lock → World D → Speicher D)
    (hq : ∀ L σ, S.inv L (quelle L σ) = true) :
    HavocOk S (fun L σ => mischU S L σ (quelle L σ)) :=
  fun L σ => ⟨rfl, mischU_aussen S L σ _, (mischU_inv hS L σ _).trans (hq L σ)⟩

/-- Two worlds that agree on every carrier and on the trace are equal. -/
theorem world_ext {σ σ' : World D} (h : ∀ c, TraegerGleich σ.speicher σ'.speicher c)
    (hs : σ.spur = σ'.spur) : σ = σ' := by
  cases σ with
  | mk sl gl sp =>
    cases σ' with
    | mk sl' gl' sp' =>
      have e1 : sl = sl' := funext fun t => h (.inl t)
      have e2 : gl = gl' := funext fun g => h (.inr g)
      simp only at hs
      subst e1 e2 hs
      rfl

/-- Over the empty family every move in the class is the identity. -/
theorem havocOk_leer {U : Umwelt D} (h : HavocOk (SperrInv.leer D) U) : ∀ L σ, U L σ = σ :=
  fun L σ => world_ext (fun c => (h L σ).2.1 c (fun hc => absurd hc List.not_mem_nil)) (h L σ).1

/-! ## 2. The semantics with acquire moves and release checks -/

section Frei

variable {V : Vertrag D}

/-- **The release of `L`**: a normal end, a `leave` or a `next` of the body
    checks the invariant of `L` and releases the lock; a failed check is
    `logik schleife`. (A `return` or a reason cannot leave a `locks` body --
    `ret` is untypable there --; they only release.) -/
def freiH (S : SperrInv D) (L : D.Lock) {l : Bool} {Γ : Ctx} : Ausgang V l Γ → Ausgang V l Γ
  | .ok σ ρ => if S.inv L σ.speicher = true then .ok (σ.gibt L) ρ else .logik .schleife
  | .leave h σ ρ => if S.inv L σ.speicher = true then .leave h (σ.gibt L) ρ else .logik .schleife
  | .next h σ ρ => if S.inv L σ.speicher = true then .next h (σ.gibt L) ρ else .logik .schleife
  | .zurueck σ v => .zurueck (σ.gibt L) v
  | .grund σ r => .grund (σ.gibt L) r
  | .logik e => .logik e
  | .hardware e => .hardware e

/-- Under the invariant `true` the release is the plain release. -/
theorem freiH_leer (L : D.Lock) {l : Bool} {Γ : Ctx} (o : Ausgang V l Γ) :
    freiH (SperrInv.leer D) L o = o.mapWelt (·.gibt L) := by
  cases o <;> rfl

end Frei

section Rumpf

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

mutual

/-- **`execStmt` with lock invariants**: every form as in `execStmt`, but
    `locks L { body }` runs the body from the environment's move `U L` of
    the acquire world and releases through the check `freiH`. -/
def execStmtH {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Stmt D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .assignSlot t f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignDurch p t _ f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignGlob g e _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .schreibBytes t f hf n i _ _ e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibBytes t f hf Λ (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)) ρ
  | .assignVar x e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok σ (ρ.set x (eval σ e σ ρ))
  | .uebergang t f hτ i von nach hn _ _ _, σ, ρ =>
      let σ := σ.lese Λ (.inl t :: i.orte)
      let k := (eval σ i σ ρ).n
      if (hτ ▸ σ.slots t k f : Zahl _ _).n = von
      then .ok (σ.schreibSlot t Λ k f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ
      else .logik .vorzustand
  | .ite c t e, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlockH t σ ρ else execBlockH e σ ρ
  | .onOption o p a, σ, ρ =>
      let σ := σ.lese Λ o.orte
      match eval σ o σ ρ with
      | Option.some k => (execBlockH p σ (.cons k ρ)).schrumpf
      | Option.none => execBlockH a σ ρ
  | .onTag v arms, σ, ρ =>
      let σ := σ.lese Λ v.orte
      execArmsH arms (eval σ v σ ρ) σ ρ
  | .onGrund r arms, σ, ρ =>
      let σ := σ.lese Λ r.orte
      execGrundH arms (eval σ r σ ρ) σ ρ
  | .call f args _ hr, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' _ => .ok σ' ρ
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callInd p args _ hr, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' _ => .ok σ' ρ
      | .grund _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .locks L _ body, σ, ρ => freiH S L (execBlockH body ((U L σ).nimmt L) ρ)
  | .breaking _ body, σ, ρ => execBlockH body σ ρ
  | .traverse t inv body, σ, ρ =>
      traverseLauf (fun σ ρ => execBlockH body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (alleIndizes (D.count t)) σ ρ
  | .retry n bis body ueberlauf, σ, ρ =>
      retryLauf (fun σ ρ => execBlockH body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        (fun σ ρ => execBlockH ueberlauf σ ρ) n σ ρ
  | .forever a inv body, σ, ρ =>
      foreverLauf a (fun σ ρ => execBlockH body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) passes σ ρ
  | .axiomCall a args _ _ _ _ _, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some _) => .ok σ' ρ
      | (_, Option.none) => .hardware (.annahme a)
  | .regSchreib r _ e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let _ := O.regSchreib r (roh (eval σ e σ ρ))
      .ok σ ρ
  | .transition r _ m _ _ maske bits, σ, ρ =>
      let alt := O.regLies m σ
      let _ := O.regSchreib r (((alt.toNat &&& (Nat.xor maske.toNat (2 ^ 64 - 1))) ||| bits.toNat : Nat) : Int)
      .ok σ ρ
  | .publish g e _ _ _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .advances _ _ _ _, σ, ρ => .ok σ ρ
  | .retires _ _ _ _, σ, ρ => .ok σ ρ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retGrund r _, σ, _ => .grund σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ

def execBlockH {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    Block D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .nil, σ, ρ => .ok σ ρ
  | .cons s rest, σ, ρ =>
      match execStmtH s σ ρ with
      | .ok σ' ρ' => execBlockH rest σ' ρ'
      | o => o
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execBlockH rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlockH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .grund _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlockH rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .grund _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlockH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .grund σ' r => (execEndH err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlockH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .regLies r _ rest, σ, ρ =>
      match einpassen (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlockH rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regLiesElse r _ zusage sonst rest, σ, ρ =>
      match einpassen (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlockH rest σ (.cons v ρ)).schrumpf
          else (execEndH sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ rest, σ, ρ =>
      if O.sichtbar g σ then
        let σ := σ.lese Λ [.inr g]
        (execBlockH rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := σ.lese Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execBlockH rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlockH rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else (execEndH sonst σ ρ).zuAusgang
  | .pruefung c sonst rest, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlockH rest σ ρ else (execEndH sonst σ ρ).zuAusgang
  | .gleit op a b lo hi rest, σ, ρ =>
      let σ := σ.lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => .hardware .ieee
  | .gleitLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => .hardware .ieee
  | .gleitVon e lo hi rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (Float.ofInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => .hardware .ieee
  | .gleitNarrow e lo hi sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEndH sonst σ ρ).zuAusgang

def execEndH {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retGrund r _, σ, _ => .grund σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmtH s σ ρ with
      | .ok σ' ρ' => execEndH rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .grund σ' r => .grund σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execEndH rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf

def execArmsH {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => (execBlockH b σ (armEnv nutz ρ)).schrumpfArm _
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArmsH rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

def execGrundH {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨0, _⟩, σ, ρ => execBlockH b σ ρ
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => execGrundH rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Rumpf

/-! ### Over the empty family the semantics is `execStmt` -/

section Leer

set_option linter.unusedSectionVars false

variable (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  (hU : ∀ L σ, U L σ = σ)
include hU

mutual

theorem Stmt.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtH (SperrInv.leer D) O U passes R s σ ρ = execStmt O passes R s σ ρ
  | .ite c t e, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer t, Block.execH_leer e] <;> rfl
  | .onOption o p a, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer p, Block.execH_leer a] <;> rfl
  | .onTag v arms, σ, ρ => by
      simp only [execStmtH, execStmt, Arms.execH_leer arms] <;> rfl
  | .onGrund r arms, σ, ρ => by
      simp only [execStmtH, execStmt]
      exact GrundArms.execH_leer arms _ _ _
  | .locks L hr body, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer body, hU, freiH_leer] <;> rfl
  | .breaking i body, σ, ρ => by
      simp only [execStmtH, execStmt, Block.execH_leer body] <;> rfl
  | .traverse t inv body, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_leer body σ ρ]
  | .retry n bis body ueber, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
          (fun σ ρ => execBlock O passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_leer body σ ρ,
        show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R ueber σ ρ) =
          (fun σ ρ => execBlock O passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_leer ueber σ ρ]
  | .forever a inv body, σ, ρ => by
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH (SperrInv.leer D) O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_leer body σ ρ]
  | .assignSlot .., _, _ => rfl
  | .assignDurch .., _, _ => rfl
  | .assignGlob .., _, _ => rfl
  | .schreibBytes .., _, _ => rfl
  | .assignVar .., _, _ => rfl
  | .uebergang .., _, _ => rfl
  | .call .., _, _ => rfl
  | .callInd .., _, _ => rfl
  | .axiomCall .., _, _ => rfl
  | .regSchreib .., _, _ => rfl
  | .transition .., _, _ => rfl
  | .publish .., _, _ => rfl
  | .advances .., _, _ => rfl
  | .retires .., _, _ => rfl
  | .ret .., _, _ => rfl
  | .retGrund .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl

theorem Block.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockH (SperrInv.leer D) O U passes R b σ ρ = execBlock O passes R b σ ρ
  | .nil, _, _ => rfl
  | .cons s rest, σ, ρ => by
      simp only [execBlockH, execBlock, Stmt.execH_leer s, Block.execH_leer rest] <;> rfl
  | .bind e rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindCall f args he hp hr rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .bindCallElse f args he hp hr err rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer err] <;> rfl
  | .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .regLies r hk rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .regLiesElse r hk zusage sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .awaits g payload hp hL rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .exchange g neu hw hL rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .pruefung c sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl
  | .gleit op a b lo hi rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .gleitLit q lo hi rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .gleitVon e lo hi rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest] <;> rfl
  | .gleitNarrow e lo hi sonst rest, σ, ρ => by
      simp only [execBlockH, execBlock, Block.execH_leer rest, Endblock.execH_leer sonst] <;> rfl

theorem Endblock.execH_leer {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → ∀ (σ : World D) (ρ : Env D Γ),
      execEndH (SperrInv.leer D) O U passes R b σ ρ = execEnd O passes R b σ ρ
  | .ret .., _, _ => rfl
  | .retGrund .., _, _ => rfl
  | .leave .., _, _ => rfl
  | .next .., _, _ => rfl
  | .cons s rest, σ, ρ => by
      simp only [execEndH, execEnd, Stmt.execH_leer s, Endblock.execH_leer rest] <;> rfl
  | .bind e rest, σ, ρ => by
      simp only [execEndH, execEnd, Endblock.execH_leer rest] <;> rfl

theorem Arms.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsH (SperrInv.leer D) O U passes R a v σ ρ = execArms O passes R a v σ ρ
  | .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [execArmsH, execArms, Block.execH_leer b] <;> rfl
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArmsH, execArms]
      exact Arms.execH_leer rest _ σ ρ

theorem GrundArms.execH_leer {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundH (SperrInv.leer D) O U passes R a r σ ρ = execGrund O passes R a r σ ρ
  | .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, ⟨0, _⟩, σ, ρ => by
      simp only [execGrundH, execGrund, Block.execH_leer b] <;> rfl
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => by
      simp only [execGrundH, execGrund]
      exact GrundArms.execH_leer rest _ σ ρ

end

end Leer

/-! ### A body without `locks` means the same in both semantics -/

section Ohne

variable {V : Vertrag D}

mutual

/-- The statement contains no `locks` block. -/
def Stmt.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.ohneLocks && e.ohneLocks
  | .onOption _ p a => p.ohneLocks && a.ohneLocks
  | .onTag _ arms => arms.ohneLocks
  | .onGrund _ arms => arms.ohneLocks
  | .locks .. => false
  | .breaking _ body => body.ohneLocks
  | .traverse _ _ body => body.ohneLocks
  | .retry _ _ body ueber => body.ohneLocks && ueber.ohneLocks
  | .forever _ _ body => body.ohneLocks
  | _ => true

def Block.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.ohneLocks && rest.ohneLocks
  | .bind _ rest => rest.ohneLocks
  | .bindCall _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallInd _ _ _ _ _ rest => rest.ohneLocks
  | .bindCallElse _ _ _ _ _ err rest => err.ohneLocks && rest.ohneLocks
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.ohneLocks
  | .regLies _ _ rest => rest.ohneLocks
  | .regLiesElse _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .awaits _ _ _ _ rest => rest.ohneLocks
  | .exchange _ _ _ _ rest => rest.ohneLocks
  | .narrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .pruefung _ sonst rest => sonst.ohneLocks && rest.ohneLocks
  | .gleit _ _ _ _ _ rest => rest.ohneLocks
  | .gleitLit _ _ _ rest => rest.ohneLocks
  | .gleitVon _ _ _ rest => rest.ohneLocks
  | .gleitNarrow _ _ _ sonst rest => sonst.ohneLocks && rest.ohneLocks

def Endblock.ohneLocks {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → Bool
  | .cons s rest => s.ohneLocks && rest.ohneLocks
  | .bind _ rest => rest.ohneLocks
  | _ => true

def Arms.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.ohneLocks && rest.ohneLocks

def GrundArms.ohneLocks {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.ohneLocks && rest.ohneLocks

end

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

mutual

theorem Stmt.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.ohneLocks = true → ∀ (σ : World D) (ρ : Env D Γ),
      execStmtH S O U passes R s σ ρ = execStmt O passes R s σ ρ
  | .ite c t e, h, σ, ρ => by
      simp only [Stmt.ohneLocks, Bool.and_eq_true] at h
      simp only [execStmtH, execStmt, Block.execH_ohne t h.1, Block.execH_ohne e h.2] <;> rfl
  | .onOption o p a, h, σ, ρ => by
      simp only [Stmt.ohneLocks, Bool.and_eq_true] at h
      simp only [execStmtH, execStmt, Block.execH_ohne p h.1, Block.execH_ohne a h.2] <;> rfl
  | .onTag v arms, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      exact Arms.execH_ohne arms h _ _ _
  | .onGrund r arms, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      exact GrundArms.execH_ohne arms h _ _ _
  | .locks .., h, _, _ => by simp [Stmt.ohneLocks] at h
  | .breaking i body, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt, Block.execH_ohne body h]
  | .traverse t inv body, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH S O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_ohne body h σ ρ]
  | .retry n bis body ueber, h, σ, ρ => by
      simp only [Stmt.ohneLocks, Bool.and_eq_true] at h
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH S O U passes R body σ ρ) =
          (fun σ ρ => execBlock O passes R body σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_ohne body h.1 σ ρ,
        show (fun σ ρ => execBlockH S O U passes R ueber σ ρ) =
          (fun σ ρ => execBlock O passes R ueber σ ρ) from
            funext fun σ => funext fun ρ => Block.execH_ohne ueber h.2 σ ρ]
  | .forever a inv body, h, σ, ρ => by
      simp only [Stmt.ohneLocks] at h
      simp only [execStmtH, execStmt]
      rw [show (fun σ ρ => execBlockH S O U passes R body σ ρ) =
        (fun σ ρ => execBlock O passes R body σ ρ) from
          funext fun σ => funext fun ρ => Block.execH_ohne body h σ ρ]
  | .assignSlot .., _, _, _ => rfl
  | .assignDurch .., _, _, _ => rfl
  | .assignGlob .., _, _, _ => rfl
  | .schreibBytes .., _, _, _ => rfl
  | .assignVar .., _, _, _ => rfl
  | .uebergang .., _, _, _ => rfl
  | .call .., _, _, _ => rfl
  | .callInd .., _, _, _ => rfl
  | .axiomCall .., _, _, _ => rfl
  | .regSchreib .., _, _, _ => rfl
  | .transition .., _, _, _ => rfl
  | .publish .., _, _, _ => rfl
  | .advances .., _, _, _ => rfl
  | .retires .., _, _, _ => rfl
  | .ret .., _, _, _ => rfl
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl

theorem Block.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.ohneLocks = true → ∀ (σ : World D) (ρ : Env D Γ),
      execBlockH S O U passes R b σ ρ = execBlock O passes R b σ ρ
  | .nil, _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Stmt.execH_ohne s h.1, Block.execH_ohne rest h.2] <;> rfl
  | .bind e rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h]
  | .bindCall f args he hp hr rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .bindCallInd p args he hp hr rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .bindCallElse f args he hp hr err rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne err h.1] <;> rfl
  | .bindAxiom a args he hw hg hd hgd rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .regLies r hk rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .regLiesElse r hk zusage sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .awaits g payload hp hL rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .exchange g neu hw hL rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h]
  | .narrow e lo' hi' sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .pruefung c sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl
  | .gleit op a b lo hi rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .gleitLit q lo hi rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .gleitVon e lo hi rest, h, σ, ρ => by
      simp only [Block.ohneLocks] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h] <;> rfl
  | .gleitNarrow e lo hi sonst rest, h, σ, ρ => by
      simp only [Block.ohneLocks, Bool.and_eq_true] at h
      simp only [execBlockH, execBlock, Block.execH_ohne rest h.2, Endblock.execH_ohne sonst h.1] <;>
        rfl

theorem Endblock.execH_ohne {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (b : Endblock D V l Γ Λ) → b.ohneLocks = true → ∀ (σ : World D) (ρ : Env D Γ),
      execEndH S O U passes R b σ ρ = execEnd O passes R b σ ρ
  | .ret .., _, _, _ => rfl
  | .retGrund .., _, _, _ => rfl
  | .leave .., _, _, _ => rfl
  | .next .., _, _, _ => rfl
  | .cons s rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks, Bool.and_eq_true] at h
      simp only [execEndH, execEnd, Stmt.execH_ohne s h.1, Endblock.execH_ohne rest h.2] <;> rfl
  | .bind e rest, h, σ, ρ => by
      simp only [Endblock.ohneLocks] at h
      simp only [execEndH, execEnd, Endblock.execH_ohne rest h]

theorem Arms.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} :
    (a : Arms D V l Γ Λ Λ' cs) → a.ohneLocks = true →
      ∀ (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
      execArmsH S O U passes R a v σ ρ = execArms O passes R a v σ ρ
  | .nil, _, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, h, ⟨⟨0, _⟩, nutz⟩, σ, ρ => by
      simp only [Arms.ohneLocks, Bool.and_eq_true] at h
      simp only [execArmsH, execArms, Block.execH_ohne b h.1]
  | .cons _ rest, h, ⟨⟨i + 1, hi⟩, nutz⟩, σ, ρ => by
      simp only [Arms.ohneLocks, Bool.and_eq_true] at h
      simp only [execArmsH, execArms]
      exact Arms.execH_ohne rest h.2 _ σ ρ

theorem GrundArms.execH_ohne {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → a.ohneLocks = true → ∀ (r : Fin n) (σ : World D) (ρ : Env D Γ),
      execGrundH S O U passes R a r σ ρ = execGrund O passes R a r σ ρ
  | .nil, _, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | .cons b _, h, ⟨0, _⟩, σ, ρ => by
      simp only [GrundArms.ohneLocks, Bool.and_eq_true] at h
      simp only [execGrundH, execGrund, Block.execH_ohne b h.1]
  | .cons _ rest, h, ⟨i + 1, hi⟩, σ, ρ => by
      simp only [GrundArms.ohneLocks, Bool.and_eq_true] at h
      simp only [execGrundH, execGrund]
      exact GrundArms.execH_ohne rest h.2 _ σ ρ

end

end Ohne

/-- **A leaf means the same in both semantics** (a leaf contains no `locks`). -/
theorem execStmtH_blatt (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D} {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true)
    (σ : World D) (ρ : Env D Γ) :
    execStmtH S O U passes R s σ ρ = execStmt O passes R s σ ρ := by
  cases s <;> first | rfl | (simp [Stmt.istBlatt] at hb)

/-! ## 3. The frame semantics of every residue, with lock invariants

  `weiterH`/`semH` are `weiterZ`/`semV` (`ZielOrtVollSem.lean`) over
  `execStmtH`; the one new case is the release marker `frei L`, which runs
  the release check `freiH`. -/

section Weiter

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- **How a residue continues from an outcome**, with lock invariants. -/
def weiterH : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ →
    Ausgang V l Γ → ZErg V
  | _, _, _, .ende e, o =>
      match o with
      | .ok σ ρ => zErg (execEndH S O U passes R e σ ρ)
      | .zurueck σ v => .zurueck σ v
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .dann b k, o => weiterH k (laufA (fun σ ρ => execBlockH S O U passes R b σ ρ) o)
  | _, _, _, .schrumpf k, o => weiterH k o.schrumpf
  | _, _, _, .frei L k, o => weiterH k (freiH S L o)
  | _, _, _, .trav _ inv body ks k, o =>
      weiterH k (laufA (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) ks) o)
  | _, _, _, .travRest _ inv body ks k, o =>
      match o with
      | .ok σ ρ =>
          weiterH k (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) ks σ
            ρ.tail)
      | .next _ σ ρ =>
          weiterH k (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) ks σ
            ρ.tail)
      | .leave _ σ ρ =>
          weiterH k (if (leseB inv σ ρ.tail).2 = true then .ok (leseB inv σ ρ.tail).1 ρ.tail
            else .logik .schleife)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .grund σ r => weiterH k (.grund σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, _, .wieder n bis body ueber k, o =>
      weiterH k (laufA (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ) n) o)
  | _, _, _, .wiederRest n bis body ueber k, o =>
      match o with
      | .ok σ ρ => weiterH k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
          (fun σ ρ => execBlockH S O U passes R ueber σ ρ) n σ ρ)
      | .next _ σ ρ => weiterH k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ)
          (leseB bis) (fun σ ρ => execBlockH S O U passes R ueber σ ρ) n σ ρ)
      | .leave _ σ ρ => weiterH k (.ok σ ρ)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .grund σ r => weiterH k (.grund σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, _, .ewig a n inv body k, o =>
      weiterH k (laufA (foreverLauf a (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) n) o)
  | _, _, _, .ewigRest a n inv body k, o =>
      match o with
      | .ok σ ρ => weiterH k (foreverLauf a (fun σ ρ => execBlockH S O U passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .next _ σ ρ => weiterH k (foreverLauf a (fun σ ρ => execBlockH S O U passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .leave _ σ ρ => weiterH k (.ok σ ρ)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .grund σ r => weiterH k (.grund σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, _, .wartet _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterH k o
  | _, _, _, .wartetSonst _ _ _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterH k o

/-- The frame semantics of a residue with lock invariants: run it from `σ`,
    `ρ`. -/
def semH {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : ZErg V :=
  weiterH S O U passes R r (.ok σ ρ)

variable {l : Bool} {Γ : Ctx}

theorem execBlockH_cons_laufA {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ : World D) (ρ : Env D Γ) :
    execBlockH S O U passes R (.cons s rest) σ ρ =
      laufA (fun σ ρ => execBlockH S O U passes R rest σ ρ) (execStmtH S O U passes R s σ ρ) := by
  simp only [execBlockH]
  cases execStmtH S O U passes R s σ ρ <;> rfl

theorem semH_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann b k) σ ρ =
      weiterH S O U passes R k (execBlockH S O U passes R b σ ρ) := rfl

theorem semH_dann_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons s rest) k) σ ρ =
      weiterH S O U passes R (.dann rest k) (execStmtH S O U passes R s σ ρ) := by
  rw [semH_dann, execBlockH_cons_laufA]
  rfl

theorem weiterH_logik : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Logik D), weiterH S O U passes R k (.logik e) = .logik e
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterH_logik k e
  | _, _, _, .schrumpf k, e => weiterH_logik k e
  | _, _, _, .frei _ k, e => weiterH_logik k e
  | _, _, _, .trav _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .wartet _ k, e => weiterH_logik k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterH_logik k e

theorem weiterH_zurueck : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (v : ErgVal D V.erg),
    (weiterH S O U passes R k (.zurueck σ v)).gleich (.zurueck σ v)
  | _, _, _, .ende _, _, _ => ZErg.gleich_refl _
  | _, _, _, .dann _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .schrumpf k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .frei L k, σ, v =>
      ZErg.gleich_trans (weiterH_zurueck k (σ.gibt L) v) ⟨sg_gibt σ L, rfl⟩
  | _, _, _, .trav _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .travRest _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wieder _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wiederRest _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .ewig _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .ewigRest _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wartet _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wartetSonst _ _ _ k, σ, v => weiterH_zurueck k σ v

/-- **An end block replacing a residue** (as `weiterZ_ende_folgt`). -/
theorem weiterH_ende_folgt {Λ : List (Res D)} (k : GRest D V l Γ Λ) (eo : EndAusgang V l Γ) :
    (weiterH S O U passes R k eo.zuAusgang).folgt (zErg eo) := by
  cases eo with
  | zurueck σ v => exact ZErg.folgt_of_gleich (weiterH_zurueck S O U passes R k σ v)
  | logik e => exact ZErg.folgt_of_eq (weiterH_logik S O U passes R k e)
  | _ => exact ZErg.folgt_sonst _

/-- `execArmsH` runs the arm `armWahlG` selects. -/
theorem execArmsH_wahl {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option (Int × Int))} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
      (σ : World D) (ρ : Env D Γ),
    execArmsH S O U passes R arms v σ ρ =
      (execBlockH S O U passes R (armWahlG arms v).2.1 σ
        (armEnv (armWahlG arms v).2.2 ρ)).schrumpfArm (armWahlG arms v).1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArmsH, armWahlG]
      exact execArmsH_wahl rest _ σ ρ

/-- `execGrundH` runs the arm `grundWahlG` selects. -/
theorem execGrundH_wahl {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrundH S O U passes R arms r σ ρ = execBlockH S O U passes R (grundWahlG arms r) σ ρ
  | _, .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨k + 1, h⟩, σ, ρ => by
      simp only [execGrundH, grundWahlG]
      exact execGrundH_wahl rest _ σ ρ

theorem execGrundH_wahlW {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n)
    (r : Wert D (.grund n)) (σ : World D) (ρ : Env D Γ) :
    execGrundH S O U passes R arms r σ ρ = execBlockH S O U passes R (grundWahlG arms r) σ ρ :=
  execGrundH_wahl S O U passes R arms r σ ρ

end Weiter

/-! ## 4. The residue step lemmas, one per rule of G -/

section Stufen

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}
  {l : Bool} {Γ : Ctx}

theorem semH_ende_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende (.cons s rest)) σ ρ =
      weiterH S O U passes R (.ende rest) (execStmtH S O U passes R s σ ρ) := by
  show zErg (execEndH S O U passes R (.cons s rest) σ ρ) = _
  simp only [execEndH]
  cases execStmtH S O U passes R s σ ρ <;> rfl

theorem laufAH_nil {Λ : List (Res D)} (o : Ausgang V l Γ) :
    laufA (fun σ ρ => execBlockH S O U passes R (.nil : Block D V l Γ Λ Λ) σ ρ) o = o := by
  cases o <;> rfl

theorem semH_endeEntf {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Endblock D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende (.cons s rest)) σ ρ =
      semH S O U passes R (.dann (.cons s .nil) (.ende rest)) σ ρ := by
  rw [semH_ende_cons, semH_dann_cons]
  show _ = weiterH S O U passes R (.ende rest) (laufA _ _)
  rw [laufAH_nil]

theorem semH_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann .nil k) σ ρ = semH S O U passes R k σ ρ := rfl

theorem semH_ite {Λ Λ' Λ'' : List (Res D)} (c : Expr D Γ Λ .bool)
    (t e : Block D V l Γ Λ Λ') (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) (b : Bool)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = b) :
    semH S O U passes R (.dann (.cons (.ite c t e) rest) k) σ ρ =
      semH S O U passes R (.dann (if b then t else e) (.dann rest k)) (σ.lese Λ c.orte) ρ := by
  rw [semH_dann_cons]
  cases b <;> simp only [execStmtH, hw] <;> rfl

theorem semH_optSome {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (.index n))
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.some v) :
    semH S O U passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semH S O U passes R (.dann p (.schrumpf (.dann rest k))) (σ.lese Λ o.orte) (.cons v ρ) := by
  rw [semH_dann_cons]
  simp only [execStmtH, hv]
  rfl

theorem semH_optNone {Λ Λ' Λ'' : List (Res D)} {n : Int} (o : Expr D Γ Λ (.opt n))
    (p : Block D V l (.index n :: Γ) Λ Λ') (a : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (hv : eval (σ.lese Λ o.orte) o (σ.lese Λ o.orte) ρ = Option.none) :
    semH S O U passes R (.dann (.cons (.onOption o p a) rest) k) σ ρ =
      semH S O U passes R (.dann a (.dann rest k)) (σ.lese Λ o.orte) ρ := by
  rw [semH_dann_cons]
  simp only [execStmtH, hv]
  rfl

theorem semH_tagSome {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (lo hi : Int) (b : Block D V l (.int lo hi :: Γ) Λ Λ') (nutz : Nutzlast (some (lo, hi)))
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) =
      ⟨some (lo, hi), b, nutz⟩) :
    semH S O U passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semH S O U passes R (.dann b (.schrumpf (.dann rest k))) (σ.lese Λ v.orte)
        (armEnv nutz ρ) := by
  rw [semH_dann_cons]
  simp only [execStmtH]
  rw [execArmsH_wahl, hw]
  rfl

theorem semH_tagNone {Λ Λ' Λ'' : List (Res D)} {cs : List (Option (Int × Int))}
    (v : Expr D Γ Λ (.sum cs)) (arms : Arms D V l Γ Λ Λ' cs)
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ)
    (b : Block D V l Γ Λ Λ') (nutz : Nutzlast none)
    (hw : armWahlG arms (eval (σ.lese Λ v.orte) v (σ.lese Λ v.orte) ρ) = ⟨none, b, nutz⟩) :
    semH S O U passes R (.dann (.cons (.onTag v arms) rest) k) σ ρ =
      semH S O U passes R (.dann b (.dann rest k)) (σ.lese Λ v.orte) (armEnv nutz ρ) := by
  rw [semH_dann_cons]
  simp only [execStmtH]
  rw [execArmsH_wahl, hw]
  rfl

theorem semH_grund {Λ Λ' Λ'' : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.grund n))
    (arms : GrundArms D V l Γ Λ Λ' n) (rest : Block D V l Γ Λ' Λ'')
    (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.onGrund r arms) rest) k) σ ρ =
      semH S O U passes R (.dann (grundWahlG arms (eval (σ.lese Λ r.orte) r (σ.lese Λ r.orte) ρ))
        (.dann rest k)) (σ.lese Λ r.orte) ρ := by
  rw [semH_dann_cons]
  simp only [execStmtH]
  rw [execGrundH_wahlW S O U passes R arms]
  rfl

theorem semH_breaking {Λ Λ' Λ'' : List (Res D)} (i : D.Inv) (body : Block D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.breaking i body) rest) k) σ ρ =
      semH S O U passes R (.dann body (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

/-- **The acquire**: the body runs from the environment's move of the
    acquire world, and the release marker `frei L` carries the release
    check. -/
theorem semH_locks {Λ Λ'' : List (Res D)} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
    (body : Block D V l Γ (Res.held L :: Λ) (Res.held L :: Λ))
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.locks L hr body) rest) k) σ ρ =
      semH S O U passes R (.dann body (.frei L (.dann rest k))) ((U L σ).nimmt L) ρ := by
  rw [semH_dann_cons]
  rfl

/-- **The release**, where the invariant holds. -/
theorem semH_frei {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) (hi : S.inv L σ.speicher = true) :
    semH S O U passes R (.frei L k) σ ρ = semH S O U passes R k (σ.gibt L) ρ := by
  show weiterH S O U passes R k (freiH S L (.ok σ ρ)) = _
  simp only [freiH, hi, if_true]
  rfl

/-- **A release where the invariant fails predicts `logik schleife`.** -/
theorem semH_frei_falsch {Λ : List (Res D)} (L : D.Lock) (k : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) (hi : S.inv L σ.speicher = false) :
    semH S O U passes R (.frei L k) σ ρ = .logik .schleife := by
  show weiterH S O U passes R k (freiH S L (.ok σ ρ)) = _
  simp only [freiH, hi, Bool.false_eq_true, if_false]
  exact weiterH_logik S O U passes R k _

theorem semH_schrumpf {Λ : List (Res D)} {τ : Ty} (k : GRest D V l Γ Λ) (σ : World D)
    (v : Wert D τ) (ρ : Env D Γ) :
    semH S O U passes R (.schrumpf k) σ (.cons v ρ) = semH S O U passes R k σ ρ := rfl

theorem semH_endeBind {Λ : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Endblock D V l (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende (.bind e rest)) σ ρ =
      semH S O U passes R (.ende rest) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := by
  show zErg (execEndH S O U passes R (.bind e rest) σ ρ) =
    zErg (execEndH S O U passes R rest _ _)
  simp only [execEndH]
  rw [zErg_schrumpf]

theorem semH_dannBind {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ)
    (rest : Block D V l (τ :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.bind e rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) := rfl

theorem semH_narrowOk {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semH S O U passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (Env.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) := by
  rw [semH_dann]
  simp only [execBlockH, dif_pos h]
  rfl

theorem semH_narrowElse {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    (lo' hi' : Int) (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    (semH S O U passes R (.dann (.narrow e lo' hi' sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.ende sonst) (σ.lese Λ e.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, dif_neg h]
  exact weiterH_ende_folgt S O U passes R k _

theorem semH_pruefWahr {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    semH S O U passes R (.dann (.pruefung c sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest k) (σ.lese Λ c.orte) ρ := by
  rw [semH_dann]
  simp only [execBlockH, hw, if_true]
  rfl

theorem semH_pruefFalsch {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = false) :
    (semH S O U passes R (.dann (.pruefung c sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.ende sonst) (σ.lese Λ c.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hw, Bool.false_eq_true, if_false]
  exact weiterH_ende_folgt S O U passes R k _

theorem semH_exchange {Λ Λ' : List (Res D)} (g : D.Glob)
    (neuE : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
    (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.exchange g neuE hw hL rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k))
        ((σ.lese Λ (.inr g :: neuE.orte)).schreibGlob g Λ
          (eval (σ.lese Λ (.inr g :: neuE.orte)) neuE (σ.lese Λ (.inr g :: neuE.orte))
            (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ)))
        (.cons ((σ.lese Λ (.inr g :: neuE.orte)).globs g) ρ) := rfl

theorem semH_gleit {Λ Λ' : List (Res D)} {l₁ h₁ l₂ h₂ : Int × Int} (op : GleitOp)
    (a : Expr D Γ Λ (.fl l₁ h₁)) (b : Expr D Γ Λ (.fl l₂ h₂)) (lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (gleitRechne op
      (eval (σ.lese Λ (a.orte ++ b.orte)) a (σ.lese Λ (a.orte ++ b.orte)) ρ).x
      (eval (σ.lese Λ (a.orte ++ b.orte)) b (σ.lese Λ (a.orte ++ b.orte)) ρ).x) = some v) :
    semH S O U passes R (.dann (.gleit op a b lo hi rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ (a.orte ++ b.orte)) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitLit {Λ Λ' : List (Res D)} (q lo hi : Int × Int)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi)) (hv : gleitPasst lo hi (bruch q) = some v) :
    semH S O U passes R (.dann (.gleitLit q lo hi rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitVon {Λ Λ' : List (Res D)} {l₁ h₁ : Int} (e : Expr D Γ Λ (.int l₁ h₁))
    (lo hi : Int × Int) (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (Float.ofInt (eval (σ.lese Λ e.orte) e
      (σ.lese Λ e.orte) ρ).n) = some v) :
    semH S O U passes R (.dann (.gleitVon e lo hi rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitNarrowOk {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ) (v : Wert D (.fl lo hi))
    (hv : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = some v) :
    semH S O U passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv]
  rfl

theorem semH_gleitNarrowElse {Λ Λ' : List (Res D)} {l₁ h₁ : Int × Int}
    (e : Expr D Γ Λ (.fl l₁ h₁)) (lo hi : Int × Int) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (.fl lo hi :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D)
    (ρ : Env D Γ)
    (hn : gleitPasst lo hi (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).x = none) :
    (semH S O U passes R (.dann (.gleitNarrow e lo hi sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.ende sonst) (σ.lese Λ e.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hn]
  exact weiterH_ende_folgt S O U passes R k _

/-! ### Loops -/

theorem semH_dannTrav {Λ Λ'' : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.traverse t inv body) rest) k) σ ρ =
      semH S O U passes R (.trav t inv body (alleIndizes (D.count t)) (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_travNext {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (i : Wert D (.index (D.count t))) (is : List (Wert D (.index (D.count t))))
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.trav t inv body (i :: is) k) σ ρ =
      semH S O U passes R (.dann body (.travRest t inv body is k)) (σ.lese Λ inv.orte)
        (.cons i ρ) := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (traverseLauf _ _ (i :: is) σ ρ) =
    weiterH S O U passes R (.travRest t inv body is k)
      (execBlockH S O U passes R body (leseB inv σ ρ).1 (.cons i ρ))
  simp only [traverseLauf, hl, Bool.true_eq_false, if_false]
  cases execBlockH S O U passes R body (leseB inv σ ρ).1 (.cons i ρ) <;> rfl

theorem semH_travFort {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.travRest t inv body is k) σ (.cons i ρ) =
      semH S O U passes R (.trav t inv body is k) σ ρ := rfl

theorem semH_travDone {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.trav t inv body [] k) σ ρ =
      semH S O U passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ)
    (leseB inv) [] σ ρ) = weiterH S O U passes R k (.ok _ ρ)
  simp only [traverseLauf, hl, if_true]
  rfl

theorem semH_dannRetry {Λ Λ'' : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ)
    (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.retry n bis body ueber) rest) k) σ ρ =
      semH S O U passes R (.wieder n bis body ueber (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

/-- A block `.nil` in front of a residue changes nothing. -/
theorem weiterH_dannLeer {Λ : List (Res D)} (k : GRest D V l Γ Λ) (o : Ausgang V l Γ) :
    weiterH S O U passes R (.dann .nil k) o = weiterH S O U passes R k o := by
  cases o <;> rfl

/-- The spent `retry` (corrected 2026-09-13): `if bis {} else { overflow }`. -/
theorem semH_wiederUeber {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.wieder 0 bis body ueber k) σ ρ =
      semH S O U passes R (.dann (.cons (.ite bis .nil ueber) .nil) k) σ ρ := by
  cases hb : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) with
  | true =>
      rw [semH_ite S O U passes R bis .nil ueber .nil k σ ρ true hb]
      show weiterH S O U passes R k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseB bis σ ρ).2 = true := hb
      simp only [retryLauf, hl, if_true]
      rfl
  | false =>
      rw [semH_ite S O U passes R bis .nil ueber .nil k σ ρ false hb]
      show weiterH S O U passes R k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ) 0 σ ρ) = _
      have hl : (leseB bis σ ρ).2 = false := hb
      simp only [retryLauf, hl, Bool.false_eq_true, if_false]
      show _ = weiterH S O U passes R (.dann .nil k) (execBlockH S O U passes R ueber (leseB bis σ ρ).1 ρ)
      rw [weiterH_dannLeer]

theorem semH_wiederWeiter {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = true) :
    semH S O U passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semH S O U passes R k (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = true := hw
  show weiterH S O U passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterH S O U passes R k (.ok _ ρ)
  simp only [retryLauf, hl, if_true]
  rfl

theorem semH_wiederSchritt {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false) :
    semH S O U passes R (.wieder (n + 1) bis body ueber k) σ ρ =
      semH S O U passes R (.dann body (.wiederRest n bis body ueber k)) (σ.lese Λ bis.orte) ρ := by
  have hl : (leseB bis σ ρ).2 = false := hw
  show weiterH S O U passes R k (retryLauf _ _ _ (n + 1) σ ρ) =
    weiterH S O U passes R (.wiederRest n bis body ueber k)
      (execBlockH S O U passes R body (leseB bis σ ρ).1 ρ)
  simp only [retryLauf, hl, Bool.false_eq_true, if_false]
  cases execBlockH S O U passes R body (leseB bis σ ρ).1 ρ <;> rfl

theorem semH_wiederFort {Λ : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.wiederRest n bis body ueber k) σ ρ =
      semH S O U passes R (.wieder n bis body ueber k) σ ρ := rfl

theorem semH_dannForever {Λ Λ'' : List (Res D)} (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons (.forever a inv body) rest) k) σ ρ =
      semH S O U passes R (.ewig a passes inv body (.dann rest k)) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_ewigWeiter {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.ewig a (n + 1) inv body k) σ ρ =
      semH S O U passes R (.dann body (.ewigRest a n inv body k)) (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  show weiterH S O U passes R k (foreverLauf a _ _ (n + 1) σ ρ) =
    weiterH S O U passes R (.ewigRest a n inv body k)
      (execBlockH S O U passes R body (leseB inv σ ρ).1 ρ)
  simp only [foreverLauf, hl, Bool.true_eq_false, if_false]
  cases execBlockH S O U passes R body (leseB inv σ ρ).1 ρ <;> rfl

theorem semH_ewigFort {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ewigRest a n inv body k) σ ρ =
      semH S O U passes R (.ewig a n inv body k) σ ρ := rfl

/-! ### The exits `leave` and `next` -/

theorem semH_leaveTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true) :
    semH S O U passes R (.dann (.cons (.leave h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semH S O U passes R k (σ.lese Λ inv.orte) ρ := by
  have hl : (leseB inv σ ρ).2 = true := hw
  rw [semH_dann_cons]
  show weiterH S O U passes R k (if (leseB inv σ ρ).2 = true then _ else _) = _
  rw [if_pos hl]
  rfl

theorem semH_nextTrav {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.next h) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      semH S O U passes R (.trav t inv body is k) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_leaveWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.leave h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semH S O U passes R k σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_nextWieder {Λ Λx : List (Res D)} (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueber : Block D V l Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.next h) rest) (.wiederRest n bis body ueber k)) σ ρ =
      semH S O U passes R (.wieder n bis body ueber k) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_leaveEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.leave h) rest) (.ewigRest a n inv body k)) σ ρ =
      semH S O U passes R k σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_nextEwig {Λ Λx : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ)
    (rest : Block D V true Γ Λx Λ) (σ : World D) (ρ : Env D Γ) (h : true = true) :
    semH S O U passes R (.dann (.cons (.next h) rest) (.ewigRest a n inv body k)) σ ρ =
      semH S O U passes R (.ewig a n inv body k) σ ρ := by
  rw [semH_dann_cons]
  rfl

theorem semH_peelDann {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)}
    (rest : Block D V true Γ Λ Λ1) (b : Block D V true Γ Λ1 Λ2) (k : GRest D V true Γ Λ2)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.dann b k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x <;> rfl

theorem semH_peelSchrumpf {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty}
    (rest : Block D V true (τ :: Γ) Λ Λ1) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D (τ :: Γ)) (h : true = true) (x : Bool) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.schrumpf k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) σ ρ.tail := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x <;> rfl

/-- **A `leave`/`next` out of a `locks` body releases through the check.** -/
theorem semH_peelFrei {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) (hi : S.inv L σ.speicher = true) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      semH S O U passes R (.dann (.cons (if x then .leave h else .next h) .nil) k) (σ.gibt L) ρ := by
  rw [semH_dann_cons, semH_dann_cons]
  cases x
  · show weiterH S O U passes R k (freiH S L (.next h σ ρ)) =
      weiterH S O U passes R k (.next h (σ.gibt L) ρ)
    simp only [freiH, hi, if_true]
  · show weiterH S O U passes R k (freiH S L (.leave h σ ρ)) =
      weiterH S O U passes R k (.leave h (σ.gibt L) ρ)
    simp only [freiH, hi, if_true]

/-- **A `leave`/`next` out of a `locks` body where the invariant fails
    predicts `logik schleife`.** -/
theorem semH_peelFrei_falsch {Γ : Ctx} {Λ Λ1 : List (Res D)} (L : D.Lock)
    (rest : Block D V true Γ Λ (Res.held L :: Λ1)) (k : GRest D V true Γ Λ1)
    (σ : World D) (ρ : Env D Γ) (h : true = true) (x : Bool) (hi : S.inv L σ.speicher = false) :
    semH S O U passes R (.dann (.cons (if x then .leave h else .next h) rest) (.frei L k)) σ ρ =
      .logik .schleife := by
  rw [semH_dann_cons]
  cases x
  · show weiterH S O U passes R k (freiH S L (.next h σ ρ)) = _
    simp only [freiH, hi, Bool.false_eq_true, if_false]
    exact weiterH_logik S O U passes R k _
  · show weiterH S O U passes R k (freiH S L (.leave h σ ρ)) = _
    simp only [freiH, hi, Bool.false_eq_true, if_false]
    exact weiterH_logik S O U passes R k _

/-! ### Returns -/

theorem semH_rueck {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.ende (.ret (l := l) e hperm)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) :=
  ZErg.gleich_refl _

theorem semH_rueckCons {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hperm : Λ.Perm V.ende)
    (rest : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.ende (.cons (.ret e hperm) rest)) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semH_ende_cons]
  exact ZErg.gleich_refl _

theorem semH_dannRet {Λ Λ'' : List (Res D)} (e : ErgExpr D Γ Λ V.erg)
    (hperm : Λ.Perm V.ende) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ'')
    (σ : World D) (ρ : Env D Γ) :
    (semH S O U passes R (.dann (.cons (.ret e hperm) rest) k) σ ρ).gleich
      (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := by
  rw [semH_dann_cons]
  exact weiterH_zurueck S O U passes R (.dann rest k) _ _

/-! ### The device forms -/

theorem semH_regLies {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (O.regLies r σ) = some v)
    (hz : D.rzusage r v = true) :
    semH S O U passes R (.dann (.regLies r hk rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) σ (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv, hz, if_true]
  rfl

theorem semH_regLiesElseWahr {Λ Λ' : List (Res D)} (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (O.regLies r σ) = some v)
    (hw : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = true) :
    semH S O U passes R (.dann (.regLiesElse r hk zusage sonst rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ zusage.orte) (.cons v ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv, hw, if_true]
  rfl

theorem semH_regLiesElseFalsch {Λ Λ' : List (Res D)} (r : D.Reg)
    (hk : (D.rklasse r).lesbar = true)
    (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l (D.rtyp r :: Γ) Λ Λ') (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ)
    (v : Wert D (D.rtyp r)) (hv : einpassen (D.rtyp r) (O.regLies r σ) = some v)
    (hw : wahr? (eval (σ.lese Λ zusage.orte) zusage (σ.lese Λ zusage.orte) (.cons v ρ)) = false) :
    (semH S O U passes R (.dann (.regLiesElse r hk zusage sonst rest) k) σ ρ).folgt
      (semH S O U passes R (.ende sonst) (σ.lese Λ zusage.orte) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hv, hw, Bool.false_eq_true, if_false]
  exact weiterH_ende_folgt S O U passes R k _

theorem semH_awaits {Λ Λ' : List (Res D)} (g : D.Glob) (payload : List D.Glob)
    (hp : payload = D.nutzlast g) (hL : gdarf D g Λ) (rest : Block D V l (D.gtyp g :: Γ) Λ Λ')
    (k : GRest D V l Γ Λ') (σ : World D) (ρ : Env D Γ) (hvis : O.sichtbar g σ = true) :
    semH S O U passes R (.dann (.awaits g payload hp hL rest) k) σ ρ =
      semH S O U passes R (.dann rest (.schrumpf k)) (σ.lese Λ [.inr g])
        (.cons ((σ.lese Λ [.inr g]).globs g) ρ) := by
  rw [semH_dann]
  simp only [execBlockH, hvis, if_true]
  rfl

/-! ### The checks of G, failing -/

theorem semH_trav_falsch {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (ks : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semH S O U passes R (.trav t inv body ks k) σ ρ = .logik .schleife := by
  cases ks with
  | nil =>
      simp only [semH, weiterH, laufA, traverseLauf, leseB, hw]
      exact weiterH_logik S O U passes R k _
  | cons i is =>
      simp only [semH, weiterH, laufA, traverseLauf, leseB, hw]
      exact weiterH_logik S O U passes R k _

theorem semH_ewig_falsch {Λ : List (Res D)} (a : D.Annahme) (n : Nat) (inv : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (k : GRest D V l Γ Λ) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semH S O U passes R (.ewig a (n + 1) inv body k) σ ρ = .logik .schleife := by
  simp only [semH, weiterH, laufA, foreverLauf, leseB, hw]
  exact weiterH_logik S O U passes R k _

theorem semH_leaveTrav_falsch {Λ Λx : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t) :: Γ) Λ Λ)
    (is : List (Wert D (.index (D.count t)))) (k : GRest D V l Γ Λ)
    (rest : Block D V true (.index (D.count t) :: Γ) Λx Λ) (hl : true = true)
    (i : Wert D (.index (D.count t))) (σ : World D) (ρ : Env D Γ)
    (hw : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false) :
    semH S O U passes R (.dann (.cons (.leave hl) rest) (.travRest t inv body is k)) σ (.cons i ρ) =
      .logik .schleife := by
  rw [semH_dann_cons]
  show weiterH S O U passes R (.travRest t inv body is k) (.leave hl σ (.cons i ρ)) = _
  simp only [weiterH, leseB, Env.tail, hw]
  exact weiterH_logik S O U passes R k _

end Stufen

end Gabbro.Grammatik
