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
import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz

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

/-- The same with only the locality half of `SperrInvOk` (the guard half is
    not used): a satisfiable, local family has a move in the class. -/
theorem havocOk_misch_lokal {S : SperrInv D}
    (hS : ∀ L (s s' : Speicher D), (∀ c ∈ S.orte L, TraegerGleich s s' c) →
      S.inv L s = S.inv L s')
    (quelle : D.Lock → World D → Speicher D) (hq : ∀ L σ, S.inv L (quelle L σ) = true) :
    HavocOk S (fun L σ => mischU S L σ (quelle L σ)) :=
  fun L σ => ⟨rfl, mischU_aussen S L σ _,
    (hS L _ _ fun c hc => mischU_innen S L σ _ c hc).trans (hq L σ)⟩

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
  | .why σ r => .why (σ.gibt L) r
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
  | .assignThru p t _ f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignSlotRef r t _ _ f e _ _, σ, ρ =>
      let σ := σ.lese Λ (r.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ ((eval σ r σ ρ).zelle : Int) f (eval σ e σ ρ)) ρ
  | .assignGlob g e _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .putBytes t f hf n i _ _ e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibBytes t f hf Λ (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)) ρ
  | .assignVar x e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok σ (ρ.set x (eval σ e σ ρ))
  | .shift t f hτ i von nach hn _ _ _, σ, ρ =>
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
  | .onWhy r arms, σ, ρ =>
      let σ := σ.lese Λ r.orte
      execGrundH arms (eval σ r σ ρ) σ ρ
  | .call f args _ hr, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' _ => .ok σ' ρ
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callInd p args _ hr, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' _ => .ok σ' ρ
      | .why _ r => keinGrundSig hf hr r
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
  | .regWrite r _ e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let _ := O.regSchreib r (roh (eval σ e σ ρ))
      .ok σ ρ
  | .transition r _ m _ _ maske bits, σ, ρ =>
      let σ := σ.fragt (.inr (.inl m))
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
  | .retWhy r _, σ, _ => .why σ r
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
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlockH rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlockH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEndH err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlockH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execBlockH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEndH err σ' (.cons r ρ)).schrumpf.zuAusgang
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlockH rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlockH rest σ (.cons v ρ)).schrumpf
          else (execEndH sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inr g))
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
  | .check c sonst rest, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlockH rest σ ρ else (execEndH sonst σ ρ).zuAusgang
  | .float op a b lo hi rest, σ, ρ =>
      let σ := σ.lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatOf e lo hi rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatNarrow e lo hi sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlockH rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEndH sonst σ ρ).zuAusgang

def execEndH {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retWhy r _, σ, _ => .why σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmtH s σ ρ with
      | .ok σ' ρ' => execEndH rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .why σ' r => .why σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execEndH rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEndH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEndH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEndH err σ' (.cons r ρ)).schrumpf
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execEndH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execEndH rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEndH err σ' (.cons r ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execEndH rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execEndH rest σ (.cons v ρ)).schrumpf
          else (execEndH sonst σ ρ)
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inr g))
      if O.sichtbar g σ then
        let σ := σ.lese Λ [.inr g]
        (execEndH rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execEndH rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e

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


end Gabbro.Grammatik
