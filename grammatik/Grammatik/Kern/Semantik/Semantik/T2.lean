/- Part 2 of 2 of `Semantik` (split by instrumente/teile/lean-teilen.py; the umbrella `Semantik.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Semantik.T1

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D}

/-- `retry until p bounded n … on_exceeded { … }`: hoechstens `n` Durchgaenge. After the
    last pass `p` is checked once more: a pass
    that makes `p` true is a success, and only otherwise the overflow block runs, from
    the world that recorded the read (corrected 2026-09-13; before,
    the `0` case ran the overflow block without the check). -/
def retryLauf (schritt : World D → Env D Γ → Ausgang V true Γ) (bis : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) :
    Nat → World D → Env D Γ → Ausgang V l Γ
  | 0, σ, ρ => if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ else ueberlauf (bis σ ρ).1 ρ
  | n + 1, σ, ρ =>
      if (bis σ ρ).2 = true then .ok (bis σ ρ).1 ρ else
      match schritt (bis σ ρ).1 ρ with
      | .ok σ' ρ' => retryLauf schritt bis ueberlauf n σ' ρ'
      | .next _ σ' ρ' => retryLauf schritt bis ueberlauf n σ' ρ'
      | .leave _ σ' ρ' => .ok σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .why σ' r => .why σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- `forever … progress a { … }` (H2): `passes` Durchgaenge von aussen; danach steht der
    Ausgang bei der Annahme `a`. -/
def foreverLauf (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool) :
    Nat → World D → Env D Γ → Ausgang V l Γ
  | 0, _, _ => .hardware (.fortschritt a)
  | n + 1, σ, ρ =>
      if (inv σ ρ).2 = false then .logik .schleife else
      match schritt (inv σ ρ).1 ρ with
      | .ok σ' ρ' => foreverLauf a schritt inv n σ' ρ'
      | .next _ σ' ρ' => foreverLauf a schritt inv n σ' ρ'
      | .leave _ σ' ρ' => .ok σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .why σ' r => .why σ' r
      | .logik e => .logik e
      | .hardware e => .hardware e

variable (P : Programm D) (O : Orakel D)

-- (H2) Wie viele Durchgaenge die Umgebung einem `forever` gibt.
variable (passes : Nat)

/-- Die Antwort eines Rufs, in den Typ der Bindung uebersetzt (`D.erg f = some τ`). -/
def ergWert {τ : Ty} {e : Option Ty} (he : e = some τ) (v : ErgVal D e) : Wert D τ := by
  subst he; exact v

/-- Die Nutzlast eines Falls in den Sichtbereich seines Arms. -/
def armEnv {c : Option (Int × Int)} (nutz : Nutzlast c) (ρ : Env D Γ) : Env D (ArmCtx Γ c) :=
  match c, nutz with
  | Option.none, _ => ρ
  | Option.some (_, _), v => .cons v ρ

def evalErg (σ₀ : World D) : ErgExpr D Γ Λ e → World D → Env D Γ → ErgVal D e
  | .empty, _, _ => ()
  | .val e, σ, ρ => eval σ₀ e σ ρ

/-- Die Argumente eines indirekten Rufs, in die Parameter der GERUFENEN Funktion: dieselbe
    Signatur, per `sig f = n`. -/
def umsig {f : D.Fn} {n : Nat} (hf : D.sig f = n) (ρ : Env D (D.sigNr n).params) :
    Env D (D.params f) := by
  unfold Deklaration.params Deklaration.signatur; rw [hf]; exact ρ

def keinGrundSig {f : D.Fn} {n : Nat} (hf : D.sig f = n) (hr : (D.sigNr n).gruende = 0)
    (r : Fin (D.gruende f)) : α := by
  unfold Deklaration.gruende Deklaration.signatur at r; rw [hf, hr] at r; exact r.elim0

theorem ergSig {f : D.Fn} {n : Nat} {τ : Ty} (hf : D.sig f = n) (he : (D.sigNr n).erg = some τ) :
    D.erg f = some τ := by
  unfold Deklaration.erg Deklaration.signatur; rw [hf]; exact he

/-- A float as a raw integer for the machine (a register write): truncation toward zero,
    saturated to the `Int64` range -- the meaning of the `Float` model's
    `x.toInt64.toInt`, now computed on the exact value (NaN/infinity give `0`; they do not
    occur, a `Val (.fl ..)` is finite). -/
def gleitRoh (x : GFloat) : Int :=
  match Gleitkomma.wertExakt Gleitkomma.f64 x with
  | Option.none => 0
  | Option.some v =>
    let t : Int := if 0 ≤ v.zweierExp then v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
      else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int)
    if t < -(2 ^ 63 : Int) then -(2 ^ 63 : Int)
    else if (2 ^ 63 - 1 : Int) < t then 2 ^ 63 - 1 else t

/-- Ein Wert als rohe Zahl, fuer die Maschine. -/
def roh : {τ : Ty} → Wert D τ → Int
  | .int _ _, v => v.n
  | .bool, b => if wahr? b then 1 else 0
  | .opt _, Option.none => -1
  | .opt _, Option.some k => k.n
  | .sum _, ⟨i, _⟩ => i.val
  | .why _, r => r.val
  | .never, v => v.elim
  | .fl _ _, v => gleitRoh v.x
  | .fnptr _, _ => 0
  | .ptr _ _, _ => 0

/-- Die Gleitkommarechnung der Maschine: IEEE-754 binary64, exact result rounded once to
    nearest-even (`Gleitkomma.add/sub/mul/div`) -- kernel-computable since 2026-09-14. -/
def gleitRechne : GleitOp → GFloat → GFloat → GFloat
  | .add, a, b => Gleitkomma.add Gleitkomma.f64 a b
  | .sub, a, b => Gleitkomma.sub Gleitkomma.f64 a b
  | .mul, a, b => Gleitkomma.mul Gleitkomma.f64 a b
  | .div, a, b => Gleitkomma.div Gleitkomma.f64 a b

section Rumpf
-- Die Bedeutung eines Rufs auf dieser Rekursionstiefe -- von aussen gegeben, und in
-- `rufAt` aus dem Rumpf des Gerufenen gebaut.
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- Ein Ruf, dessen Signatur keinen Fehlerkanal hat, liefert keinen Grund. -/
def keinGrund {f : D.Fn} (hr : D.gruende f = 0) (r : Fin (D.gruende f)) : α :=
  (Fin.cast hr r).elim0

/-- Das Ergebnis eines Axioms, gegen seinen Typ gehalten. -/
def axiomAntwort (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    World D × Option (ErgVal D (D.aerg a)) :=
  let (σ', roh) := O.wirkt a σ ρ
  (σ', einpassenErg O.zeiger (D.aerg a) roh)

/-- **The raw word of a FALLIBLE foreign body** (C-free lane, 2026-09-30): the pair
    "value or reason" packed as a `tagged` value is (`summePasst`) -- the case number in the low
    digit, base `n + 1`: case `0` carries the value (held against the declared answer type by
    `einpassenErg`), case `i + 1` is the reason `i`. The emitted stub forms that pair from the
    kernel's word (the `errors` map: listed `-errno` to its reason, an in-range value to case 0,
    anything else to the hardware outcome); that correspondence is the template `tor.fehlbar`
    (SchablonenOhneLibc.lean). -/
def sonstPasst (z : Int → Option D.Fn) (e : Option Ty) (n : Nat) (roh : Int) :
    Option (ErgVal D e ⊕ Fin n) :=
  let k : Int := (n : Int) + 1
  let tag : Int := roh % k
  if tag = 0 then (einpassenErg z e (roh / k)).map Sum.inl
  else if h : 0 < tag ∧ tag ≤ n then some (Sum.inr ⟨(tag - 1).toNat, by omega⟩)
  else none

/-- The answer of a fallible axiom: the world it leaves (as `axiomAntwort`) and the decoded
    pair. -/
def axiomAntwortSonst (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    World D × Option (ErgVal D (D.aerg a) ⊕ Fin (D.agruende a)) :=
  let (σ', roh) := O.wirkt a σ ρ
  (σ', sonstPasst O.zeiger (D.aerg a) (D.agruende a) roh)

/-- The world a fallible axiom leaves is the world the oracle's effect leaves -- the same as
    `axiomAntwort`'s, so every frame lemma about the one is one about the other. -/
theorem axiomAntwortSonst_fst (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    (axiomAntwortSonst O a σ ρ).1 = (axiomAntwort O a σ ρ).1 := rfl

mutual

def execStmt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .assignSlot t f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignThru p t _ f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
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
      if wahr? (eval σ c σ ρ) then execBlock t σ ρ else execBlock e σ ρ
  | .onOption o p a, σ, ρ =>
      let σ := σ.lese Λ o.orte
      match eval σ o σ ρ with
      | Option.some k => (execBlock p σ (.cons k ρ)).schrumpf
      | Option.none => execBlock a σ ρ
  | .onTag v arms, σ, ρ =>
      let σ := σ.lese Λ v.orte
      execArms arms (eval σ v σ ρ) σ ρ
  | .onWhy r arms, σ, ρ =>
      let σ := σ.lese Λ r.orte
      execGrund arms (eval σ r σ ρ) σ ρ
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
  | .locks L _ body, σ, ρ => (execBlock body (σ.nimmt L) ρ).mapWelt (·.gibt L)
  | .breaking _ body, σ, ρ => execBlock body σ ρ
  | .traverse t inv body, σ, ρ =>
      traverseLauf (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (alleIndizes (D.count t)) σ ρ
  | .retry n bis body ueberlauf, σ, ρ =>
      retryLauf (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        (fun σ ρ => execBlock ueberlauf σ ρ) n σ ρ
  | .forever a inv body, σ, ρ =>
      foreverLauf a (fun σ ρ => execBlock body σ ρ)
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

def execBlock {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .nil, σ, ρ => .ok σ ρ
  | .cons s rest, σ, ρ =>
      match execStmt s σ ρ with
      | .ok σ' ρ' => execBlock rest σ' ρ'
      | o => o
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execBlock rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlock rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlock rest σ (.cons v ρ)).schrumpf
          else (execEnd sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ rest, σ, ρ =>
      if O.sichtbar g σ then
        let σ := σ.lese Λ [.inr g]
        (execBlock rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := σ.lese Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execBlock rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlock rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else (execEnd sonst σ ρ).zuAusgang
  | .check c sonst rest, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlock rest σ ρ else (execEnd sonst σ ρ).zuAusgang
  | .float op a b lo hi rest, σ, ρ =>
      let σ := σ.lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatOf e lo hi rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatNarrow e lo hi sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEnd sonst σ ρ).zuAusgang

def execEnd {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retWhy r _, σ, _ => .why σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmt s σ ρ with
      | .ok σ' ρ' => execEnd rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .why σ' r => .why σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execEnd rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEnd err σ' (.cons r ρ)).schrumpf
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)

def execArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option (Int × Int))} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => (execBlock b σ (armEnv nutz ρ)).schrumpfArm _
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

def execGrund {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨0, _⟩, σ, ρ => execBlock b σ ρ
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => execGrund rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Rumpf
/-! ## 6. Der Ruf -- `requires`, der Rumpf, `ensures`, die Invarianten; und die Tiefe -/

/-- Die Bedeutung eines Rufs auf Tiefe `fuel`: die Vorbedingung, der Rumpf, die
    Nachbedingung, die geschuldeten Invarianten. Ist die Tiefe erschoepft, ist das Mass
    nicht gefallen -- `abstieg`, eine Logikstelle. -/
def rufAt : Nat → ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f
  | 0, f, _, _ => .logik (.abstieg f)
  | n + 1, f, σ, ρ =>
      let σ := σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
      if wahr? (eval σ (P.requires f) σ ρ) = false then .logik (.vorbedingung f) else
      match execEnd (V := vertragVon D f) O passes (rufAt n) (P.rumpf f) σ ρ with
      | EndAusgang.zurueck σ' v =>
          let σ' := σ'.lese (vertragVon D f).ende (P.ensures f).orte
          if wahr? (eval σ (P.ensures f) σ' (ergEnv (D.erg f) v ρ)) = false then .logik (.nachbedingung f)
          else
            let σ' := (D.invs.filter (schuldet f)).foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ'
            match D.invs.find? (fun i => schuldet f i && !wahr? (eval σ' (P.invariante i) σ' .nil)) with
            | Option.some i => .logik (.invariante i)
            | Option.none => .ok σ' v
      | .why σ' r => .why σ' r
      | .leave h _ _ => absurd h (by decide)
      | .next h _ _ => absurd h (by decide)
      | .logik e => .logik e
      | .hardware e => .hardware e

/-- **Die Bedeutung eines Rumpfs** in einem Programm, auf Rekursionstiefe `fuel`. -/
def exec (fuel : Nat) (V : Vertrag D) (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    Ausgang V l Γ :=
  execBlock O passes (rufAt P O passes fuel) b σ ρ

/-! ## 7. User partition and async device step -- shapes beside the run, no discharge -/

/-! ### 7.1 The two sides of one boundary, over the flat key space -/

/-- The two sides of one boundary: kernel memory and user memory. The world stays
    one flat mapping (`slots`/`globs`/`spur` above); the partition is a side per key,
    not a second world -- so every existing theorem reads the same `World`. -/
inductive Seite where
  | kern
  | user
  deriving DecidableEq, Repr

/-- A side assignment over the flat key space: each table slot has one side. -/
def SeitenWahl (D : Deklaration) : Type :=
  D.Tab → Int → Seite

/-- The user side, as a boolean test. -/
def istUserSeite : Seite → Bool
  | .user => true
  | .kern => false

/-- The kernel side, as a boolean test. -/
def istKernSeite : Seite → Bool
  | .kern => true
  | .user => false

/-- A world key on the user side: the assignment says `user`. -/
def benutzerSchluessel (w : SeitenWahl D) (t : D.Tab) (k : Int) : Prop :=
  w t k = .user

/-- A world key on the kernel side: the assignment says `kern`. -/
def kernSchluessel (w : SeitenWahl D) (t : D.Tab) (k : Int) : Prop :=
  w t k = .kern

/-- The partition covers and separates: every key is on exactly one side. -/
theorem seite_zerlegt (w : SeitenWahl D) (t : D.Tab) (k : Int) :
    (benutzerSchluessel w t k ∨ kernSchluessel w t k) ∧
    ¬ (benutzerSchluessel w t k ∧ kernSchluessel w t k) := by
  constructor
  · cases h : w t k <;> simp_all [benutzerSchluessel, kernSchluessel]
  · cases h : w t k <;> simp_all [benutzerSchluessel, kernSchluessel]

/-- The flat mapping is preserved across the partition: a store to one carrier
    leaves every slot of another carrier untouched -- the frame the partition
    checks against, still stated on `World.slots`. -/
theorem seite_rahmen_fremd (σ : World D) {t t' : D.Tab} (h : t' ≠ t)
    (k k' : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) (f' : D.Feld t') :
    (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
  simp [World.storeSlot, h]

/-! ### 7.2 The async device write beside `Orakel.wirkt` -/

/-- An async device write to carrier `t`, world to world -- beside `Orakel.wirkt`,
    which acts AT a call site (`D.Ax` plus its `Env`). This shape takes neither:
    no axiom, no call site, no argument environment. What it may change is the
    DMA-visible buffer carrier `t` alone: every other carrier, every global, and
    the trace stay -- the frame half. What the write OBSERVES (content) is not
    stated here: events carry no values, so no run fact implies it. -/
structure GeraetSchreibt (t : D.Tab) (σ σ' : World D) : Prop where
  sichtbar : D.geteilt t = true
  rahmen : ∀ t' : D.Tab, t' ≠ t → ∀ k' : Int, ∀ f' : D.Feld t', σ'.slots t' k' f' = σ.slots t' k' f'
  globale : ∀ g : D.Glob, σ'.globs g = σ.globs g
  spur : σ'.spur = σ.spur

/-- The window around an async device write: handoff before, take-back after --
    the `vor`/`nach` premise shape of `GeraetWache` (Geraet.lean), stated over
    worlds instead of run indices. At the handoff the guard is released (not held
    in `σ`); at the take-back it is held again (held in `σ'`). The CPU-side
    ordering against these endpoints stays driver duty, as `haussen` there. -/
structure GeraetFensterWelt (W : D.Lock) (t : D.Tab) (σ σ' : World D) : Prop where
  schritt : GeraetSchreibt t σ σ'
  vor : W ∉ σ.haelt
  nach : W ∈ σ'.haelt

/-- A windowed device write leaves every foreign carrier untouched. -/
theorem asyncFenster_rahmen {W : D.Lock} {t : D.Tab} {σ σ' : World D}
    (w : GeraetFensterWelt W t σ σ') {t' : D.Tab} (h : t' ≠ t)
    (k' : Int) (f' : D.Feld t') :
    σ'.slots t' k' f' = σ.slots t' k' f' :=
  w.schritt.rahmen t' h k' f'

/-- A windowed device write leaves the trace untouched -- locks held stay held. -/
theorem asyncFenster_spur {W : D.Lock} {t : D.Tab} {σ σ' : World D}
    (w : GeraetFensterWelt W t σ σ') :
    σ'.spur = σ.spur :=
  w.schritt.spur

/-! ### Cuts (booked, not hidden)

    (S1) The partition is a shape over the flat key space; no `Stmt`/`Block`
         transition discharges it -- a range check inside `exec` stays future work.
    (S2) The async step is a shape beside `Orakel.wirkt`; there is no interleaving
         with `exec` runs here and no content invariant -- order without content
         leaves the content half open, content without order the race half open.
-/


end Gabbro.Grammatik
