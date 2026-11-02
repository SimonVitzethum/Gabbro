module

public import Grammatik.Kern.Semantik.Semantik.T1

@[expose] public section



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

/-- Die Nutzlast D.Fn D.passt eines Falls in den Sichtbereich seines Arms. -/
def armEnv {c : Option Ty} (nutz : Nutzlast D.Fn D.passt c) (ρ : Env D Γ) : Env D (ArmCtx Γ c) :=
  match c, nutz with
  | Option.none, _ => ρ
  | Option.some _, v => .cons v ρ

def evalErg (σ₀ : World D) : ErgExpr D Γ Λ e → World D → Env D Γ → ErgVal D e
  | .empty, _, _ => ()
  | .val e, σ, ρ => eval σ₀ e σ ρ

/-- The arguments of an indirect call, as the parameters of the CALLED function: a conforming
    function has the pointer type's parameters (`SigPasst.params`). -/
def umsig {f : D.Fn} {n : Nat} (hf : D.passt f n = true) (ρ : Env D (D.sigNr n).params) :
    Env D (D.params f) := by
  unfold Deklaration.params; rw [(D.passt_sig hf).params]; exact ρ

def keinGrundSig {f : D.Fn} {n : Nat} (hf : D.passt f n = true) (hr : (D.sigNr n).gruende = 0)
    (r : Fin (D.gruende f)) : α := by
  unfold Deklaration.gruende at r; rw [(D.passt_sig hf).gruende, hr] at r; exact r.elim0

theorem ergSig {f : D.Fn} {n : Nat} {τ : Ty} (hf : D.passt f n = true) (he : (D.sigNr n).erg = some τ) :
    D.erg f = some τ := by
  unfold Deklaration.erg; rw [(D.passt_sig hf).erg]; exact he

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
  | .ptr _, _ => 0
  | .ref _, v => (v.zelle : Int)
  -- an aggregate has no raw word (the checker writes none to a register)
  | .arr _ _, _ => 0
  | .str _, _ => 0
  | .prod _ _, _ => 0

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
  let (σ', roh) := O.wirkt a (σ.fragt (.inl a)) ρ
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
  let (σ', roh) := O.wirkt a (σ.fragt (.inl a)) ρ
  (σ', sonstPasst O.zeiger (D.aerg a) (D.agruende a) roh)

/-- The world a fallible axiom leaves is the world the oracle's effect leaves -- the same as
    `axiomAntwort`'s, so every frame lemma about the one is one about the other. -/
theorem axiomAntwortSonst_fst (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    (axiomAntwortSonst O a σ ρ).1 = (axiomAntwort O a σ ρ).1 := by rfl

end Rumpf
end Gabbro.Grammatik
