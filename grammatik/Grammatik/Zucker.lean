/-
  Datei:      Grammatik/Zucker.lean
  Gegenstand: **Der Zucker** -- jede Schreibweise von `SYNTAX.md`, die keinen eigenen
              Konstruktor hat, als DEFINITION ueber dem Kern. Ihre Bedeutung ist damit die
              des Terms, den sie bildet; es gibt keine zweite Uebersetzung, die falsch sein
              koennte. Was hier steht, ist das, was `SYNTAX.md` als `SUGAR` markiert.

    §1  Typen ohne Bereich            `u8` … `i64`, `f64` ohne `in`
    §2  Praedikatzucker               `=>`, `!=`, `>`, `>=`, `~`, `in`, `descendants of`,
                                      `ancestors of`, `chain(…) in`, `queue`, `fields of`
    §3  Anweisungszucker              `+=` `-=` `&=` `|=`, `observes`, `on_exceeded f`,
                                      `accumulates … merge`, `maintains`, ein Verbundwert
    §4  Bytes als Sicht               ein `format`-Feld `@[hi:lo]`, `embeds … scale`,
                                      `offset_into`, `endian big`
    §5  `walk`                        `mappings of` als geschachtelter `traverse`
    §6  Sichtbereich erweitern        `Expr.weaken` -- was jeder Zucker mit Binder braucht

  Nichts hier hat eine eigene Bedeutung: `eval`/`exec` sehen nur den Kern.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Typen ohne Bereich -/

namespace Ty
abbrev u8 : Ty := .int 0 (2 ^ 8 - 1)
abbrev u16 : Ty := .int 0 (2 ^ 16 - 1)
abbrev u32 : Ty := .int 0 (2 ^ 32 - 1)
abbrev u64 : Ty := .int 0 (2 ^ 64 - 1)
abbrev i8 : Ty := .int (-(2 ^ 7)) (2 ^ 7 - 1)
abbrev i16 : Ty := .int (-(2 ^ 15)) (2 ^ 15 - 1)
abbrev i32 : Ty := .int (-(2 ^ 31)) (2 ^ 31 - 1)
abbrev i64 : Ty := .int (-(2 ^ 63)) (2 ^ 63 - 1)
/-- `f64` ohne `in`: der weiteste endliche Bereich der Breite (hier als Bruch mit Nenner 1). -/
abbrev f64 : Ty := .fl (-(2 ^ 1024 - 1), 1) (2 ^ 1024 - 1, 1)
end Ty

/-! ## 6. Sichtbereich erweitern -- vorgezogen, weil §2 und §5 es brauchen -/

/-- Eine Variable unter einem eingeschobenen Binder. -/
def Var.ins : (Γ1 : Ctx) → Var (Γ1 ++ Γ2) τ → Var (Γ1 ++ σ :: Γ2) τ
  | [], x => .dort x
  | _ :: _, .hier => .hier
  | _ :: Γ1, .dort x => .dort (Var.ins Γ1 x)

mutual
/-- Ein Ausdruck unter einem eingeschobenen Binder: dieselben Orte, dasselbe `Λ`. -/
def Expr.ins (Γ1 : Ctx) : Expr D (Γ1 ++ Γ2) Λ τ → Expr D (Γ1 ++ σ :: Γ2) Λ τ
  | .lit n => .lit n
  | .wahr => .wahr
  | .falsch => .falsch
  | .var x => .var (Var.ins Γ1 x)
  | .glob g hL => .glob g hL
  | .slot t f i hL => .slot t f (i.ins Γ1) hL
  | .durch p t ht f i hL => .durch (p.ins Γ1) t ht f (i.ins Γ1) hL
  | .ptrOf t n ht rw => .ptrOf t n ht rw
  | .fnref f n h => .fnref f n h
  | .altGlob g hL => .altGlob g hL
  | .altSlot t f i hL => .altSlot t f (i.ins Γ1) hL
  | .leseBytes t f hf n i hlo hhi hL => .leseBytes t f hf n (i.ins Γ1) hlo hhi hL
  | .weiter h1 h2 e => .weiter h1 h2 (e.ins Γ1)
  | .add a b => .add (a.ins Γ1) (b.ins Γ1)
  | .sub a b => .sub (a.ins Γ1) (b.ins Γ1)
  | .neg a => .neg (a.ins Γ1)
  | .mul a b => .mul (a.ins Γ1) (b.ins Γ1)
  | .div h0 h1 a b => .div h0 h1 (a.ins Γ1) (b.ins Γ1)
  | .rem h0 h1 a b => .rem h0 h1 (a.ins Γ1) (b.ins Γ1)
  | .sdiv hb a b => .sdiv hb (a.ins Γ1) (b.ins Γ1)
  | .srem hb a b => .srem hb (a.ins Γ1) (b.ins Γ1)
  | .band h0 h0' a b => .band h0 h0' (a.ins Γ1) (b.ins Γ1)
  | .bor w h0 h0' hw1 hw2 a b => .bor w h0 h0' hw1 hw2 (a.ins Γ1) (b.ins Γ1)
  | .bxor w h0 h0' hw1 hw2 a b => .bxor w h0 h0' hw1 hw2 (a.ins Γ1) (b.ins Γ1)
  | .shl h0 h0' a b => .shl h0 h0' (a.ins Γ1) (b.ins Γ1)
  | .shr h0 h0' a b => .shr h0 h0' (a.ins Γ1) (b.ins Γ1)
  | .lt a b => .lt (a.ins Γ1) (b.ins Γ1)
  | .le a b => .le (a.ins Γ1) (b.ins Γ1)
  | .eq a b => .eq (a.ins Γ1) (b.ins Γ1)
  | .fllt a b => .fllt (a.ins Γ1) (b.ins Γ1)
  | .flle a b => .flle (a.ins Γ1) (b.ins Γ1)
  | .und a b => .und (a.ins Γ1) (b.ins Γ1)
  | .oder a b => .oder (a.ins Γ1) (b.ins Γ1)
  | .nicht a => .nicht (a.ins Γ1)
  | .none n => .none n
  | .some e => .some (e.ins Γ1)
  | .istSome e => .istSome (e.ins Γ1)
  | .fall cs i nutz => .fall cs i (nutz.ins Γ1)
  | .grund n r => .grund n r
  | .forallSlots t body hL => .forallSlots t (body.ins (_ :: Γ1)) hL
  | .existsSlots t body hL => .existsSlots t (body.ins (_ :: Γ1)) hL
  | .reaches t f hf a b hL => .reaches t f hf (a.ins Γ1) (b.ins Γ1) hL

def NutzlastExpr.ins (Γ1 : Ctx) : NutzlastExpr D (Γ1 ++ Γ2) Λ c → NutzlastExpr D (Γ1 ++ σ :: Γ2) Λ c
  | .keine => .keine
  | .zahl e => .zahl (e.ins Γ1)
end

/-- Ein Ausdruck, einen Binder tiefer. -/
def Expr.weaken (e : Expr D Γ Λ τ) : Expr D (σ :: Γ) Λ τ := Expr.ins (Γ1 := []) e

/-! ## 2. Praedikatzucker -/

namespace Expr
variable {Γ : Ctx} {Λ : List (Res D)}

/-- `p => q` -/
def impl (p q : Expr D Γ Λ .bool) : Expr D Γ Λ .bool := .oder (.nicht p) q
/-- `a != b` -/
def ne (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Expr D Γ Λ .bool := .nicht (.eq a b)
/-- `a > b` -/
def gt (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Expr D Γ Λ .bool := .lt b a
/-- `a >= b` -/
def ge (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Expr D Γ Λ .bool := .le b a
theorem two_pow_pos_int (w : Nat) : (0 : Int) < 2 ^ w := by
  have := Nat.two_pow_pos w
  have e : ((2 ^ w : Nat) : Int) = (2 : Int) ^ w := by simp
  omega

/-- `~a` in der Breite `w`: `a ^ (2^w − 1)` (`M137`). -/
def bnot (w : Nat) (h0 : 0 ≤ l1) (hw : h1 < 2 ^ w) (a : Expr D Γ Λ (.int l1 h1)) :
    Expr D Γ Λ (.int 0 (2 ^ w - 1)) :=
  .bxor w h0 (by have := two_pow_pos_int w; omega) hw (by omega) a (.lit (2 ^ w - 1))
/-- `e in slots of T` -/
def member (t : D.Tab) (e : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr D Γ Λ .bool :=
  .existsSlots t (.eq (.var .hier) e.weaken) hL
/-- `forall k in descendants of s : p` -- jeder Slot, den `s` ueber die `child`-Kante erreicht. -/
def descendants (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
    (s : Expr D Γ Λ (.index (D.count t))) (body : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (hL : darf D t Λ) : Expr D Γ Λ .bool :=
  .forallSlots t (impl (.reaches t f hf s.weaken (.var .hier) hL) body) hL
/-- `forall k in ancestors of s : p` -- dieselbe Kette, andere Richtung: `k` erreicht `s`. -/
def ancestors (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
    (s : Expr D Γ Λ (.index (D.count t))) (body : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (hL : darf D t Λ) : Expr D Γ Λ .bool :=
  .forallSlots t (impl (.reaches t f hf (.var .hier) s.weaken hL) body) hL
/-- `chain(a, b) in T` -- `a` erreicht `b` ueber das Feld, das die Stelle nennt. -/
def chain (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
    (a b : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr D Γ Λ .bool :=
  .reaches t f hf a b hL
/-- `forall k in queue T : p`, `elems of`, `fields of`, `threads` -- alles `slots of`. -/
def queue (t : D.Tab) (body : Expr D (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
    Expr D Γ Λ .bool := .forallSlots t body hL
end Expr

/-! ## 3. Anweisungszucker -/

namespace Stmt
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- `x += e` -- der Bereich von `x + e` liegt im Bereich von `x`; sonst ist es nicht
    schreibbar (das ist `M104`, als Voraussetzung des Zuckers). -/
def plusGleich (x : Var Γ (.int lo hi)) (e : Expr D Γ Λ (.int lo' hi'))
    (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi) : Stmt D V l Γ Λ Λ :=
  .assignVar x (.weiter h1 h2 (.add (.var x) e))
/-- `x -= e` -/
def minusGleich (x : Var Γ (.int lo hi)) (e : Expr D Γ Λ (.int lo' hi'))
    (h1 : lo ≤ lo - hi') (h2 : hi - lo' ≤ hi) : Stmt D V l Γ Λ Λ :=
  .assignVar x (.weiter h1 h2 (.sub (.var x) e))
/-- `x &= e` ueber `0 ..` -/
def undGleich (x : Var Γ (.int 0 hi)) (e : Expr D Γ Λ (.int lo' hi')) (h0' : 0 ≤ lo') :
    Stmt D V l Γ Λ Λ :=
  .assignVar x (.band (Int.le_refl 0) h0' (.var x) e)
/-- `x |= e` in der Breite `w` -/
def oderGleich (w : Nat) (x : Var Γ (.int 0 (2 ^ w - 1))) (e : Expr D Γ Λ (.int lo' hi'))
    (h0' : 0 ≤ lo') (hw : hi' < 2 ^ w) : Stmt D V l Γ Λ Λ :=
  .assignVar x (.bor w (Int.le_refl 0) h0' (by omega) hw (.var x) e)
/-- `observes R { … }` -- eine Sperre ohne Ausschluss ist eine Sperre mit Rang. -/
def observes (R : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang R)
    (body : Block D V l Γ (.held R :: Λ) (.held R :: Λ)) : Stmt D V l Γ Λ Λ :=
  .locks R hr body
/-- `maintains I` -- sagt nichts, was `effects` nicht schon sagt. -/
def maintains (_ : D.Inv) : Stmt D V l Γ Λ Λ := .ite .wahr .nil .nil
/-- `accumulates A merge max`: `if A < v { A = v; }` ueber einem Zahlglobal. -/
def mergeMax (g : D.Glob) (hτ : D.gtyp g = .int lo hi) (v : Expr D Γ Λ (.int lo hi))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ) : Stmt D V l Γ Λ Λ :=
  .ite (.lt (hτ ▸ Expr.glob g hL) v) (.cons (.assignGlob g (hτ.symm ▸ v) hw hL) .nil) .nil
/-- `accumulates A merge add`: `A = A + v` -- der Bereich muss tragen. -/
def mergeAdd (g : D.Glob) (hτ : D.gtyp g = .int lo hi) (v : Expr D Γ Λ (.int lo' hi'))
    (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) :
    Stmt D V l Γ Λ Λ :=
  .assignGlob g (hτ.symm ▸ Expr.weiter h1 h2 (.add (hτ ▸ Expr.glob g hL) v)) hw hL
/-- Ein Verbundwert `P(a: e)` -- ein Traeger mit `count 1`: Feld fuer Feld gesetzt. -/
def verbund (t : D.Tab) (hc : 1 ≤ D.count t) (f : D.Feld t) (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt D V l Γ Λ Λ :=
  .assignSlot t f (.weiter (Int.le_refl 0) (by omega) (.lit 0)) e hw hL
end Stmt

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
/-- `on_exceeded f` -- `{ f(); }` mit einer parameterlosen `f` ohne Fehlerkanal. -/
def onExceeded (f : D.Fn) (hp0 : D.params f = []) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) : Block D V l Γ Λ (nach D f Λ) :=
  .cons (.call f (hp0 ▸ Args.nil) hp hr) .nil
end Block

/-! ## 4. Bytes als Sicht -/

namespace Expr
variable {Γ : Ctx} {Λ : List (Res D)}

/-- Ein `format`-Feld `@[hi:lo]` in einem Wort von `n` Bytes am Versatz `off` eines
    Bytetraegers: `(bytes >> lo) & (2^(hi-lo+1) - 1)`. `offset_into` und `@bitpos` sind
    diese Lesung; die Schranke am Versatz steht an `leseBytes`. -/
def bitfeld (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
    (off : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ)
    (lo' breite : Nat) :
    Expr D Γ Λ (.int 0 (2 ^ breite - 1)) :=
  .band (l1 := 2 ^ breite - 1) (l2 := 0) (by have := two_pow_pos_int breite; omega) (Int.le_refl 0)
    (.lit (2 ^ breite - 1))
    (.shr (l1 := 0) (l2 := (lo' : Int)) (Int.le_refl 0) (Int.natCast_nonneg lo')
      (.leseBytes t f hf n off hlo hhi hL) (.lit lo'))

/-- `embeds [hi:lo] scale s` -- das Bitfeld, mal `s`. -/
def embeds (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
    (off : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ)
    (lo' breite : Nat) (s : Int) :
    Expr D Γ Λ (.int (imin (imin (0 * s) (0 * s)) (imin ((2 ^ breite - 1) * s) ((2 ^ breite - 1) * s)))
                     (imax (imax (0 * s) (0 * s)) (imax ((2 ^ breite - 1) * s) ((2 ^ breite - 1) * s)))) :=
  .mul (bitfeld t f hf n off hlo hhi hL lo' breite) (.lit s)
end Expr

/-- `endian big`: dieselben Bytes, umgedreht -- eine Zahl aus der gespiegelten Liste. -/
def bytesZuZahlBig (bs : List Byte) : Int := bytesZuZahl bs.reverse

/-! ## 5. `walk` -- `mappings of` als geschachtelter `traverse` -/

namespace Stmt
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
/-- Zwei Stufen: ueber jeden Eintrag der oberen, darin ueber jeden der unteren; `n` Stufen
    sind `n`-mal dieses. Die Invariante gilt an jeder Grenze beider Schleifen. -/
def walk2 (t1 t2 : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D V true (.index (D.count t2) :: .index (D.count t1) :: Γ) Λ Λ) : Stmt D V l Γ Λ Λ :=
  .traverse t1 inv (.cons (.traverse t2 inv.weaken body) .nil)
end Stmt

/-! ## Sprechproben: der Zucker bedeutet, was er soll -/

example (p q : Expr D Γ Λ .bool) (σ₀ σ : World D) (ρ : Env D Γ) :
    wahr? (eval σ₀ (Expr.impl p q) σ ρ) = (!wahr? (eval σ₀ p σ ρ) || wahr? (eval σ₀ q σ ρ)) := rfl

example (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) (σ₀ σ : World D) (ρ : Env D Γ) :
    wahr? (eval σ₀ (Expr.gt a b) σ ρ) = decide ((eval σ₀ b σ ρ).n < (eval σ₀ a σ ρ).n) := rfl

end Gabbro.Grammatik
