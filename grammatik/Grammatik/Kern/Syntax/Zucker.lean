/-
  Datei:      Grammatik/Zucker.lean
  Gegenstand: **Der Zucker** -- jede Schreibweise von `SYNTAX.md`, die keinen eigenen
              Konstruktor hat, als DEFINITION ueber dem Kern. Ihre Bedeutung ist damit die
              des Terms, den sie bildet; es gibt keine zweite Uebersetzung, die falsch sein
              koennte. Was hier steht, ist das, was `SYNTAX.md` als `SUGAR` markiert.

    §1  Typen ohne Bereich            `u8` … `i64`, `f64` ohne `in`
    §2  Praedikatzucker               `=>`, `!=`, `>`, `>=`, `~`, `in`, `descendants of`,
                                      `ancestors of`, `chain(…) in`, `queue`, `fields of`
    §3  Anweisungszucker              `+=` `-=` `&=` `|=`, `observes`, `on_exceeded f`, `alloc T`,
                                      `accumulates … merge`, `maintains`, ein Verbundwert
    §4  Bytes als Sicht               ein `format`-Feld `@[hi:lo]`, `embeds … scale`,
                                      `offset_into`, `endian big`
    §5  `walk`                        `mappings of` als geschachtelter `traverse`
    §6  Sichtbereich erweitern        `Expr.weaken` -- was jeder Zucker mit Binder braucht

  Nichts hier hat eine eigene Bedeutung: `eval`/`exec` sehen nur den Kern.
-/
import Grammatik.Kern.Semantik.Semantik

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
  | [], x => .there x
  | _ :: _, .here => .here
  | _ :: Γ1, .there x => .there (Var.ins Γ1 x)

/-- A renaming lifted under one more binder. -/
def Var.hoch {Γ Γ' : Ctx} (r : ∀ {τ : Ty}, Var Γ τ → Var Γ' τ) :
    ∀ {τ : Ty}, Var (σ :: Γ) τ → Var (σ :: Γ') τ
  | _, .here => .here
  | _, .there x => .there (r x)

mutual
/-- An expression under a renaming of its variables: the same places, the same `Λ`.
    Structural, so it computes in the kernel (an exported program's sugar is decided by `decide`). -/
def Expr.ren {Γ Γ' : Ctx} (r : ∀ {τ : Ty}, Var Γ τ → Var Γ' τ) : Expr D Γ Λ τ → Expr D Γ' Λ τ
  | .lit n => .lit n
  | .tru => .tru
  | .fls => .fls
  | .var x => .var (r x)
  | .glob g hL => .glob g hL
  | .slot t f i hL => .slot t f (i.ren r) hL
  | .thru p t ht f i hL => .thru (p.ren r) t ht f (i.ren r) hL
  | .ptrOf t n ht rw => .ptrOf t n ht rw
  | .fnref f n h => .fnref f n h
  | .oldG g hL => .oldG g hL
  | .oldS t f i hL => .oldS t f (i.ren r) hL
  | .refEq a b => .refEq (a.ren r) (b.ren r)
  | .slotRef q t ht ho f hL => .slotRef (q.ren r) t ht ho f hL
  | .getBytes t f hf n i hlo hhi hL => .getBytes t f hf n (i.ren r) hlo hhi hL
  | .widen h1 h2 e => .widen h1 h2 (e.ren r)
  | .add a b => .add (a.ren r) (b.ren r)
  | .sub a b => .sub (a.ren r) (b.ren r)
  | .neg a => .neg (a.ren r)
  | .mul a b => .mul (a.ren r) (b.ren r)
  | .div h0 h1 a b => .div h0 h1 (a.ren r) (b.ren r)
  | .rem h0 h1 a b => .rem h0 h1 (a.ren r) (b.ren r)
  | .sdiv hb a b => .sdiv hb (a.ren r) (b.ren r)
  | .srem hb a b => .srem hb (a.ren r) (b.ren r)
  | .band h0 h0' a b => .band h0 h0' (a.ren r) (b.ren r)
  | .bor w h0 h0' hw1 hw2 a b => .bor w h0 h0' hw1 hw2 (a.ren r) (b.ren r)
  | .bxor w h0 h0' hw1 hw2 a b => .bxor w h0 h0' hw1 hw2 (a.ren r) (b.ren r)
  | .shl w hw1 hw2 h0 h0' a b => .shl w hw1 hw2 h0 h0' (a.ren r) (b.ren r)
  | .shr w hw1 hw2 h0 h0' a b => .shr w hw1 hw2 h0 h0' (a.ren r) (b.ren r)
  | .lt a b => .lt (a.ren r) (b.ren r)
  | .le a b => .le (a.ren r) (b.ren r)
  | .eq a b => .eq (a.ren r) (b.ren r)
  | .fllt a b => .fllt (a.ren r) (b.ren r)
  | .flle a b => .flle (a.ren r) (b.ren r)
  | .and a b => .and (a.ren r) (b.ren r)
  | .or a b => .or (a.ren r) (b.ren r)
  | .not a => .not (a.ren r)
  | .none n => .none n
  | .some e => .some (e.ren r)
  | .istSome e => .istSome (e.ren r)
  | .case cs i nutz => .case cs i (nutz.ren r)
  | .why n r' => .why n r'
  | .forallSlots t body hL => .forallSlots t (body.ren (Var.hoch r)) hL
  | .existsSlots t body hL => .existsSlots t (body.ren (Var.hoch r)) hL
  | .reaches t f hf a b hL => .reaches t f hf (a.ren r) (b.ren r) hL

def NutzlastExpr.ren {Γ Γ' : Ctx} (r : ∀ {τ : Ty}, Var Γ τ → Var Γ' τ) :
    NutzlastExpr D Γ Λ c → NutzlastExpr D Γ' Λ c
  | .empty => .empty
  | .num e => .num (e.ren r)
end

/-- Ein Ausdruck unter einem eingeschobenen Binder: dieselben Orte, dasselbe `Λ`. -/
def Expr.ins (Γ1 : Ctx) (e : Expr D (Γ1 ++ Γ2) Λ τ) : Expr D (Γ1 ++ σ :: Γ2) Λ τ :=
  e.ren (Var.ins Γ1)

def NutzlastExpr.ins (Γ1 : Ctx) (e : NutzlastExpr D (Γ1 ++ Γ2) Λ c) : NutzlastExpr D (Γ1 ++ σ :: Γ2) Λ c :=
  e.ren (Var.ins Γ1)

/-- Ein Ausdruck, einen Binder tiefer. -/
def Expr.weaken (e : Expr D Γ Λ τ) : Expr D (σ :: Γ) Λ τ := Expr.ins (Γ1 := []) e

/-! ## 2. Praedikatzucker -/

namespace Expr
variable {Γ : Ctx} {Λ : List (Res D)}

/-- `p => q` -/
def impl (p q : Expr D Γ Λ .bool) : Expr D Γ Λ .bool := .or (.not p) q
/-- `a != b` -/
def ne (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) : Expr D Γ Λ .bool := .not (.eq a b)
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
  .existsSlots t (.eq (.var .here) e.weaken) hL
/-- `forall k in descendants of s : p` -- jeder Slot, den `s` ueber die `child`-Kante erreicht. -/
def descendants (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
    (s : Expr D Γ Λ (.index (D.count t))) (body : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (hL : darf D t Λ) : Expr D Γ Λ .bool :=
  .forallSlots t (impl (.reaches t f hf s.weaken (.var .here) hL) body) hL
/-- `forall k in ancestors of s : p` -- dieselbe Kette, andere Richtung: `k` erreicht `s`. -/
def ancestors (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
    (s : Expr D Γ Λ (.index (D.count t))) (body : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (hL : darf D t Λ) : Expr D Γ Λ .bool :=
  .forallSlots t (impl (.reaches t f hf (.var .here) s.weaken hL) body) hL
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
  .assignVar x (.widen h1 h2 (.add (.var x) e))
/-- `x -= e` -/
def minusGleich (x : Var Γ (.int lo hi)) (e : Expr D Γ Λ (.int lo' hi'))
    (h1 : lo ≤ lo - hi') (h2 : hi - lo' ≤ hi) : Stmt D V l Γ Λ Λ :=
  .assignVar x (.widen h1 h2 (.sub (.var x) e))
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
def maintains (_ : D.Inv) : Stmt D V l Γ Λ Λ := .ite .tru .nil .nil
/-- `accumulates A merge max`: `if A < v { A = v; }` ueber einem Zahlglobal. -/
def mergeMax (g : D.Glob) (hτ : D.gtyp g = .int lo hi) (v : Expr D Γ Λ (.int lo hi))
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ) : Stmt D V l Γ Λ Λ :=
  .ite (.lt (hτ ▸ Expr.glob g hL) v) (.cons (.assignGlob g (hτ.symm ▸ v) hw hL) .nil) .nil
/-- `accumulates A merge add`: `A = A + v` -- der Bereich muss tragen. -/
def mergeAdd (g : D.Glob) (hτ : D.gtyp g = .int lo hi) (v : Expr D Γ Λ (.int lo' hi'))
    (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) :
    Stmt D V l Γ Λ Λ :=
  .assignGlob g (hτ.symm ▸ Expr.widen h1 h2 (.add (hτ ▸ Expr.glob g hL) v)) hw hL
/-- Ein Verbundwert `P(a: e)` -- ein Traeger mit `count 1`: Feld fuer Feld gesetzt. -/
def verbund (t : D.Tab) (hc : 1 ≤ D.count t) (f : D.Feld t) (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt D V l Γ Λ Λ :=
  .assignSlot t f (.widen (Int.le_refl 0) (by omega) (.lit 0)) e hw hL
end Stmt

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
/-- `on_exceeded f` -- `{ f(); }` mit einer parameterlosen `f` ohne Fehlerkanal. -/
def onExceeded (f : D.Fn) (hp0 : D.params f = []) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) : Block D V l Γ Λ (nach D f Λ) :=
  .cons (.call f (hp0 ▸ Args.nil) hp hr) .nil

/-- The empty argument list at a parameter list known to be empty (by a match, so that `alloc` reduces where the
    provider's parameters are concrete). -/
def argsLeer : (ps : List Ty) → ps = [] → Args D Γ Λ ps
  | [], _ => .nil

/-- `let r = alloc T;` -- the call of `T`'s provider (`table T from p`): `let r = p();`. The provider
    takes no arguments (`anbieter_passt`); its answer is a reference into `T` (`Block.alloc_tabelle`). -/
def alloc (t : D.Tab) (a : D.Ax) (hp : D.anbieter t = some a) (he : D.aerg a = some (.ref n))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Block D V l (.ref n :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .bindAxiom a (argsLeer _ (D.anbieter_passt t a hp).2.1) he hw hg hd hgd rest

/-- **`alloc T` answers a reference into `T`**: the number its provider's answer type names is `T`'s. -/
theorem alloc_tabelle {t : D.Tab} {a : D.Ax} (hp : D.anbieter t = some a) (he : D.aerg a = some (.ref n)) :
    D.tabNr n = some t ∧ D.offen t = true := by
  obtain ⟨ho, _, m, hm, ht⟩ := D.anbieter_passt t a hp
  rw [he] at hm
  cases hm
  exact ⟨ht, ho⟩
end Block

namespace Endblock
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
/-- `let r = alloc T;` at the top level of a body: `Block.alloc` with an end-block rest. -/
def alloc (t : D.Tab) (a : D.Ax) (hp : D.anbieter t = some a) (he : D.aerg a = some (.ref n))
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (rest : Endblock D V l (.ref n :: Γ) Λ) : Endblock D V l Γ Λ :=
  .bindAxiom a (Block.argsLeer _ (D.anbieter_passt t a hp).2.1) he hw hg hd hgd rest
end Endblock

/-! ## 4. Bytes als Sicht -/

namespace Expr
variable {Γ : Ctx} {Λ : List (Res D)}

/-- Ein `format`-Feld `@[hi:lo]` in einem Wort von `n` Bytes am Versatz `off` eines
    Bytetraegers: `(bytes >> lo) & (2^(hi-lo+1) - 1)`. `offset_into` und `@bitpos` sind
    diese Lesung; die Schranke am Versatz steht an `leseBytes`.

    SCHRANKE (2026-09-12, lane 61): die Schiebeweite `lo'` braucht eine
    Speicherbreite `w` mit `256^n - 1 < 2^w` und `lo' < w` (PLAN-BITS.md §2).
    Beides folgt NICHT aus den Argumenten -- `lo'` und `n` sind frei --,
    darum nimmt `bitfeld` sie als Voraussetzungen. -/
def bitfeld (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
    (off : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ)
    (lo' breite : Nat) (hw1 : (256 : Int) ^ n - 1 < 2 ^ (lo' + 1))
    (hw2 : (lo' : Int) < ((lo' + 1 : Nat) : Int)) :
    Expr D Γ Λ (.int 0 (2 ^ breite - 1)) :=
  .band (l1 := 2 ^ breite - 1) (l2 := 0) (by have := two_pow_pos_int breite; omega) (Int.le_refl 0)
    (.lit (2 ^ breite - 1))
    (.shr (lo' + 1) hw1 hw2 (l1 := 0) (l2 := (lo' : Int))
      (Int.le_refl 0) (Int.natCast_nonneg lo')
      (.getBytes t f hf n off hlo hhi hL) (.lit lo'))

/-- `embeds [hi:lo] scale s` -- das Bitfeld, mal `s`. -/
def embeds (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
    (off : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ)
    (lo' breite : Nat) (hw1 : (256 : Int) ^ n - 1 < 2 ^ (lo' + 1))
    (hw2 : (lo' : Int) < ((lo' + 1 : Nat) : Int)) (s : Int) :
    Expr D Γ Λ (.int (imin (imin (0 * s) (0 * s)) (imin ((2 ^ breite - 1) * s) ((2 ^ breite - 1) * s)))
                     (imax (imax (0 * s) (0 * s)) (imax ((2 ^ breite - 1) * s) ((2 ^ breite - 1) * s)))) :=
  .mul (bitfeld t f hf n off hlo hhi hL lo' breite hw1 hw2) (.lit s)
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
