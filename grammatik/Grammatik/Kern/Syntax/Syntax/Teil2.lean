module

public import Grammatik.Kern.Syntax.Typen.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable (D : Deklaration)

mutual

inductive Expr : Ctx → List (Res D) → Ty → Type where
  | lit (n : Int) : Expr Γ Λ (.int n n)
  | tru : Expr Γ Λ .bool
  | fls : Expr Γ Λ .bool
  | var (x : Var Γ τ) : Expr Γ Λ τ
  /-- Ein `static`/`atomic`: unter seinen Waechtern (`H007`). -/
  | glob (g : D.Glob) (hL : gdarf D g Λ) : Expr Γ Λ (D.gtyp g)
  /-- `T.slots[i].f` -- Index vom ERZEUGTEN Indextyp (`M103`), Traeger unter Waechtern. -/
  | slot (t : D.Tab) (f : D.Feld t) (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
      Expr Γ Λ (D.typ t f)
  /-- `p->f`, `p[i].f` -- ein Zugriff DURCH einen Zeiger auf Traeger `n`: derselbe Zugriff wie
      `slot`, mit denselben Waechtern; der Zeiger ist die Faehigkeit, `t` zu nennen (M3). -/
  | thru (p : Expr Γ Λ (.ptr n rw)) (t : D.Tab) (ht : D.tabNr n = some t) (f : D.Feld t)
      (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr Γ Λ (D.typ t f)
  /-- Der Zeiger auf einen Traeger -- die einzige Adresse, die es gibt: die eines DEKLARIERTEN
      Dings. Es gibt keine Adresse eines Ausdrucks (`SYNTAX.md` §4, `fnvalue`). -/
  | ptrOf (t : D.Tab) (n : Nat) (ht : D.tabNr n = some t) (rw : Bool) : Expr Γ Λ (.ptr n rw)
  /-- `&f` -- the function pointer: a function that CONFORMS to the pointer type («B8»; structural
      since 2026-10-21, `Deklaration.passt`). -/
  | fnref (f : D.Fn) (n : Nat) (h : D.passt f n = true) : Expr Γ Λ (.fnptr n)
  /-- `old(g)`, `old(T.slots[i].f)` -- nur in `ensures`: der Wert beim Eintritt. -/
  | oldG (g : D.Glob) (hL : gdarf D g Λ) : Expr Γ Λ (D.gtyp g)
  | oldS (t : D.Tab) (f : D.Feld t) (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
      Expr Γ Λ (D.typ t f)
  | widen (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (e : Expr Γ Λ (.int lo hi)) : Expr Γ Λ (.int lo' hi')
  | add (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int (l1 + l2) (h1 + h2))
  | sub (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int (l1 - h2) (h1 - l2))
  | neg (a : Expr Γ Λ (.int lo hi)) : Expr Γ Λ (.int (-hi) (-lo))
  | mul (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
                     (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))))
  /-- `/` `%` -- `M102`: Nenner in `1 ..`, Zaehler in `0 ..` («SG-3»). -/
  | div (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 h1)
  | rem (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 (h2 - 1))
  /-- Vorzeichenbehaftete Division und Rest («SG-3», zweiter Satz): der Nenner schliesst
      die Null aus (`1 ≤ lo₂` oder `hi₂ ≤ −1`); Ergebnis in `−M .. M`. -/
  | sdiv (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int (-(betragMax l1 h1)) (betragMax l1 h1))
  | srem (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1))
  /-- `n` Bytes ab Index `i` eines Bytetraegers, als EINE Zahl («SG-16»): `offset_into`,
      `@bitpos`, `embeds` und die zweite Sicht auf dieselben Bytes sind Lesungen dieser
      Form. Der Bereich des Index plus `n` liegt in der Tabelle -- das ist die Schranke am
      Versatz, als Attribut. -/
  | getBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ) :
      Expr Γ Λ (.int 0 (256 ^ n - 1))
  /-- `&` `|` `^` `<<` `>>` `~` -- `M137`: nur ueber nichtnegativen Bereichen; `|`, `^`, `~`
      nennen die Breite. `~a` ist `a ^ (2^w − 1)`. -/
  | band (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 h1)
  | bor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int 0 (2 ^ w - 1))
  | bxor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ (.int 0 (2 ^ w - 1))
  | shl (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 (h1 * 2 ^ h2.toNat))
  | shr (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) :
      Expr Γ Λ (.int 0 h1)
  | lt (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ .bool
  | le (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ .bool
  | eq (a : Expr Γ Λ (.int l1 h1)) (b : Expr Γ Λ (.int l2 h2)) : Expr Γ Λ .bool
  /-- Gleitkommavergleiche -- total, weil ein `Val (.fl …)` ENDLICH ist (`finite`): die
      Trichotomie gilt, die NaN-Vierteilung («F») gibt es nicht. -/
  | fllt (a : Expr Γ Λ (.fl l1 h1)) (b : Expr Γ Λ (.fl l2 h2)) : Expr Γ Λ .bool
  | flle (a : Expr Γ Λ (.fl l1 h1)) (b : Expr Γ Λ (.fl l2 h2)) : Expr Γ Λ .bool
  | and (a b : Expr Γ Λ .bool) : Expr Γ Λ .bool
  | or (a b : Expr Γ Λ .bool) : Expr Γ Λ .bool
  | not (a : Expr Γ Λ .bool) : Expr Γ Λ .bool
  | none (n : Int) : Expr Γ Λ (.opt n)
  | some (e : Expr Γ Λ (.index n)) : Expr Γ Λ (.opt n)
  | istSome (e : Expr Γ Λ (.opt n)) : Expr Γ Λ .bool
  | case (cs : List (Option Ty)) (i : Fin cs.length)
      (nutz : NutzlastExpr Γ Λ (cs.get i)) : Expr Γ Λ (.sum cs)
  | why (n : Nat) (r : Fin n) : Expr Γ Λ (.why n)
  /-- `forall k in slots of T : pred` / `elems of` / `queue` -- der Binder traegt den Index. -/
  | forallSlots (t : D.Tab) (body : Expr (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
      Expr Γ Λ .bool
  | existsSlots (t : D.Tab) (body : Expr (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
      Expr Γ Λ .bool
  /-- `a reaches b via f` -- die Kette ueber ein `option index into Self`-Feld, mit `count`
      Schritten Treibstoff (mehr Schritte als Slots wiederholen einen). `descendants of`,
      `ancestors of` und `chain(…) in` sind `forallSlots` mit `reaches` als Filter. -/
  | reaches (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
      (a b : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr Γ Λ .bool
  /-- Two references name the same cell. -/
  | refEq (a b : Expr Γ Λ (.ref n)) : Expr Γ Λ .bool
  /-- `r->f` into the OPEN table number `n` -- under the same guards as a slot of `t`. -/
  | slotRef (r : Expr Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t) (ho : D.offen t = true)
      (f : D.Feld t) (hL : darf D t Λ) : Expr Γ Λ (D.typ t f)
  /-- The empty array literal (2026-10-25: aggregate values). -/
  | arrNil : Expr Γ Λ (.arr τ 0)
  /-- `[a, rest…]`: one element in front of an array literal. -/
  | arrCons (a : Expr Γ Λ τ) (rest : Expr Γ Λ (.arr τ n)) : Expr Γ Λ (.arr τ (n + 1))
  /-- `a[i]`: the element at an index of the array's length. -/
  | arrGet (a : Expr Γ Λ (.arr τ n)) (i : Expr Γ Λ (.index n)) : Expr Γ Λ τ
  /-- The array with the element at `i` replaced by `v` (a value; `a[i] = v` on a local binds it). -/
  | arrSet (a : Expr Γ Λ (.arr τ n)) (i : Expr Γ Λ (.index n)) (v : Expr Γ Λ τ) : Expr Γ Λ (.arr τ n)
  /-- A string literal: its UTF-8 bytes, at most the declared maximum. -/
  | strLit (bs : List (Zahl 0 255)) (h : bs.length ≤ n) : Expr Γ Λ (.str n)
  /-- `lenof(s)`: the length of a string. -/
  | strLen (s : Expr Γ Λ (.str n)) : Expr Γ Λ (.int 0 n)
  /-- `s + t`: the concatenation, its maximum the sum of the maxima. -/
  | strCat (s : Expr Γ Λ (.str n)) (t : Expr Γ Λ (.str m)) : Expr Γ Λ (.str (n + m))
  /-- `s[i]`: the byte at position `i`, `0` outside the length (the bound is the contract's). -/
  | strGet (s : Expr Γ Λ (.str n)) (i : Expr Γ Λ (.int lo hi)) : Expr Γ Λ (.int 0 255)
  /-- `s == t`: the same bytes. -/
  | strEq (s : Expr Γ Λ (.str n)) (t : Expr Γ Λ (.str m)) : Expr Γ Λ .bool
  /-- `s < t`: lexicographic over the bytes. -/
  | strLt (s : Expr Γ Λ (.str n)) (t : Expr Γ Λ (.str m)) : Expr Γ Λ .bool
  /-- A string under the maximum `m` (`let t : string max m = s`): the front end writes it for `n ≤ m`. -/
  | strWeit (m : Nat) (s : Expr Γ Λ (.str n)) : Expr Γ Λ (.str m)
  /-- `if c then a else b` as a value: the compare form of `exchange` and an `update` body with `if`
      (stage 0, 2026-10-26). -/
  | wenn (c : Expr Γ Λ .bool) (a b : Expr Γ Λ τ) : Expr Γ Λ τ
  /-- `e` narrowed to `lo' .. hi'`, else `sonst`: the binder of an `update` body under the guard of its branch,
      where `sonst` is unreachable (stage 0, 2026-10-26). -/
  | eng (e : Expr Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Expr Γ Λ (.int lo' hi')) : Expr Γ Λ (.int lo' hi')

inductive NutzlastExpr : Ctx → List (Res D) → Option Ty → Type where
  | empty : NutzlastExpr Γ Λ none
  | val (e : Expr Γ Λ τ) : NutzlastExpr Γ Λ (some τ)

end

inductive Args : Ctx → List (Res D) → List Ty → Type where
  | nil : Args Γ Λ []
  | cons (e : Expr D Γ Λ τ) (rest : Args Γ Λ τs) : Args Γ Λ (τ :: τs)

/-! ## 4. Anweisungen -- `stmt`, `block`, und der Block, der nicht abfaellt -/

inductive ErgExpr (Γ : Ctx) (Λ : List (Res D)) : Option Ty → Type where
  | empty : ErgExpr Γ Λ none
  | val (e : Expr D Γ Λ τ) : ErgExpr Γ Λ (some τ)

/-- Die Gleitkommarechnung («F»): jede Operation nennt den Bereich ihres Ergebnisses; die
    Maschine rechnet, und das Ergebnis wird gegen den Bereich gehalten (`rounded`). -/
inductive GleitOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr

variable (V : Vertrag D)

mutual

inductive Stmt : Bool → Ctx → List (Res D) → List (Res D) → Type where
  | assignSlot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ
  /-- `p->f = e;` -- Schreiben DURCH einen `rw`-Zeiger (`R002`/`R003`: kein `w` ohne Recht). -/
  | assignThru (p : Expr D Γ Λ (.ptr n true)) (t : D.Tab) (ht : D.tabNr n = some t)
      (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (e : Expr D Γ Λ (D.typ t f))
      (hw : V.schreibt t = true) (hL : darf D t Λ) : Stmt l Γ Λ Λ
  | assignGlob (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `n` Bytes ab Index `i` schreiben («SG-16») -- ein Feld eines `format` ueber einem
      Bytetraeger setzen. -/
  | putBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t)
      (e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  | assignVar (x : Var Γ τ) (e : Expr D Γ Λ τ) : Stmt l Γ Λ Λ
  /-- `T.slots[i].s = B;` an einem `state`-Feld: der Uebergang `von -> nach` ist ERKLAERT
      (`state S { … }`), und dass das Feld gerade auf `von` steht, ist die Logik des
      Schreibers (`Logik.uebergang`). -/
  | shift (t : D.Tab) (f : D.Feld t) (hτ : D.typ t f = .int lo hi)
      (i : Expr D Γ Λ (.index (D.count t))) (von nach : Int) (hn : lo ≤ nach ∧ nach ≤ hi)
      (he : D.erlaubt t f von nach = true) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ
  | ite (c : Expr D Γ Λ .bool) (t e : Block l Γ Λ Λ') : Stmt l Γ Λ Λ'
  | onOption (o : Expr D Γ Λ (.opt n)) (p : Block l (.index n :: Γ) Λ Λ') (a : Block l Γ Λ Λ') :
      Stmt l Γ Λ Λ'
  | onTag (v : Expr D Γ Λ (.sum cs)) (arms : Arms l Γ Λ Λ' cs) : Stmt l Γ Λ Λ'
  | onWhy (r : Expr D Γ Λ (.why n)) (arms : GrundArms l Γ Λ Λ' n) : Stmt l Γ Λ Λ'
  /-- `f(a, b);` -/
  | call (f : D.Fn) (args : Args D Γ Λ (D.params f)) (hp : RufPasst D V (D.signatur f) Λ)
      (hr : D.gruende f = 0) : Stmt l Γ Λ (nach D f Λ)
  /-- `p(a, b);` durch einen Funktionszeiger («B8»): der Vertrag steht am TYP. -/
  | callInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0) :
      Stmt l Γ Λ (nachSig D (D.sigNr n) Λ)
  /-- `locks L { … }` / `observes R { … }` -- Rang groesser als alles Gehaltene (`H006`). -/
  | locks (L : D.Lock) (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L)
      (body : Block l Γ (.held L :: Λ) (.held L :: Λ)) : Stmt l Γ Λ Λ
  /-- `breaking I { … }` -- die Invariante ruht; ihre Wiederherstellung wird am `return`
      verlangt wie ohne `breaking` (`schuldet`). Der Name steht im Term, damit er
      nachgelesen werden kann (`D013`). -/
  | breaking (i : D.Inv) (body : Block l Γ Λ Λ') : Stmt l Γ Λ Λ'
  | traverse (t : D.Tab) (inv : Expr D Γ Λ .bool) (body : Block true (.index (D.count t) :: Γ) Λ Λ) :
      Stmt l Γ Λ Λ
  | retry (n : Nat) (bis : Expr D Γ Λ .bool) (body : Block true Γ Λ Λ) (ueberlauf : Block l Γ Λ Λ) :
      Stmt l Γ Λ Λ
  | forever (a : D.Annahme) (inv : Expr D Γ Λ .bool) (body : Block true Γ Λ Λ) : Stmt l Γ Λ Λ
  | axiomCall (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `R = e;` an einem Register (`transition` ist dieselbe Anweisung mit dem Spiegel): die
      Klasse erlaubt das Schreiben, oder die Anweisung ist nicht ableitbar (`R005`/`R006`). -/
  | regWrite (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (e : Expr D Γ Λ (D.rtyp r)) :
      Stmt l Γ Λ Λ
  /-- `transition t { R.b : 0 -> 1 }` (Falle 4): EIN Lesen des Spiegels `m`, EIN Schreiben
      auf `R` -- die Bits `bits` unter der Maske `maske` ersetzt, alle anderen aus dem
      Spiegel. Dass `m` der Spiegel von `R` ist, steht in der Deklaration (`mirrors`); dass
      das Geraet die zwei Zugriffe in dieser Reihenfolge sieht, ist die Annahme am Geraet. -/
  | transition (r : D.Reg) (hk : (D.rklasse r).schreibbar = true) (m : D.Reg)
      (hm : D.spiegel r = some m) (hl : (D.rklasse m).lesbar = true) (maske bits : Int) :
      Stmt l Γ Λ Λ
  /-- `A = e publishes { p, q };` -- die Nutzlast D.Fn D.passt ist die erklaerte (`V001`-`V004` als Form);
      die Sichtbarkeit ist das Speichermodell, Annahme A10. -/
  | publish (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (payload : List D.Glob)
      (hp : payload = D.nutzlast g) (hw : V.gschreibt g = true) (hL : gdarf D g Λ) : Stmt l Γ Λ Λ
  /-- `advances a -> b` («B37»): die Marke steht auf Stufe `a`, und `b` ist die naechste. -/
  | advances (m : D.Marke) (a : Nat) (h : Res.marke m a ∈ Λ) (hs : a + 1 < D.stufen m) :
      Stmt l Γ Λ ((Λ.erase (.marke m a)) ++ [.marke m (a + 1)])
  /-- `retires t from space falsifier s` (S3): die Marke wird verbraucht, die Annahme genannt. -/
  | retires (m : D.Marke) (s : Nat) (h : Res.marke m s ∈ Λ) (a : D.Annahme) :
      Stmt l Γ Λ (Λ.erase (.marke m s))
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Stmt l Γ Λ Λ
  | retWhy (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Stmt l Γ Λ Λ
  | leave (h : l = true) : Stmt l Γ Λ Λ
  | next (h : l = true) : Stmt l Γ Λ Λ
  /-- `r->f = e;` into the OPEN table number `n` (`Expr.slotRef`). -/
  | assignSlotRef (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t) (ho : D.offen t = true)
      (f : D.Feld t) (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ) :
      Stmt l Γ Λ Λ

inductive Block : Bool → Ctx → List (Res D) → List (Res D) → Type where
  | nil : Block l Γ Λ Λ
  | cons (s : Stmt l Γ Λ Λ') (rest : Block l Γ Λ' Λ'') : Block l Γ Λ Λ''
  | bind (e : Expr D Γ Λ τ) (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  | bindCall (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
      (rest : Block l (τ :: Γ) (nach D f Λ) Λ') : Block l Γ Λ Λ'
  | bindCallInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Block l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ') : Block l Γ Λ Λ'
  | bindCallElse (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock l (.why (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Block l (τ :: Γ) (nach D f Λ) Λ') : Block l Γ Λ Λ'
  | bindAxiom (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = g(…) else (e) { … }` over a FALLIBLE foreign body (C-free lane, 2026-09-30):
      the answer is a value (`rest`) or a reason of the channel (`err`, an end block that does
      not fall off) -- `bindCallElse`'s shape over `D.agruende` instead of a signature. -/
  | bindAxiomElse (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock l (.why (D.agruende a) :: Γ) Λ)
      (rest : Block l (τ :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = R;` -- eine Registerlesung, lesbar nach Klasse; `requires … else` (B26) ist die
      Form `regLiesElse`. -/
  | regRead (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (rest : Block l (D.rtyp r :: Γ) Λ Λ') :
      Block l Γ Λ Λ'
  /-- `let x = R else (e) { … }` -- die Lesung ist fehlbar; die Geraetezusage (`requires`) ist
      die Bedingung, der `else`-Zweig faellt nicht ab. -/
  | regReadElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock l Γ Λ)
      (rest : Block l (D.rtyp r :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = A awaits { p, q };` -- the same payload as at the `publishes`; only at an atomic static
      (an await at a plain static would be an unordered read, Simon 2026-10-21). -/
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g) (hL : gdarf D g Λ)
      (ha : D.atomar g = true) (rest : Block l (D.gtyp g :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `let x = A exchange update(v) { … } …` -- Lesen, Rechnen, Schreiben: als EINE Anweisung
      (die Atomizitaet ist A10); `bounded`/`on_exceeded` sind die von `retry`. -/
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) (rest : Block l (D.gtyp g :: Γ) Λ Λ') : Block l Γ Λ Λ'
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock l Γ Λ)
      (rest : Block l (.int lo' hi' :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- `where`-Bedingung eines `format`-Felds, `requires` einer Lesung, jede benannte Absage
      (Regel 3): die Bedingung gilt, oder der `else`-Zweig -- der nicht abfaellt. -/
  | check (c : Expr D Γ Λ .bool) (sonst : Endblock l Γ Λ) (rest : Block l Γ Λ Λ') :
      Block l Γ Λ Λ'
  /-- Gleitkomma («F»): `let y = a op b;` mit erklaertem Bereich `lo .. hi` -- die Maschine
      rechnet (IEEE), das Ergebnis wird gegen den Bereich gehalten, und ein Ergebnis
      ausserhalb (oder NaN, Unendlich) ist `Logik.bereich` (since 2026-09-15, verdict F1:
      the kernel IEEE model decides it from the program's values; was `Hardware.ieee`). -/
  | float (op : GleitOp) (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) (lo hi : Int × Int)
      (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- Ein Gleitkommaliteral `1.5 rounded` in seinem Bereich. -/
  | floatLit (q : Int × Int) (lo hi : Int × Int) (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'
  /-- Eine Zahl als Gleitkommazahl, in ihrem Bereich. -/
  | floatOf (e : Expr D Γ Λ (.int l1 h1)) (lo hi : Int × Int) (rest : Block l (.fl lo hi :: Γ) Λ Λ') :
      Block l Γ Λ Λ'
  /-- `narrow x to finite` -- eine Gleitkommazahl in einen engeren Bereich, sonst der
      `else`-Zweig. -/
  | floatNarrow (e : Expr D Γ Λ (.fl l1 h1)) (lo hi : Int × Int) (sonst : Endblock l Γ Λ)
      (rest : Block l (.fl lo hi :: Γ) Λ Λ') : Block l Γ Λ Λ'

inductive Endblock : Bool → Ctx → List (Res D) → Type where
  | ret (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) : Endblock l Γ Λ
  | retWhy (r : Fin V.gruende) (hΛ : Λ.Perm V.ende) : Endblock l Γ Λ
  | leave (h : l = true) : Endblock l Γ Λ
  | next (h : l = true) : Endblock l Γ Λ
  | cons (s : Stmt l Γ Λ Λ') (rest : Endblock l Γ Λ') : Endblock l Γ Λ
  | bind (e : Expr D Γ Λ τ) (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = f(…);` at the top level of a body (or in an `else` that must not fall off):
      `Block.bindCall` with an end-block rest (Track P, 2026-10-18). Same premises; the rest is
      where the body ends. -/
  | bindCall (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
      (rest : Endblock l (τ :: Γ) (nach D f Λ)) : Endblock l Γ Λ
  /-- `let x = f(…) else (e) { … }` at the top level of a body: `Block.bindCallElse` with an
      end-block rest (Track P, 2026-10-18); the `else` branch is an end block over the reason. -/
  | bindCallElse (f : D.Fn) (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ)
      (hp : RufPasst D V (D.signatur f) Λ) (hr : 0 < D.gruende f)
      (err : Endblock l (.why (D.gruende f) :: Γ) (nach D f Λ))
      (rest : Endblock l (τ :: Γ) (nach D f Λ)) : Endblock l Γ Λ
  /-- `let x = g(…);` of a FOREIGN body at the top level of a body (or in an `else` that
      must not fall off): `Block.bindAxiom` with an end-block rest (C-free lane,
      2026-09-30). The same premises; the rest is where the body ends. -/
  | bindAxiom (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ
  /-- `Block.bindAxiomElse` with an end-block rest: a fallible foreign call at the top level
      of a body (C-free lane, 2026-09-30). -/
  | bindAxiomElse (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (he : D.aerg a = some τ)
      (hr : 0 < D.agruende a)
      (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
      (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
      (err : Endblock l (.why (D.agruende a) :: Γ) Λ)
      (rest : Endblock l (τ :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = R;` at the top level of a body (or in an `else` that must not fall off):
      `Block.regRead` with an end-block rest (Track P, 2026-10-21). -/
  | regRead (r : D.Reg) (hk : (D.rklasse r).lesbar = true) (rest : Endblock l (D.rtyp r :: Γ) Λ) :
      Endblock l Γ Λ
  /-- `let x = R else (e) { … }` at the top level of a body: `Block.regReadElse` with an
      end-block rest (Track P, 2026-10-21). -/
  | regReadElse (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
      (zusage : Expr D (D.rtyp r :: Γ) Λ .bool) (sonst : Endblock l Γ Λ)
      (rest : Endblock l (D.rtyp r :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = A awaits { p, q };` at the top level of a body: `Block.awaits` with an end-block
      rest (Track P, 2026-10-21). -/
  | awaits (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g) (hL : gdarf D g Λ)
      (ha : D.atomar g = true) (rest : Endblock l (D.gtyp g :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = p(…);` through a function pointer at the top level of a body: `Block.bindCallInd`
      with an end-block rest (Track P, 2026-10-21). -/
  | bindCallInd (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
      (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
      (rest : Endblock l (τ :: Γ) (nachSig D (D.sigNr n) Λ)) : Endblock l Γ Λ
  /-- `narrow x to lo .. hi else { … }` at the top level of a body (or in an `else` that must not fall off):
      `Block.narrow` with an end-block rest (stage 0, 2026-10-26). -/
  | narrow (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Endblock l Γ Λ)
      (rest : Endblock l (.int lo' hi' :: Γ) Λ) : Endblock l Γ Λ
  /-- `let x = A exchange update(v) { … } …` at the top level of a body: `Block.exchange` with an end-block
      rest (stage 0, 2026-10-26). -/
  | exchange (g : D.Glob) (neu : Expr D (D.gtyp g :: Γ) Λ (D.gtyp g)) (hw : V.gschreibt g = true)
      (hL : gdarf D g Λ) (rest : Endblock l (D.gtyp g :: Γ) Λ) : Endblock l Γ Λ
  /-- `if c { … } else { … }` as the last statement of a body, both branches ending (stage 0, 2026-10-26). -/
  | ite (c : Expr D Γ Λ .bool) (t e : Endblock l Γ Λ) : Endblock l Γ Λ

inductive Arms : Bool → Ctx → List (Res D) → List (Res D) → List (Option Ty) → Type where
  | nil : Arms l Γ Λ Λ []
  | cons (b : Block l (ArmCtx Γ c) Λ Λ') (rest : Arms l Γ Λ Λ' cs) : Arms l Γ Λ Λ' (c :: cs)

inductive GrundArms : Bool → Ctx → List (Res D) → List (Res D) → Nat → Type where
  | nil : GrundArms l Γ Λ Λ 0
  | cons (b : Block l Γ Λ Λ') (rest : GrundArms l Γ Λ Λ' n) : GrundArms l Γ Λ Λ' (n + 1)

end

/-! ## 5. Das Programm -- Ruempfe und Vertraege zu den Signaturen -/

def vertragVon (f : D.Fn) : Vertrag D := Vertrag.vonSig D (D.signatur f)

def ErgCtx (Γ : Ctx) : Option Ty → Ctx
  | none => Γ
  | some τ => τ :: Γ

def invSicht (i : D.Inv) : List (Res D) :=
  (D.traeger i).foldr (fun t acc => (D.braucht t).map (Res.von D) ++ acc) []

/-- Ein Programm: je Funktion `requires`, `ensures` (mit `refines`: die `ensures` der
    Spezifikation sind darin enthalten -- eine Konjunktion, kein zweiter Kanal) und ein
    Rumpf, der nicht abfaellt; je Invariante ihr Praedikat. -/
structure Programm where
  invariante : ∀ i : D.Inv, Expr D [] (invSicht D i) .bool
  requires : ∀ f : D.Fn, Expr D (D.params f) (Signatur.anfang D (D.signatur f)) .bool
  ensures : ∀ f : D.Fn, Expr D (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende .bool
  rumpf : ∀ f : D.Fn, Endblock D (vertragVon D f) false (D.params f) (Signatur.anfang D (D.signatur f))
  /-- `entry … via idt dispatch f` (Opus agent H, 2026-09-26, OFFEN O19): `f` is entered by
      HARDWARE -- an interrupt handler, the `Kontext::unterbricht` of the Rust checker
      (`kontexte.rs`, `H102`). A thread whose root is such a function preempts the thread
      running on its core (`KernPlan`, `Zielsatz/Spec.lean`). Default: no handler, so every
      program written before this field is the program of before. -/
  unterbricht : D.Fn → Bool := fun _ => false

end Gabbro.Grammatik
