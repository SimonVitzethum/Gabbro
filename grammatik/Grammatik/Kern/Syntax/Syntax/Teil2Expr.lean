module

public import Grammatik.Kern.Syntax.Typen.Teil2
public import Grammatik.Kern.Syntax.Syntax.Teil1
public import Grammatik.Kern.Syntax.Typen.IntBuiltin

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
  | thru (p : Expr Γ Λ (.ptr (.table n (true, rw) space))) (t : D.Tab) (ht : D.capTab space n = some t) (f : D.Feld t)
      (i : Expr Γ Λ (.index (D.count t))) (hL : darf D t Λ) : Expr Γ Λ (D.typ t f)
  /-- Der Zeiger auf einen Traeger -- die einzige Adresse, die es gibt: die eines DEKLARIERTEN
      Dings. Es gibt keine Adresse eines Ausdrucks (`SYNTAX.md` §4, `fnvalue`). -/
  | ptrOf (t : D.Tab) (n : Nat) (ht : D.capTab space n = some t) (rw : Bool × Bool) : Expr Γ Λ (.ptr (.table n rw space))
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
  /-- C13: a closed typed integer builtin with ONE operand (`clz`, `ctz`, `log2Floor`, `popcount`,
      `bswap16/32/64`); its width is in the operation (`IntBuiltin`), never read off an interval. -/
  | intBuiltin1 (op : IntBuiltin [τ1] τ) (a : Expr Γ Λ τ1) : Expr Γ Λ τ
  /-- C13: a closed typed integer builtin with TWO operands (`addW`, `subW`, `mulW`, `shlW`, `addS`,
      `rotl`, `rotr`). -/
  | intBuiltin2 (op : IntBuiltin [τ1, τ2] τ) (a : Expr Γ Λ τ1) (b : Expr Γ Λ τ2) : Expr Γ Λ τ
  /-- C13: the bounded count fold -- how many of the `n` indices `0 ..< n` satisfy the predicate; the
      binder carries the index, the result is at most `n`. -/
  | count (n : Nat) (body : Expr (.index (n : Int) :: Γ) Λ .bool) : Expr Γ Λ (.int 0 (n : Int))

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

def ErgCtx (Γ : Ctx) : Option Ty → Ctx
  | none => Γ
  | some τ => τ :: Γ

/-- **The reason channel as a type** (C08): the error of `n` reasons, as `Block`
    and `Endblock` bind it behind `else`. -/
def reasonTy (n : Nat) : Ty := .why n


end Gabbro.Grammatik
