/-
  Datei:      Grammatik/Typen.lean
  Gegenstand: Die TYPEN der Grammatik, und die Werte, die sie tragen. **Jede Zahl traegt
              ihren Bereich** -- ein `u32` ohne `in` gibt es in dieser Grammatik nicht; es
              ist `u32 in 0 .. 4294967295`, ausgeschrieben.

  QUELLSAETZE
    dokumente/SYNTAX.md:411   -- `intty = ( "u8"|…|"i64" ) [ "in" range ]`
    dokumente/SYNTAX.md:715   -- "M1 acts here and nowhere else: every operation must stay
                                 within the range of its result type"
    dokumente/SYNTAX.md:719   -- "Division and remainder demand a denominator whose range
                                 excludes zero"
    dokumente/SYNTAX.md:406   -- `indexty = [ "option" ] "index" "into" ident` -- der ERZEUGTE
                                 Indextyp einer Tabelle, `0 ..< count`
    dokumente/SYNTAX.md:441   -- `variants` -- der `tagged`-Typ, geschlossen, ohne Auffangzweig
    dokumente/SYNTAX.md:1331  -- `reason` -- die Faelle des Fehlerkanals

  WAS HIER STEHT
    `Ty`  -- die Typen: Zahl mit Bereich, Wahrheitswert, Optionsindex mit Schranke, Summe
             mit Nutzlasten, Grund.
    `Val` -- der WERT eines Typs, als Lean-Typ: eine Zahl im Bereich ist ein Paar aus Zahl
             und Beweis. Ein Wert ausserhalb seines Bereichs ist damit kein Wert -- er ist
             nicht konstruierbar. Das ist der ganze Mechanismus M1, als Typ.
    die Rechnung: `add`, `sub`, `mul`, `div`, `rem`, die Bits, die Schiebungen -- jede
             liefert einen Wert im GERECHNETEN Bereich, und der Beweis steht daneben.
-/

namespace Gabbro.Grammatik

/-! ## 1. Die Typen -/

/-- Die Typen der Kernsprache. -/
inductive Ty where
  /-- `intty "in" range` -- eine Zahl in `lo .. hi`. -/
  | int (lo hi : Int)
  | bool
  /-- `option index into T` -- abwesend, oder ein Index in `0 ..< n`. -/
  | opt (n : Int)
  /-- `tagged type` -- die Faelle, je mit oder ohne Zahl-Nutzlast im Bereich. -/
  | sum (cases : List (Option (Int × Int)))
  /-- `reason` -- `n` Gruende. -/
  | grund (n : Nat)
  /-- `never` -- der Typ ohne Wert: die Antwort einer `divergent`/`prim` Funktion. -/
  | never
  /-- `f32`/`f64 in lo .. hi` («F») -- die Schranken als Brueche `(z, n)`, weil `0.5` eine
      Schranke ist. Der Wert ist eine ENDLICHE Gleitkommazahl der Maschine im Bereich. -/
  | fl (lo hi : Int × Int)
  /-- `fn(…) -> T effects {…} costs …` -- ein Funktionszeiger mit seinem Vertrag («B8»):
      der Wert ist eine Funktion, deren Signatur GENAU diese ist. Die Signatur steht hier
      als Nummer; welche das ist, sagt die Deklaration (`sig`). -/
  | fnptr (sig : Nat)
  /-- `ptr<space, rights> T` -- ein Zeiger auf den Traeger Nummer `t` (M3). Der Wert ist die
      FAEHIGKEIT, `t` anzusprechen; jeder Zugriff hindurch braucht die Waechter von `t`
      wie ein direkter. Zwei Zeiger auf `t` sind damit zwei Namen fuer EINE Welt unter EINEM
      Waechter -- der Alias kostet keine Sicherheit, nur Logik (§15.8). -/
  | ptr (t : Nat) (rw : Bool)
  deriving DecidableEq, Repr

/-- Ein Index in `0 ..< n`: der Typ, den `index into T` erzeugt. -/
abbrev Ty.index (n : Int) : Ty := .int 0 (n - 1)

/-! ## 2. Die Werte -/

/-- Eine Zahl in ihrem Bereich. -/
structure Zahl (lo hi : Int) where
  n : Int
  lo_le : lo ≤ n
  le_hi : n ≤ hi

/-- Die Nutzlast eines Falls. -/
def Nutzlast : Option (Int × Int) → Type
  | none => Unit
  | some (lo, hi) => Zahl lo hi

/-- Ein Bruch als Gleitkommazahl. -/
def bruch (q : Int × Int) : Float := Float.ofInt q.1 / Float.ofInt q.2

/-- Eine endliche Gleitkommazahl im Bereich -- kein NaN, keine Unendlichkeit (`finite`). -/
structure Gleit (lo hi : Int × Int) where
  x : Float
  endlich : x.isFinite = true
  lo_le : bruch lo ≤ x
  le_hi : x ≤ bruch hi

/-- Der Wert eines Typs. **Ein Wert ausserhalb seines Typs existiert nicht.**
    `F` sind die Funktionen des Programms, `sig` ihre Signaturnummer -- ein Funktionszeiger
    ist eine Funktion mit GENAU der Signatur seines Typs. -/
def Val (F : Type) (sig : F → Nat) : Ty → Type
  | .int lo hi => Zahl lo hi
  | .bool => Bool
  | .opt n => Option (Zahl 0 (n - 1))
  | .sum cs => Σ i : Fin cs.length, Nutzlast (cs.get i)
  | .grund n => Fin n
  | .never => Empty
  | .fl lo hi => Gleit lo hi
  | .fnptr n => { f : F // sig f = n }
  | .ptr _ _ => Unit

theorem Val.int_bereich {F : Type} {sig : F → Nat} {lo hi : Int} (v : Val F sig (.int lo hi)) :
    lo ≤ v.n ∧ v.n ≤ hi := ⟨v.lo_le, v.le_hi⟩

/-- Ein Wert eines engeren Bereichs ist einer des weiteren -- die eine Umwandlung, die die
    Grammatik zulaesst (`M104` in der sicheren Richtung). -/
def Zahl.weiter {lo hi lo' hi' : Int} (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (v : Zahl lo hi) :
    Zahl lo' hi' := ⟨v.n, by have := v.lo_le; omega, by have := v.le_hi; omega⟩

/-! ## 3. Die Rechnung -- jede Operation mit dem Bereich, den `M104` ihr gibt -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem le_imax_left (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem le_imax_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega

def Zahl.add {l1 h1 l2 h2 : Int} (a : Zahl l1 h1) (b : Zahl l2 h2) : Zahl (l1 + l2) (h1 + h2) :=
  ⟨a.n + b.n, by have := a.lo_le; have := b.lo_le; omega,
               by have := a.le_hi; have := b.le_hi; omega⟩

def Zahl.sub {l1 h1 l2 h2 : Int} (a : Zahl l1 h1) (b : Zahl l2 h2) : Zahl (l1 - h2) (h1 - l2) :=
  ⟨a.n - b.n, by have := a.lo_le; have := b.le_hi; omega,
               by have := a.le_hi; have := b.lo_le; omega⟩

def Zahl.neg {lo hi : Int} (a : Zahl lo hi) : Zahl (-hi) (-lo) :=
  ⟨-a.n, by have := a.le_hi; omega, by have := a.lo_le; omega⟩

/-- Das Vier-Ecken-Produkt (`Bereich.lean`, `mul_korrekt`; hier fuer den WERT). -/
theorem produkt_in_ecken (p q r s u v : Int) (hpu : p ≤ u) (huq : u ≤ q) (hrv : r ≤ v)
    (hvs : v ≤ s) :
    imin (imin (p*r) (p*s)) (imin (q*r) (q*s)) ≤ u*v
    ∧ u*v ≤ imax (imax (p*r) (p*s)) (imax (q*r) (q*s)) := by
  have hpv_qv : (p*v ≤ u*v ∧ u*v ≤ q*v) ∨ (q*v ≤ u*v ∧ u*v ≤ p*v) := by
    rcases Int.lt_or_le v 0 with hv | hv
    · right
      exact ⟨Int.mul_le_mul_of_nonpos_right huq (Int.le_of_lt hv),
             Int.mul_le_mul_of_nonpos_right hpu (Int.le_of_lt hv)⟩
    · left
      exact ⟨Int.mul_le_mul_of_nonneg_right hpu hv, Int.mul_le_mul_of_nonneg_right huq hv⟩
  have hp : (p*r ≤ p*v ∧ p*v ≤ p*s) ∨ (p*s ≤ p*v ∧ p*v ≤ p*r) := by
    rcases Int.lt_or_le p 0 with hp0 | hp0
    · right
      exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hp0) hvs,
             Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hp0) hrv⟩
    · left
      exact ⟨Int.mul_le_mul_of_nonneg_left hrv hp0, Int.mul_le_mul_of_nonneg_left hvs hp0⟩
  have hq : (q*r ≤ q*v ∧ q*v ≤ q*s) ∨ (q*s ≤ q*v ∧ q*v ≤ q*r) := by
    rcases Int.lt_or_le q 0 with hq0 | hq0
    · right
      exact ⟨Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hq0) hvs,
             Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hq0) hrv⟩
    · left
      exact ⟨Int.mul_le_mul_of_nonneg_left hrv hq0, Int.mul_le_mul_of_nonneg_left hvs hq0⟩
  have l1 := imin_le_left (imin (p*r) (p*s)) (imin (q*r) (q*s))
  have l2 := imin_le_right (imin (p*r) (p*s)) (imin (q*r) (q*s))
  have l3 := imin_le_left (p*r) (p*s)
  have l4 := imin_le_right (p*r) (p*s)
  have l5 := imin_le_left (q*r) (q*s)
  have l6 := imin_le_right (q*r) (q*s)
  have u1 := le_imax_left (imax (p*r) (p*s)) (imax (q*r) (q*s))
  have u2 := le_imax_right (imax (p*r) (p*s)) (imax (q*r) (q*s))
  have u3 := le_imax_left (p*r) (p*s)
  have u4 := le_imax_right (p*r) (p*s)
  have u5 := le_imax_left (q*r) (q*s)
  have u6 := le_imax_right (q*r) (q*s)
  rcases hpv_qv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hp with ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
    rcases hq with ⟨q1, q2⟩ | ⟨q1, q2⟩ <;> omega

def Zahl.mul {l1 h1 l2 h2 : Int} (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
         (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))) :=
  ⟨a.n * b.n, (produkt_in_ecken l1 h1 l2 h2 a.n b.n a.lo_le a.le_hi b.lo_le b.le_hi).1,
              (produkt_in_ecken l1 h1 l2 h2 a.n b.n a.lo_le a.le_hi b.lo_le b.le_hi).2⟩

/-! ### Division und Rest -- ueber NICHTNEGATIVEN Bereichen, mit POSITIVEM Nenner

    Das ist enger als `M102` ("der Nenner schliesst die Null aus"): die Grammatik hier
    verlangt `0 ≤ lo₁` und `1 ≤ lo₂`. Grund: fuer nichtnegative Operanden fallen C's
    Abschneiden gegen Null und die Ganzzahldivision zusammen, und `0 ≤ a / b ≤ a` ist ein
    Satz. Fuer Vorzeichen braeuchte es die Fallunterscheidung -- ein zweiter Satz, der hier
    nicht steht («SG-3» in SYNTAX.md nennt die Grenze). -/

theorem Int.tdiv_eq_ediv_nonneg {a b : Int} (ha : 0 ≤ a) : a.tdiv b = a / b := by
  rw [Int.tdiv_eq_ediv]; simp [ha]

def Zahl.div {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 h1 :=
  ⟨a.n.tdiv b.n, by
      have ha := a.lo_le; have hb := b.lo_le
      rw [Int.tdiv_eq_ediv_nonneg (by omega)]
      exact Int.ediv_nonneg (by omega) (by omega),
    by
      have ha := a.lo_le; have hb := b.lo_le; have hh := a.le_hi
      rw [Int.tdiv_eq_ediv_nonneg (by omega)]
      have := Int.ediv_le_self b.n (show 0 ≤ a.n by omega)
      omega⟩

def Zahl.rem {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 (h2 - 1) :=
  ⟨a.n.tmod b.n, by
      have ha := a.lo_le; have hb := b.lo_le
      rw [Int.tmod_eq_emod_of_nonneg (by omega)]
      exact Int.emod_nonneg _ (by omega),
    by
      have ha := a.lo_le; have hb := b.lo_le; have hh := b.le_hi
      rw [Int.tmod_eq_emod_of_nonneg (by omega)]
      have := Int.emod_lt_of_pos a.n (show 0 < b.n by omega)
      omega⟩

/-! ### Vorzeichenbehaftete Division -- der zweite Satz («SG-3», seit 2026-09-09 abends)

    Ueber einem Nenner, dessen Bereich die Null ausschliesst (`1 ≤ lo₂` ODER `hi₂ ≤ -1`),
    ist C's abschneidende Division `tdiv` total, und `|a tdiv b| ≤ |a|`. Der Bereich des
    Ergebnisses ist damit `-M .. M` mit `M = max |lo₁| |hi₁|`; der Rest liegt in
    `-(N-1) .. N-1` mit `N = max |lo₂| |hi₂|`. Beides ist ein Satz, kein Fall fuer `narrow`. -/

/-- Der Betrag der Schranken. -/
def betragMax (lo hi : Int) : Int := (max lo.natAbs hi.natAbs : Nat)

theorem tdiv_natAbs_le (a b : Int) : (a.tdiv b).natAbs ≤ a.natAbs := by
  rw [Int.natAbs_tdiv]; exact Nat.div_le_self _ _

theorem tmod_natAbs_lt (a b : Int) (hb : b ≠ 0) : (a.tmod b).natAbs < b.natAbs := by
  rw [Int.natAbs_tmod]; exact Nat.mod_lt _ (Int.natAbs_pos.mpr hb)

def Zahl.sdiv {l1 h1 l2 h2 : Int} (_hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl (-(betragMax l1 h1)) (betragMax l1 h1) :=
  ⟨a.n.tdiv b.n, by
      have ha := a.lo_le; have hh := a.le_hi; have := tdiv_natAbs_le a.n b.n
      unfold betragMax; omega,
    by
      have ha := a.lo_le; have hh := a.le_hi; have := tdiv_natAbs_le a.n b.n
      unfold betragMax; omega⟩

def Zahl.srem {l1 h1 l2 h2 : Int} (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1) :=
  ⟨a.n.tmod b.n, by
      have hb1 := b.lo_le; have hb2 := b.le_hi
      have := tmod_natAbs_lt a.n b.n (by omega)
      unfold betragMax; omega,
    by
      have hb1 := b.lo_le; have hb2 := b.le_hi
      have := tmod_natAbs_lt a.n b.n (by omega)
      unfold betragMax; omega⟩

theorem Int.pow_nonneg_two (k : Nat) : (0 : Int) ≤ 2 ^ k := by
  have e : ((2 ^ k : Nat) : Int) = (2:Int) ^ k := by simp
  have : (0:Int) ≤ ((2 ^ k : Nat) : Int) := Int.natCast_nonneg _
  omega

/-! ### Bits und Schiebungen -- ueber NICHTNEGATIVEN Bereichen (`M137`) -/

/-- `a & b` ueber `0 ≤ a, b`: hoechstens `a`. -/
def Zahl.band {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (_h0' : 0 ≤ l2) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 h1 :=
  ⟨((a.n.toNat &&& b.n.toNat : Nat) : Int), by omega, by
      have ha := a.lo_le; have hh := a.le_hi
      have := Nat.and_le_left (n := a.n.toNat) (m := b.n.toNat)
      omega⟩

/-- Die Breite, in der `hi` liegt: `2 ^ w > hi`. Die Grammatik nennt sie an der Deklaration
    (`u8`, `u16`, …); hier ist sie ein Parameter mit Beweis. -/
def Zahl.bor {l1 h1 l2 h2 : Int} (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 (2 ^ w - 1) :=
  ⟨((a.n.toNat ||| b.n.toNat : Nat) : Int), by omega, by
      have ha := a.lo_le; have hh := a.le_hi; have hb := b.lo_le; have hh' := b.le_hi
      have e : ((2 ^ w : Nat) : Int) = (2:Int) ^ w := by simp
      have := Nat.or_lt_two_pow (x := a.n.toNat) (y := b.n.toNat) (n := w) (by omega) (by omega)
      omega⟩

def Zahl.bxor {l1 h1 l2 h2 : Int} (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 (2 ^ w - 1) :=
  ⟨((a.n.toNat ^^^ b.n.toNat : Nat) : Int), by omega, by
      have ha := a.lo_le; have hh := a.le_hi; have hb := b.lo_le; have hh' := b.le_hi
      have e : ((2 ^ w : Nat) : Int) = (2:Int) ^ w := by simp
      have := Nat.xor_lt_two_pow (x := a.n.toNat) (y := b.n.toNat) (n := w) (by omega) (by omega)
      omega⟩

/-- `a << b` ist `a · 2^b`; die Schiebeweite ist eine Zahl in `0 .. h2`, und das Ergebnis
    liegt in `0 .. h1 · 2^h2`. -/
def Zahl.shl {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (_h0' : 0 ≤ l2) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 (h1 * 2 ^ h2.toNat) :=
  ⟨a.n * 2 ^ b.n.toNat, by
      have ha := a.lo_le
      exact Int.mul_nonneg (by omega) (Int.pow_nonneg_two _),
    by
      have ha := a.lo_le; have hh := a.le_hi; have hb := b.lo_le; have hh' := b.le_hi
      have hpow : (2 : Int) ^ b.n.toNat ≤ 2 ^ h2.toNat := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show b.n.toNat ≤ h2.toNat by omega)
        have e1 : ((2 ^ b.n.toNat : Nat) : Int) = (2:Int) ^ b.n.toNat := by simp
        have e2 : ((2 ^ h2.toNat : Nat) : Int) = (2:Int) ^ h2.toNat := by simp
        omega
      have s1 : a.n * 2 ^ b.n.toNat ≤ h1 * 2 ^ b.n.toNat :=
        Int.mul_le_mul_of_nonneg_right hh (Int.pow_nonneg_two _)
      have s2 : h1 * 2 ^ b.n.toNat ≤ h1 * 2 ^ h2.toNat :=
        Int.mul_le_mul_of_nonneg_left hpow (show (0:Int) ≤ h1 by omega)
      omega⟩

def Zahl.shr {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (_h0' : 0 ≤ l2) (a : Zahl l1 h1) (b : Zahl l2 h2) :
    Zahl 0 h1 :=
  ⟨a.n / 2 ^ b.n.toNat, by
      have ha := a.lo_le
      exact Int.ediv_nonneg (by omega) (Int.pow_nonneg_two _),
    by
      have ha := a.lo_le; have hh := a.le_hi
      have := Int.ediv_le_self (2 ^ b.n.toNat) (show 0 ≤ a.n by omega)
      omega⟩

/-! ## 4. Bytes -- die zweite Sicht auf dieselben Zellen («SG-16», seit 2026-09-09 abends)

    Ein Byte ist eine Zahl in `0 .. 255`, ein Bytetraeger eine Tabelle mit einem solchen
    Feld. `n` Bytes ab einem Index sind EINE Zahl in `0 .. 256^n − 1` (kleinstes zuerst,
    `endian little`; `big` ist dieselbe Liste umgedreht -- Zucker). Ein `format` ueber einem
    Bytetraeger ist damit eine SICHT: `offset_into`, `@bitpos`, `embeds` sind Lesungen von
    Bytes an einem Versatz, und zwei Sichten auf dieselben Bytes lesen dieselbe Welt. -/

abbrev Byte := Zahl 0 255

/-- `n` Bytes, kleinstes zuerst, zu einer Zahl. -/
def bytesZuZahl : List Byte → Int
  | [] => 0
  | b :: bs => b.n + 256 * bytesZuZahl bs

theorem bytesZuZahl_bereich (bs : List Byte) :
    0 ≤ bytesZuZahl bs ∧ bytesZuZahl bs ≤ 256 ^ bs.length - 1 := by
  induction bs with
  | nil => simp [bytesZuZahl]
  | cons b bs ih =>
      simp only [bytesZuZahl, List.length_cons]
      have h1 := b.lo_le; have h2 := b.le_hi
      have e : (256 : Int) ^ (bs.length + 1) = 256 ^ bs.length * 256 := Int.pow_succ _ _
      omega

/-- Eine Zahl in ihre `n` Bytes, kleinstes zuerst. -/
def zahlZuBytes : Nat → Int → List Byte
  | 0, _ => []
  | k + 1, z => ⟨z % 256, Int.emod_nonneg _ (by decide), by
                  have := Int.emod_lt_of_pos z (show (0:Int) < 256 by decide); omega⟩
                :: zahlZuBytes k (z / 256)

theorem zahlZuBytes_length (k : Nat) (z : Int) : (zahlZuBytes k z).length = k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp [zahlZuBytes, ih]

end Gabbro.Grammatik
