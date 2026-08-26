/-
  Datei:      Passlogik/Kosten.lean
  Gegenstand: Die KOSTENRECHNUNG -- `Ĉ` ist eine OBERE Schranke jedes Durchlaufs.

  MODELLIERT WIRD
    Eine Ausdrucks- und Anweisungssprache mit den vier Primitiven aus `SPRACHE.md` §7,
    die statisch gerechnete Zahl `Ĉ` und eine LAUFRELATION `laeuft s n` ("ein Durchlauf
    durch `s` fuehrt `n` Primitiven aus"). Bewiesen wird L1 aus `messung/K001.md`:
    `Ĉ(b) >= K(b, r)` fuer JEDEN Durchlauf `r`. Dazu L2 (Vergleich bei der kleinsten
    Belegung), die Schleifenmultiplikation und die Komposition von `held`.

  QUELLSAETZE
    dokumente/SPRACHE.md:940  -- "`costs` counts operations, and the unit is defined:
                                 1 op = one Gabbro primitive (assignment, arithmetic
                                 operation, load, store; a call counts the declared `costs`
                                 of the callee; a traversal counts body costs x domain
                                 bound; branches count the maximum)."
    dokumente/SPRACHE.md:949  -- "The four primitives are conclusive. An `if`, a `match`,
                                 a `return`, a `leave` cost NOTHING [...] And what is fixed
                                 at compile time costs nothing at run time."
    dokumente/SPRACHE.md:953  -- "What stands after a branch that ALWAYS leaves lies on the
                                 other path."
    dokumente/SPRACHE.md:1176 -- §9.3, Punkt 1/4: "Every lock declares `held <= K ops`. A
                                 `locks` block whose body costs exceed K is a compile
                                 error. [...] Die Latenzaussage je Wartestelle ist damit
                                 ableitbar (hoeherrangige Halter halten <= die Summe ihrer
                                 `held`)."
    messung/K001.md §1-§4     -- L1/L2, die Fallliste, und der gemessene Fehler
    messung/K001.md §3        -- "Bis zum 2026-08-24 rechnete der Pass
                                 `max over i (Ĉ(bed_i) + Ĉ(rumpf_i))` -- nur die EIGENE
                                 Bedingung je Zweig, und fuer `sonst` GAR KEINE."

  ANGENOMMEN STATT BEWIESEN
    (K1) **`Ĉ(konstanter Ausdruck) = 0` ist eine Aussage ueber den ERZEUGER.**
         `messung/K001.md` §5 nennt sie selbst "die schwaechste Stelle des ganzen
         Arguments": sie haengt an 6 976 Zeilen `emit.rs`, die niemand aufgeschrieben hat.
         Hier steht sie als Definition (`kostenA .konst = 0`) und damit als Annahme.
    (K2) Die Fallliste ist die aus `messung/K001.md` §3. Ob sie VOLLSTAENDIG ist -- ob
         also keine `StmtArt`-Variante fehlt --, ist eine Aussage ueber den Rust und
         kann hier nicht fallen. *Das ist derselbe Vorbehalt, den §7 dort selbst nennt.*
    (K3) `retry … bounded N ops`: dass ein Durchlauf innerhalb von `N` bleibt, ist die
         Zusage des `on_exceeded`-Waechters zur LAUFZEIT, nicht ein statischer Satz. Sie
         steht als Praemisse in der Laufrelation.
    (K4) Die Domaenenschranke `|D|` wird als Zahl GEGEBEN. Dass die gelesene Zahl die
         Maechtigkeit der Domaene IST, ist `kosten.domaenenschranke`, und dieser Satz
         steht auf `CONJECTURED` -- der `mappings of`-Fehler (2 048 statt 512^4) lebte
         genau in dieser Luecke. **Hier ist sie eine Annahme, keine Behauptung.**
-/

namespace Passlogik.Kosten

/-! ## 1. Die Sprache -/

variable {F : Type u}

/-- Ausdruecke. Die Kostenzahl je Form steht in `messung/K001.md` §3, Tafel 1. -/
inductive Ausdr (F : Type u) where
  /-- zur Uebersetzungszeit konstant, Zahl, `true`, `&f`, Grundwert, `result` -- **0** (K1) -/
  | konst  : Ausdr F
  /-- ein Ort `x.a[i].b` -- **1 + #Indizes** (ein Laden, plus je Indexrechnung eine) -/
  | ort    : Nat → Ausdr F
  /-- unaer -- **1 + Ĉ(e)** -/
  | unaer  : Ausdr F → Ausdr F
  /-- binaer -- **1 + Ĉ(a) + Ĉ(b)** -/
  | binaer : Ausdr F → Ausdr F → Ausdr F
  /-- ein Ruf -- die **deklarierten** Kosten des Gerufenen -/
  | ruf    : F → Ausdr F

/-- Eine Sperre mit Rang und Haltezeit (`SPRACHE.md`:1272, `lockdecl`). -/
structure Sperre where
  rang : Int
  held : Nat
deriving DecidableEq, Repr

mutual
/-- Anweisungen. -/
inductive Anw (F : Type u) where
  /-- eine Primitive tragende Anweisung (Zuweisung, Ausdrucksanweisung) -/
  | prim     : Ausdr F → Anw F
  | leer     : Anw F
  | folge    : Anw F → Anw F → Anw F
  /-- `if … else if … else` -- die Zweigkette ist FLACH, wie `WennStmt::zweige` -/
  | wenn     : Kette F → Anw F
  /-- `match` -- EIN Gegenstand, dann ein Sprung -/
  | passt    : Ausdr F → Zweige F → Anw F
  /-- `traverse … over D` -- Rumpf x Domaenenschranke (K4) -/
  | traverse : Nat → Anw F → Anw F
  /-- `retry … bounded N ops` -- die Schranke IST die Zusage (K3) -/
  | retry    : Nat → Anw F → Anw F
  /-- `locks L { … }` -- der Block selbst ist keine Primitive -/
  | sperrt   : Sperre → Anw F → Anw F
  /-- `return`, `leave`, `next` -- **kosten nichts** (`SPRACHE.md`:949) -/
  | sprung   : Anw F

/-- Die Zweigkette eines `if`. **Flach**, und genau daran hing der Fehler. -/
inductive Kette (F : Type u) where
  | ohneSonst : Kette F
  | mitSonst  : Anw F → Kette F
  | zweig     : Ausdr F → Anw F → Kette F → Kette F

/-- Die Zweige eines `match`. -/
inductive Zweige (F : Type u) where
  | keine : Zweige F
  | dazu  : Anw F → Zweige F → Zweige F
end

/-- Ein Programm: je Funktion ein Rumpf und eine deklarierte Kostenzahl. -/
structure KProgramm (F : Type u) where
  rumpf : F → Anw F
  dekl  : F → Nat

/-! ## 2. `Ĉ` -- was der Pass ausrechnet

    Die Zweigkette traegt den PRAEFIX der Bedingungen. `messung/K001.md` §3:
    `Ĉ(if …) = max( max_i ( P_i + Ĉ(rumpf_i) ), P_{n-1} + Ĉ(sonst) )` mit
    `P_i = Σ_{j<=i} Ĉ(bed_j)`. Die Rekursion unten traegt `P` als Parameter mit --
    **das ist dieselbe Rechnung, nur von links statt von rechts geschrieben.**
-/

def kostenA (dekl : F → Nat) : Ausdr F → Nat
  | .konst      => 0
  | .ort i      => 1 + i
  | .unaer e    => 1 + kostenA dekl e
  | .binaer a b => 1 + kostenA dekl a + kostenA dekl b
  | .ruf g      => dekl g

mutual
def kostenS (dekl : F → Nat) : Anw F → Nat
  | .prim e       => kostenA dekl e
  | .leer         => 0
  | .folge a b    => kostenS dekl a + kostenS dekl b
  | .wenn k       => kostenK dekl 0 k
  | .passt g z    => kostenA dekl g + kostenZ dekl z
  | .traverse b r => b * kostenS dekl r
  | .retry n _    => n
  | .sperrt _ r   => kostenS dekl r
  | .sprung       => 0

def kostenK (dekl : F → Nat) (praefix : Nat) : Kette F → Nat
  | .ohneSonst    => praefix
  | .mitSonst s   => praefix + kostenS dekl s
  | .zweig b r k  =>
      Nat.max (praefix + kostenA dekl b + kostenS dekl r)
              (kostenK dekl (praefix + kostenA dekl b) k)

def kostenZ (dekl : F → Nat) : Zweige F → Nat
  | .keine    => 0
  | .dazu s z => Nat.max (kostenS dekl s) (kostenZ dekl z)
end

/-! ## 3. Was ein DURCHLAUF kostet

    Die Laufrelation ist nichtdeterministisch: sie beschreibt JEDEN moeglichen Durchlauf.
    **Der Kurzschluss steht ausdruecklich darin** -- `messung/K001.md` §3 nennt ihn als
    Ueberschaetzung "in die richtige Richtung".

    **Und die Zweigkette ist der Ort, an dem der Fehler sass:** ein Durchlauf, der Zweig
    `i` nimmt, hat die Bedingungen `0 … i` AUSGEWERTET. In der Relation unten steht das
    als eigener Konstruktor `weiter`, und der Praefix entsteht von selbst.
-/

mutual
inductive laeuftA (P : KProgramm F) : Ausdr F → Nat → Prop where
  | konst  : laeuftA P .konst 0
  | ort (i : Nat) : laeuftA P (.ort i) (1 + i)
  | unaer  {e n} : laeuftA P e n → laeuftA P (.unaer e) (1 + n)
  | binaer {a b n m} : laeuftA P a n → laeuftA P b m → laeuftA P (.binaer a b) (1 + n + m)
  /-- **Kurzschluss:** `&&` wertet die rechte Seite nicht aus. -/
  | kurz   {a b n} : laeuftA P a n → laeuftA P (.binaer a b) (1 + n)
  /-- **Ein Ruf laeuft den Rumpf des Gerufenen.** *Keine Bedingung an den Graphen* --
      die Induktion laeuft ueber die ABLEITUNG, und ein endender Durchlauf hat eine
      endliche. -/
  | ruf    {g n} : laeuftS P (P.rumpf g) n → laeuftA P (.ruf g) n

inductive laeuftS (P : KProgramm F) : Anw F → Nat → Prop where
  | prim   {e n} : laeuftA P e n → laeuftS P (.prim e) n
  | leer   : laeuftS P .leer 0
  | folge  {a b n m} : laeuftS P a n → laeuftS P b m → laeuftS P (.folge a b) (n + m)
  | wenn   {k n} : laeuftK P k n → laeuftS P (.wenn k) n
  | passt  {g z n m} : laeuftA P g n → laeuftZ P z m → laeuftS P (.passt g z) (n + m)
  | traverse {b r k n} : k ≤ b → laeuftW P r k n → laeuftS P (.traverse b r) n
  /-- (K3) -- die Schranke ist die LAUFZEIT-Zusage des `on_exceeded`-Waechters. -/
  | retry  {n r m} : m ≤ n → laeuftS P (.retry n r) m
  | sperrt {L r n} : laeuftS P r n → laeuftS P (.sperrt L r) n
  | sprung : laeuftS P .sprung 0

inductive laeuftK (P : KProgramm F) : Kette F → Nat → Prop where
  | durch  : laeuftK P .ohneSonst 0
  | sonst  {s n} : laeuftS P s n → laeuftK P (.mitSonst s) n
  /-- Die Bedingung war WAHR: sie wurde ausgewertet, dann der Rumpf. -/
  | nimmt  {b r k n m} : laeuftA P b n → laeuftS P r m → laeuftK P (.zweig b r k) (n + m)
  /-- Die Bedingung war FALSCH: sie wurde ausgewertet, dann geht es weiter.
      **Genau dieser Konstruktor ist der Praefix.** -/
  | weiter {b r k n m} : laeuftA P b n → laeuftK P k m → laeuftK P (.zweig b r k) (n + m)

inductive laeuftZ (P : KProgramm F) : Zweige F → Nat → Prop where
  | hier {s z n} : laeuftS P s n → laeuftZ P (.dazu s z) n
  | dort {s z n} : laeuftZ P z n → laeuftZ P (.dazu s z) n

/-- `laeuftW P r k n`: der Rumpf `r` wurde `k`-mal durchlaufen und kostete zusammen `n`. -/
inductive laeuftW (P : KProgramm F) : Anw F → Nat → Nat → Prop where
  | null {r} : laeuftW P r 0 0
  | mehr {r k n m} : laeuftS P r n → laeuftW P r k m → laeuftW P r (k+1) (n+m)
end

/-! ### 3.1 Zwei Hilfslemmata zu `Nat.max` -- `omega` kennt es nicht -/

theorem le_max_links {a b c : Nat} (h : a ≤ b) : a ≤ Nat.max b c :=
  Nat.le_trans h (Nat.le_max_left b c)
theorem le_max_rechts {a b c : Nat} (h : a ≤ c) : a ≤ Nat.max b c :=
  Nat.le_trans h (Nat.le_max_right b c)
/-- Der Schritt der Wiederholung: `n + m <= (k+1) * c` aus `n <= c` und `m <= k * c`. -/
theorem wdh_schritt {n m k c : Nat} (h1 : n ≤ c) (h2 : m ≤ k * c) : n + m ≤ (k+1) * c := by
  have : (k+1) * c = k * c + c := by rw [Nat.succ_mul]
  omega

/-! ## 4. L1 -- DER SATZ: `Ĉ` ueberschaetzt nie

    `messung/K001.md` §1: *"`Ĉ(b) >= K(b, r)` fuer JEDEN Durchlauf `r`"*.

    Die eine Praemisse ist `K001` selbst an jeder Funktion: der Rumpf kostet nicht mehr
    als deklariert. **Sie ist es, die den Ruf traegt** -- und sie ist es auch, die an einer
    rekursiven Funktion fast unerfuellbar wird (§4.1).
-/

mutual
theorem deckt_A {P : KProgramm F} (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g) :
    ∀ {e n}, laeuftA P e n → n ≤ kostenA P.dekl e
  | _, _, .konst   => Nat.le_refl 0
  | _, _, .ort i   => Nat.le_refl (1 + i)
  | _, _, .unaer h => by
      have := deckt_A hK h; simp only [kostenA]; omega
  | _, _, .binaer h1 h2 => by
      have := deckt_A hK h1; have := deckt_A hK h2; simp only [kostenA]; omega
  | _, _, .kurz h => by
      have := deckt_A hK h; simp only [kostenA]; omega
  | _, _, @laeuftA.ruf _ _ g _ h => by
      have h1 := deckt_S hK h
      have h2 := hK g
      simp only [kostenA]; omega

theorem deckt_S {P : KProgramm F} (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g) :
    ∀ {s n}, laeuftS P s n → n ≤ kostenS P.dekl s
  | _, _, .prim h  => by have := deckt_A hK h; simp only [kostenS]; omega
  | _, _, .leer    => Nat.le_refl 0
  | _, _, .folge h1 h2 => by
      have := deckt_S hK h1; have := deckt_S hK h2; simp only [kostenS]; omega
  | _, _, .wenn h  => by
      have := deckt_K hK 0 h; simp only [kostenS]; omega
  | _, _, .passt h1 h2 => by
      have := deckt_A hK h1; have := deckt_Z hK h2; simp only [kostenS]; omega
  | _, _, @laeuftS.traverse _ _ b r k _ hkb h => by
      have h1 := deckt_W hK h
      have h2 : k * kostenS P.dekl r ≤ b * kostenS P.dekl r :=
        Nat.mul_le_mul_right _ hkb
      simp only [kostenS]; omega
  | _, _, .retry h => by simp only [kostenS]; omega
  | _, _, .sperrt h => by have := deckt_S hK h; simp only [kostenS]; omega
  | _, _, .sprung  => Nat.le_refl 0

/-- **Die Kettenaussage, mit dem Praefix als Parameter.** Das ist die Form, in der die
    Induktion durchgeht -- und sie ist woertlich die korrigierte Regel aus
    `messung/K001.md` §3. -/
theorem deckt_K {P : KProgramm F} (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g)
    (praefix : Nat) : ∀ {k n}, laeuftK P k n → praefix + n ≤ kostenK P.dekl praefix k
  | _, _, .durch    => by simp only [kostenK]; omega
  | _, _, .sonst h  => by have := deckt_S hK h; simp only [kostenK]; omega
  | _, _, .nimmt h1 h2 => by
      have := deckt_A hK h1; have := deckt_S hK h2
      simp only [kostenK]; refine le_max_links ?_; omega
  | _, _, @laeuftK.weiter _ _ b _ k _ _ h1 h2 => by
      have ha := deckt_A hK h1
      have hk := deckt_K hK (praefix + kostenA P.dekl b) h2
      simp only [kostenK]; refine le_max_rechts ?_; omega

theorem deckt_Z {P : KProgramm F} (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g) :
    ∀ {z n}, laeuftZ P z n → n ≤ kostenZ P.dekl z
  | _, _, .hier h => by
      simp only [kostenZ]; exact le_max_links (deckt_S hK h)
  | _, _, .dort h => by
      simp only [kostenZ]; exact le_max_rechts (deckt_Z hK h)

theorem deckt_W {P : KProgramm F} (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g) :
    ∀ {r k n}, laeuftW P r k n → n ≤ k * kostenS P.dekl r
  | _, _, _, .null => by omega
  | _, _, _, .mehr h1 h2 => wdh_schritt (deckt_S hK h1) (deckt_W hK h2)
end

/-- **L1, in einem Satz.** -/
-- BEWEIST NICHT: dass ein Durchlauf ueberhaupt ENDET. Die Laufrelation beschreibt nur
-- endende Durchlaeufe -- ein `forever` hat gar keine Ableitung, und der Pass sagt fuer
-- ihn `Unbekannt` statt einer Zahl. Terminierung ist `Terminierung.lean`.
-- BEWEIST AUCH NICHT: (K1). `Ĉ(konst) = 0` steht als DEFINITION da; die Aussage, dass
-- der Erzeuger fuer einen konstanten Ausdruck keine Primitive ausgibt, ist eine ueber
-- `emit.rs` und faellt hier nicht.
theorem L1_obere_schranke {P : KProgramm F}
    (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g)
    {s : Anw F} {n : Nat} (h : laeuftS P s n) : n ≤ kostenS P.dekl s :=
  deckt_S hK h


#print axioms Passlogik.Kosten.L1_obere_schranke
/-! ### 4.1 FUND, formal: warum `K001` an jeder rekursiven Funktion fiel

    `messung/K001.md` §4 und `SYNTAX.md`:749: *"`K001` fiel an jeder korrekten rekursiven
    Funktion, und das ist der Grund, warum niemand eine schrieb."*

    Der Grund steht in der Praemisse `hK` selbst: ruft `f` sich, so zaehlt der Rumpf
    `dekl f` fuer den Ruf -- und `kostenS(rumpf f) <= dekl f` erzwingt, dass der GANZE
    UEBRIGE Rumpf null kostet.
-/

/-- Eine Funktion mit genau einer Selbstruf-Anweisung und einer weiteren Primitive. -/
def selbstruf (f : Unit) : Anw Unit :=
  .folge (.prim (.ruf f)) (.prim (.ort 0))

/-- **Die Praemisse ist unerfuellbar, sobald neben dem Selbstruf irgendetwas steht.** -/
theorem rekursion_bricht_die_praemisse (d : Nat) :
    ¬ (kostenS (fun _ : Unit => d) (selbstruf ()) ≤ d) := by
  simp only [selbstruf, kostenS, kostenA]
  omega


#print axioms Passlogik.Kosten.rekursion_bricht_die_praemisse
/-! ## 5. L2 -- der Vergleich bei der KLEINSTEN Belegung

    `messung/K001.md` §2. `E` ist eine Konstante plus Vielfache nichtnegativer Groessen,
    verglichen wird bei `σ = 0`. **Die Nichtnegativitaet ist die Praemisse, und sie ist
    `K005`** -- ohne sie gaebe es keine kleinste Belegung.
-/

/-- Ein Kostenterm `c + Σ a_i * s_i`. Ueber `Int`, damit die Praemisse SICHTBAR ist:
    ueber `Nat` waere sie geschenkt und damit unsichtbar. -/
structure Term where
  fest    : Int
  glieder : List (Int × Nat)      -- (Koeffizient, Symbolkennung)

def gliederwert (σ : Nat → Int) : List (Int × Nat) → Int
  | []           => 0
  | (a, s) :: gs => a * σ s + gliederwert σ gs

def wert (t : Term) (σ : Nat → Int) : Int := t.fest + gliederwert σ t.glieder

/-- Die kleinste zulaessige Belegung. -/
def null_belegung : Nat → Int := fun _ => 0

/-- **`K005` -- alle Koeffizienten sind nichtnegativ.** -/
def koeffizienten_nichtnegativ (t : Term) : Prop := ∀ p ∈ t.glieder, 0 ≤ p.1

/-- Die zweite Haelfte der Praemisse: die SYMBOLE sind nichtnegativ (geprueft). -/
def belegung_nichtnegativ (σ : Nat → Int) : Prop := ∀ s, 0 ≤ σ s

theorem gliederwert_null (gs : List (Int × Nat)) : gliederwert null_belegung gs = 0 := by
  induction gs with
  | nil => rfl
  | cons p rest ih => simp [gliederwert, null_belegung, ih]

theorem gliederwert_nichtnegativ {σ : Nat → Int} {gs : List (Int × Nat)}
    (hk : ∀ p ∈ gs, 0 ≤ p.1) (hs : belegung_nichtnegativ σ) : 0 ≤ gliederwert σ gs := by
  induction gs with
  | nil => simp [gliederwert]
  | cons p rest ih =>
      have h1 : 0 ≤ p.1 := hk p (List.mem_cons_self ..)
      have h2 : 0 ≤ σ p.2 := hs p.2
      have h3 : 0 ≤ p.1 * σ p.2 := Int.mul_nonneg h1 h2
      have h4 : 0 ≤ gliederwert σ rest :=
        ih (fun q hq => hk q (List.mem_cons_of_mem _ hq))
      simp only [gliederwert]
      omega

/-- **L2.** Haelt die Zusage bei der kleinsten Belegung, so haelt sie bei jeder. -/
-- BEWEIST NICHT: dass `K005` fuer ein gegebenes Programm gilt. Das ist eine Pruefung
-- des Passes. Was hier steht, ist, dass sie GEBRAUCHT wird -- siehe der Gegenfall.
theorem L2_kleinste_belegung {t : Term} {σ : Nat → Int} {C : Int}
    (hk : koeffizienten_nichtnegativ t) (hs : belegung_nichtnegativ σ)
    (h : C ≤ wert t null_belegung) : C ≤ wert t σ := by
  unfold wert at h ⊢
  rw [gliederwert_null] at h
  have := gliederwert_nichtnegativ hk hs (gs := t.glieder)
  omega


#print axioms Passlogik.Kosten.L2_kleinste_belegung
/-- **Und ohne `K005` faellt L2.** `costs <= 40 * n` mit einem negativen Koeffizienten
    ist bei `n = 1` kleiner als bei `n = 0`. *Deshalb ist `K005` keine Bequemlichkeit,
    sondern die Voraussetzung, unter der L2 ueberhaupt gilt* (`messung/K001.md` §2). -/
theorem ohne_K005_faellt_L2 :
    ∃ (t : Term) (σ : Nat → Int), belegung_nichtnegativ σ ∧ wert t σ < wert t null_belegung := by
  have hs : belegung_nichtnegativ (fun _ => (1 : Int)) := by
    intro _; show (0 : Int) ≤ 1; decide
  refine ⟨⟨0, [(-1, 0)]⟩, (fun _ => (1 : Int)), hs, ?_⟩
  simp [wert, gliederwert, null_belegung]


#print axioms Passlogik.Kosten.ohne_K005_faellt_L2
/-! ## 6. FUND, machinengeprueft: die alte Zweigkettenregel ZAEHLT ZU WENIG

    `messung/K001.md` §3: bis zum 2026-08-24 rechnete der Pass
    `max over i (Ĉ(bed_i) + Ĉ(rumpf_i))` -- nur die eigene Bedingung je Zweig, fuer
    `sonst` gar keine. **Zwei Ruempfe gleicher Bedeutung massen 2 und 6, und der mit
    der 2 ging mit `costs <= 2 ops` und null Fehlern durch.**

    Hier steht dieselbe Datei als Satz.
-/

/-- Die ALTE, falsche Regel. -/
def kostenKalt (dekl : F → Nat) : Kette F → Nat
  | .ohneSonst   => 0
  | .mitSonst s  => kostenS dekl s
  | .zweig b r k => Nat.max (kostenA dekl b + kostenS dekl r) (kostenKalt dekl k)

/-- Die gemessene Datei: `if a > 5 { return 1; } else if b > 5 … else { return 4; }`.
    Jede Bedingung ist `Ort > Konstante`, also `1 + (1+0) + 0 = 2`; jeder Rumpf ist ein
    `return`, also `0`. -/
def bedingung : Ausdr Unit := .binaer (.ort 0) .konst

def kette_gemessen : Kette Unit :=
  .zweig bedingung .sprung
    (.zweig bedingung .sprung
      (.zweig bedingung .sprung (.mitSonst .sprung)))

def leeres_programm : KProgramm Unit := ⟨fun _ => .leer, fun _ => 0⟩

/-- Die alte Regel rechnet **2**. -/
theorem alt_rechnet_zwei : kostenKalt leeres_programm.dekl kette_gemessen = 2 := by
  simp [kette_gemessen, bedingung, kostenKalt, kostenS, kostenA, leeres_programm]

/-- Die korrigierte Regel rechnet **6**. -/
theorem neu_rechnet_sechs : kostenK leeres_programm.dekl 0 kette_gemessen = 6 := by
  simp [kette_gemessen, bedingung, kostenK, kostenS, kostenA, leeres_programm]

/-- **Und es GIBT einen Durchlauf, der 6 kostet** -- der, der bis zum `sonst` laeuft. -/
theorem durchlauf_kostet_sechs : laeuftK leeres_programm kette_gemessen 6 := by
  have hb : laeuftA leeres_programm bedingung 2 := by
    simp only [bedingung]
    have := laeuftA.binaer (P := leeres_programm) (laeuftA.ort (P := leeres_programm) 0)
              (laeuftA.konst (P := leeres_programm))
    simpa using this
  have h3 : laeuftK leeres_programm (.zweig bedingung .sprung (.mitSonst .sprung)) 2 := by
    have := laeuftK.weiter (P := leeres_programm) (r := .sprung) hb
              (laeuftK.sonst (P := leeres_programm) laeuftS.sprung)
    simpa using this
  have h2 : laeuftK leeres_programm
      (.zweig bedingung .sprung (.zweig bedingung .sprung (.mitSonst .sprung))) 4 := by
    have := laeuftK.weiter (P := leeres_programm) (r := .sprung) hb h3
    simpa using this
  simp only [kette_gemessen]
  have := laeuftK.weiter (P := leeres_programm) (r := .sprung) hb h2
  simpa using this

/-- **Der Satz: die alte Regel war nicht sound.** Es gibt einen Durchlauf, der mehr
    kostet als die alte Regel rechnet -- und eine Unterzaehlung ist die einzige
    Fehlerrichtung, die zaehlt, weil `K001` eine OBERE Schranke sein soll. -/
-- BEWEIST NICHT: dass der Rust genau diese Regel trug. Diese Datei liest keinen Rust.
-- Modelliert ist die Regel, wie `messung/K001.md` §3 sie AUFSCHREIBT -- und die
-- gerechneten Zahlen 2 und 6 sind dieselben, die dort gemessen stehen.
theorem alte_regel_zaehlt_zu_wenig :
    ∃ (k : Kette Unit) (n : Nat),
      laeuftK leeres_programm k n ∧ kostenKalt leeres_programm.dekl k < n := by
  refine ⟨kette_gemessen, 6, durchlauf_kostet_sechs, ?_⟩
  rw [alt_rechnet_zwei]; omega


#print axioms Passlogik.Kosten.alte_regel_zaehlt_zu_wenig
/-! ## 7. `held` -- die Haltezeit komponiert

    `SPRACHE.md`:1176, §9.3:
    1. "Every lock declares `held <= K ops`. A `locks` block whose body costs exceed K is
       a compile error." -- das ist `K002`.
    4. "Die Latenzaussage je Wartestelle ist damit ableitbar (hoeherrangige Halter halten
       <= die Summe ihrer `held`)."
-/

/-- **`K002`.** Der Rumpf eines `locks`-Blocks kostet hoechstens die deklarierte
    Haltezeit -- und zwar an JEDEM `locks`-Block im Baum. -/
def k002_haelt (dekl : F → Nat) : Anw F → Prop
  | .prim _       => True
  | .leer         => True
  | .folge a b    => k002_haelt dekl a ∧ k002_haelt dekl b
  | .wenn k       => k002_kette dekl k
  | .passt _ z    => k002_zweige dekl z
  | .traverse _ r => k002_haelt dekl r
  | .retry _ r    => k002_haelt dekl r
  | .sperrt L r   => kostenS dekl r ≤ L.held ∧ k002_haelt dekl r
  | .sprung       => True
where
  k002_kette (dekl : F → Nat) : Kette F → Prop
    | .ohneSonst   => True
    | .mitSonst s  => k002_haelt dekl s
    | .zweig _ r k => k002_haelt dekl r ∧ k002_kette dekl k
  k002_zweige (dekl : F → Nat) : Zweige F → Prop
    | .keine    => True
    | .dazu s z => k002_haelt dekl s ∧ k002_zweige dekl z

/-- **Die Komposition: `held` bindet ALLES darunter.** Ein Durchlauf unter der Sperre
    kostet hoechstens ihre deklarierte Haltezeit -- einschliesslich der geschachtelten
    `locks`-Bloecke, der Schleifen und der Rufe, weil `Ĉ` sie alle mitzaehlt. -/
-- BEWEIST NICHT: dass die Sperre in dieser Zeit auch wirklich gehalten wird. Das ist
-- eine Aussage ueber die Absenkung. Und BEWEIST NICHT: irgendetwas ueber einen
-- SYMBOLISCHEN `held` -- `K010` verlangt `constexpr`, und `SPRACHE.md`:1282 sagt warum:
-- "Latenz lebt bei der GROESSTEN Belegung, und ein Symbol hat keine."
theorem held_bindet_darunter {P : KProgramm F}
    (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g)
    {L : Sperre} {r : Anw F} {n : Nat}
    (hk002 : kostenS P.dekl r ≤ L.held)
    (h : laeuftS P (.sperrt L r) n) : n ≤ L.held := by
  cases h with
  | sperrt hr => exact Nat.le_trans (deckt_S hK hr) hk002


#print axioms Passlogik.Kosten.held_bindet_darunter
/-- Die Summe der Haltezeiten einer gehaltenen Kette. -/
def summe_held : List Sperre → Nat
  | []      => 0
  | L :: Ls => L.held + summe_held Ls

/-- **Punkt 4 aus §9.3, als Satz.** Halten `n` Sperren gleichzeitig, so ist die Zeit,
    die ein Warter hoechstens wartet, die Summe ihrer `held`. -/
-- BEWEIST NICHT: dass die Kette der Halter ENDLICH ist -- das liefert die Rangordnung
-- (`Rang.lean`), und ohne sie waere die Summe gar nicht gebildet. **Die beiden Saetze
-- haengen zusammen, und diese Zeile ist die Naht.**
-- BEWEIST AUCH NICHT: Fairness. "Kein Verklemmen" heisst nicht "jeder kommt dran"
-- (`messung/H006.md` §5d).
theorem wartezeit_ist_summe (Ls : List Sperre) (kosten : Sperre → Nat)
    (h : ∀ L ∈ Ls, kosten L ≤ L.held) :
    (Ls.map kosten).sum ≤ summe_held Ls := by
  induction Ls with
  | nil => simp [summe_held]
  | cons L rest ih =>
      have h1 : kosten L ≤ L.held := h L (List.mem_cons_self ..)
      have h2 := ih (fun M hm => h M (List.mem_cons_of_mem _ hm))
      simp only [List.map_cons, List.sum_cons, summe_held]
      omega


#print axioms Passlogik.Kosten.wartezeit_ist_summe
/-! ## 8. Die Schleifenschranke multipliziert

    `SPRACHE.md`:940: "a traversal counts body costs x domain bound". Der Satz steckt
    schon in `deckt_S`; hier steht er allein, weil er die Stelle ist, an der der
    `mappings of`-Fehler lebte.
-/

/-- **Der Schleifensatz.** Ein Durchlauf, der den Rumpf hoechstens `b`-mal betritt,
    kostet hoechstens `b * Ĉ(rumpf)`. -/
-- BEWEIST NICHT: **dass `b` die Maechtigkeit der Domaene IST** (K4). Genau in dieser
-- Luecke lebte der Fehler `Ebenen x Knotenlaenge = 2 048` statt
-- `Knotenlaenge ^ Ebenen = 512^4 = 68 719 476 736` -- sieben Groessenordnungen, drei
-- Tage getragen, gefunden vom ERZEUGER und nicht von einem Test
-- (`messung/K001.md` §6). *`kosten.domaenenschranke` steht deshalb auf `CONJECTURED`,
-- und dieser Satz macht die Naht sichtbar statt sie zu schliessen.*
theorem schleife_multipliziert {P : KProgramm F}
    (hK : ∀ g, kostenS P.dekl (P.rumpf g) ≤ P.dekl g)
    {b : Nat} {r : Anw F} {n : Nat}
    (h : laeuftS P (.traverse b r) n) : n ≤ b * kostenS P.dekl r := by
  have := deckt_S hK h
  simpa only [kostenS] using this


#print axioms Passlogik.Kosten.schleife_multipliziert
/-- **Und die Ueberlaufvoraussetzung**, die `messung/K001.md` §3 als "Voraussetzung von
    L1, keine Feinheit" nennt: bis 2026-08-19 ergaben vier geschachtelte `traverse` ueber
    `count 4294967295` ein NEGATIVES Produkt. Ueber `Nat` kann das nicht geschehen --
    **und das ist eine Modellentscheidung, keine Aussage ueber den Pruefer.** Der Pruefer
    rechnet in Maschinenzahlen und muss `checked_mul` benutzen; hier steht nur, was dann
    gilt. -/
theorem produkt_waechst_monoton (a b c : Nat) (h : a ≤ b) : a * c ≤ b * c :=
  Nat.mul_le_mul_right _ h

end Passlogik.Kosten
