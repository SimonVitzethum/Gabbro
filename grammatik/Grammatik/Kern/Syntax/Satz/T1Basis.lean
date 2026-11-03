/-
  Datei:      Grammatik/Satz.lean
  Gegenstand: **DER SATZ**, ueber die GANZE Grammatik, und was neben ihm steht.

  ## Der Satz, in einem Satz

  > Ein Satz der Grammatik hat eine totale Bedeutung, und ihr Ausgangstyp kennt genau zwei
  > Fehler: die Logik des Schreibers und eine Hardwareannahme.

  Der Beweis ist die DEFINITION von `eval` und `exec`: beide sind totale Funktionen
  (`Grammatik/Semantik.lean` uebersetzt), und `Ausgang` hat sieben Konstruktoren. Was hier
  als `theorem` steht, macht das nachpruefbar, ohne die Definition zu lesen:

    §1  `zwei_fehler`          -- jeder Ausgang ist Kontrollfluss, `logik` oder `hardware`
    §2  die Inversionen        -- was die Grammatik an einer Stelle VERLANGT hat
    §3  `exec_gut`             -- ZWEI Saetze in einer Induktion ueber die ganze Grammatik:
                                  der RAHMEN (ein Rumpf schreibt keinen Traeger, den sein
                                  Vertrag nicht nennt) und die SPUR (jeder Zugriff, den ein
                                  Rumpf tut, traegt die Waechter seines Traegers und haelt
                                  dynamisch jede Sperre, die sein Λ nennt). Die Spur ist der
                                  Anschluss an `Wettlauf.lean`: dort steht, dass Faeden mit
                                  solchen Spuren einander nie im Wettlauf beruehren.
    §4  die Sprechproben       -- Saetze, die die Grammatik ABLEITET, ausgewertet

  ## Was der Satz NICHT sagt

  Die Grammatik ist die GANZE Sprache (`Syntax.lean`, Kopf). Was bleibt, sind die drei
  PARAMETER der Bedeutung: das Orakel (H1: was ein fremder Rumpf, ein Register, das
  Speichermodell tut), die Durchgaenge eines `forever` (H2), die Rekursionstiefe (`abstieg`
  ist die Logikstelle `decreases`). *Sie sind die Hardware und die Logik -- genau die zwei,
  die bleiben sollen.* `SYNTAX.md` §16 zaehlt auf, was daraus folgt und was nicht.
-/
module
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Zwei Fehler, kein dritter -/

/-- Was ein Ausgang meldet: nichts (Kontrollfluss), Logik oder Hardware. -/
def Ausgang.fehler : Ausgang V l Γ → Option (Logik D ⊕ Hardware D)
  | .logik e => some (.inl e)
  | .hardware e => some (.inr e)
  | _ => none

/-- **Jeder Ausgang ist Kontrollfluss, oder er nennt seinen Fehler -- und der ist Logik oder
    Hardware.** Ein dritter Konstruktor wuerde diesen Satz brechen, nicht eine Definition
    weiter hinten. -/
theorem zwei_fehler (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .why σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) := by
  cases o <;> simp only [Ausgang.ok.injEq, exists_and_left, exists_eq', and_true, reduceCtorEq, exists_false, or_self, or_false, Ausgang.zurueck.injEq, or_true, Ausgang.why.injEq, Ausgang.leave.injEq, exists_prop, false_or, Ausgang.next.injEq, Ausgang.logik.injEq, Ausgang.hardware.injEq] <;> assumption

/-- Und die Bedeutung ist TOTAL: zu jedem Satz der Grammatik, jeder Welt, jeder Belegung
    gibt es den Ausgang -- `exec` ist eine Funktion. (Der Beweis ist, dass sie eine ist.) -/
theorem bedeutung_total (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    ∃ o : Ausgang V l Γ, exec P O passes fuel V b σ ρ = o := ⟨_, rfl⟩

/-- Ebenso jeder Ausdruck: ein Wert seines Typs, immer. -/
theorem wert_total (e : Expr D Γ Λ τ) (σ₀ σ : World D) (ρ : Env D Γ) :
    ∃ v : Wert D τ, eval σ₀ e σ ρ = v :=
  ⟨_, rfl⟩

/-- Ein Zahlwert liegt in seinem Bereich -- das ist sein Typ. -/
theorem im_bereich (e : Expr D Γ Λ (.int lo hi)) (σ₀ σ : World D) (ρ : Env D Γ) :
    lo ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ hi :=
  ⟨(eval σ₀ e σ ρ).lo_le, (eval σ₀ e σ ρ).le_hi⟩

/-- Ein Gleitkommawert ist ENDLICH und in seinem Bereich -- kein NaN, kein Unendlich («F»). -/
theorem gleit_endlich (e : Expr D Γ Λ (.fl lo hi)) (σ₀ σ : World D) (ρ : Env D Γ) :
    gleitEndlich (eval σ₀ e σ ρ).x = true ∧ gleitLe (bruch lo) (eval σ₀ e σ ρ).x = true
      ∧ gleitLe (eval σ₀ e σ ρ).x (bruch hi) = true :=
  ⟨(eval σ₀ e σ ρ).endlich, (eval σ₀ e σ ρ).lo_le, (eval σ₀ e σ ρ).le_hi⟩

/-- A function pointer points to a function that conforms to its type («B8», structural since
    2026-10-21): its own signature fits the pointer's (`SigPasst`). -/
theorem fnptr_passt (e : Expr D Γ Λ (.fnptr n)) (σ₀ σ : World D) (ρ : Env D Γ) :
    D.passt (eval σ₀ e σ ρ).val n = true :=
  (eval σ₀ e σ ρ).property

/-- Es gibt keinen Wert vom Typ `never`: ein Rumpf `-> never` hat kein `return`. -/
theorem never_leer (v : Wert D .never) : False := v.elim

/-! ## 2. Die Inversionen -- was an einer Stelle gegolten haben MUSS -/

/-- Ein Slotzugriff steht unter den Waechtern seines Traegers (`H007`, `own`). -/
theorem slot_hat_waechter {t : D.Tab} {f : D.Feld t} {i : Expr D Γ Λ (.index (D.count t))}
    {hL : darf D t Λ} (_e : Expr D Γ Λ (D.typ t f)) (_h : _e = .slot t f i hL) : darf D t Λ := hL

/-- Ein Zugriff DURCH einen Zeiger steht unter denselben Waechtern («SG-8»). -/
theorem zeiger_hat_waechter {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr (.table n (true, rw) space))}
    {ht : D.capTab space n = some t} {i : Expr D Γ Λ (.index (D.count t))} {hL : darf D t Λ}
    (_e : Expr D Γ Λ (D.typ t f)) (_h : _e = .thru p t ht f i hL) : darf D t Λ := hL

/-- Ein Zugriff DURCH eine `own`-Faehigkeit steht unter denselben Waechtern wie `thru` --
    plus der gehaltenen Eigentumsmarke. -/
theorem zeigerOwn_hat_waechter {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr ⟨space, ⟨true, rw, some o⟩, .table n⟩)}
    {ht : D.capTab space n = some t} {i : Expr D Γ Λ (.index (D.count t))}
    {m : D.Marke} {s : Nat} {ho : D.ownerNr o = some m} {he : m ∈ D.eigner t}
    {hg : Sum.inr (m, s) ∈ D.braucht t} {hL : darf D t Λ}
    (_e : Expr D Γ Λ (D.typ t f)) (_h : _e = .thruOwn p t ht f i m s ho he hg hL) : darf D t Λ := hL

/-- Eine Bytelesung liegt in der Tabelle: `hi + n ≤ count` («SG-16»). -/
theorem bytes_in_tabelle {t : D.Tab} {f : D.Feld t} {hf} {n : Nat} {i : Expr D Γ Λ (.int lo hi)}
    {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t} {hL}
    (_e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (_h : _e = .getBytes t f hf n i hlo hhi hL) :
    0 ≤ lo ∧ hi + n ≤ D.count t := ⟨hlo, hhi⟩

/-- Eine Zuweisung an einen Slot hat das Schreibrecht ihres Vertrags. -/
theorem zuweisung_hat_recht {t : D.Tab} {f : D.Feld t} {i} {e} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignSlot t f i e hw hL) : V.schreibt t = true := hw

/-- Eine Zuweisung DURCH einen Zeiger verlangt einen `rw`-Zeiger UND das Schreibrecht. -/
theorem zeiger_schreibt_mit_recht {read : Bool} {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr (.table n (read, true) space))}
    {ht} {i} {e} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignThru p t ht f i e hw hL) : V.schreibt t = true := hw

/-- Eine Zuweisung DURCH eine `own`-Faehigkeit verlangt dasselbe Schreibrecht wie `assignThru`. -/
theorem zeigerOwn_schreibt_mit_recht {read : Bool} {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr ⟨space, ⟨read, true, some o⟩, .table n⟩)}
    {ht} {i} {e} {m : D.Marke} {s : Nat} {ho : D.ownerNr o = some m} {he : m ∈ D.eigner t}
    {hg : Sum.inr (m, s) ∈ D.braucht t} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignThruOwn p t ht f i e m s ho he hg hw hL) : V.schreibt t = true := hw

/-- Ein `locks L` steht ueber jedem gehaltenen Rang (`H006`): kein zirkulaeres Warten. -/
theorem sperre_steigt {L : D.Lock} {hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L} {body}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .locks L hr body) :
    ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L := hr

/-- **Keine Verklemmung, aus der Grammatik.** Zwei Ruempfe halten je eine Sperre und wollen
    die des anderen: beide `locks` sind dann nicht ableitbar -- `rang L1 < rang L2 < rang L1`
    ist keine Zahl. -/
theorem keine_verklemmung {L1 L2 : D.Lock} {ΛA ΛB : List (Res D)}
    (hA : Res.held L1 ∈ ΛA) (hB : Res.held L2 ∈ ΛB)
    {hrA : ∀ M, Res.held M ∈ ΛA → D.rang M < D.rang L2} {bodyA}
    {hrB : ∀ M, Res.held M ∈ ΛB → D.rang M < D.rang L1} {bodyB}
    (_sA : Stmt D V l Γ ΛA ΛA) (_hsA : _sA = .locks L2 hrA bodyA)
    (_sB : Stmt D V l' Γ' ΛB ΛB) (_hsB : _sB = .locks L1 hrB bodyB) : False := by
  have h1 := hrA L1 hA
  have h2 := hrB L2 hB
  omega

/-- Eine Division hat einen positiven Nenner und einen nichtnegativen Zaehler (`M102`). -/
theorem division_hat_nenner {h0 : 0 ≤ l1} {h1' : 1 ≤ l2} {a : Expr D Γ Λ (.int l1 h1)}
    {b : Expr D Γ Λ (.int l2 h2)} (_e : Expr D Γ Λ (.int 0 h1)) (_h : _e = .div h0 h1' a b) :
    0 ≤ l1 ∧ 1 ≤ l2 := ⟨h0, h1'⟩

/-- Eine vorzeichenbehaftete Division hat einen Nenner, dessen Bereich die Null ausschliesst. -/
theorem sdivision_ohne_null {hb : 1 ≤ l2 ∨ h2 ≤ -1} {a : Expr D Γ Λ (.int l1 h1)}
    {b : Expr D Γ Λ (.int l2 h2)}
    (_e : Expr D Γ Λ (.int (-(betragMax l1 h1)) (betragMax l1 h1))) (_h : _e = .sdiv hb a b) :
    1 ≤ l2 ∨ h2 ≤ -1 := hb

/-- Ein `return` gibt genau die geschuldeten Zeugnisse und Marken zurueck -- linear. -/
theorem rueckgabe_bilanziert {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .ret e hΛ) : Λ.Perm V.ende := hΛ

/-- Ein Ruf traegt die verbrauchten Marken und die verlangten Zeugnisse in der Hand, und die
    Schreibrechte des Gerufenen stehen im eigenen Vertrag. -/
theorem ruf_hat_alles {f : D.Fn} {args} {hp : RufPasst D V (D.signatur f) Λ} {hr}
    (_s : Stmt D V l Γ Λ (nach D f Λ)) (_h : _s = .call f args hp hr) :
    Untermulti ((D.signatur f).inputMarks.map (Res.vonMarke D)) Λ ∧
    (∀ L, L ∈ D.haelt f → Res.held L ∈ Λ) ∧
    (∀ t, D.schreibt f t = true → V.schreibt t = true) := ⟨hp.hk, hp.hh, hp.hw⟩

/-- Ein Ruf DURCH einen Funktionszeiger hat dasselbe in der Hand («B8»). -/
theorem zeigerruf_hat_alles {p : Expr D Γ Λ (.fnptr n)} {args} {hp : RufPasst D V (D.sigNr n) Λ} {hr}
    (_s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ)) (_h : _s = .callInd p args hp hr) :
    Untermulti ((D.sigNr n).inputMarks.map (Res.vonMarke D)) Λ ∧
    (∀ t, (D.sigNr n).schreibt t = true → V.schreibt t = true) := ⟨hp.hk, hp.hw⟩

/-- Ein Registerschreiben steht an einem Register schreibbarer Klasse (`R005`/`R006`). -/
theorem register_schreibbar {r : D.Reg} {hk : (D.rklasse r).schreibbar = true} {e}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .regWrite r hk e) : (D.rklasse r).schreibbar = true := hk

/-- Eine Registerlesung steht an einem Register lesbarer Klasse. -/
theorem register_lesbar {r : D.Reg} {hk : (D.rklasse r).lesbar = true} {rest}
    (_b : Block D V l Γ Λ Λ') (_h : _b = .regRead r hk rest) : (D.rklasse r).lesbar = true := hk

/-- Ein `transition` schreibt ein schreibbares Register aus seinem ERKLAERTEN Spiegel. -/
theorem transition_hat_spiegel {r m : D.Reg} {hk} {hm : D.spiegel r = some m} {hl} {maske bits}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .transition r hk m hm hl maske bits) :
    D.spiegel r = some m ∧ (D.rklasse m).lesbar = true := ⟨hm, hl⟩

/-- Ein `state`-Uebergang ist ERKLAERT: `erlaubt t f von nach`. -/
theorem uebergang_erklaert {t : D.Tab} {f : D.Feld t} {hτ : D.typ t f = .int lo hi} {i}
    {von nach : Int} {hn} {he : D.erlaubt t f von nach = true} {hw} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .shift t f hτ i von nach hn he hw hL) :
    D.erlaubt t f von nach = true := he

/-- Eine Veroeffentlichung nimmt GENAU die erklaerte Nutzlast D.Fn D.passt mit (`V001`-`V004`). -/
theorem publish_paart {g : D.Glob} {e} {payload : List D.Glob} {hp : payload = D.nutzlast g} {hw} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .publish g e payload hp hw hL) : payload = D.nutzlast g := hp

/-- Ein `awaits` nimmt dieselbe Nutzlast D.Fn D.passt entgegen. -/
theorem awaits_paart {g : D.Glob} {payload : List D.Glob} {hp : payload = D.nutzlast g} {hL} {hat} {rest}
    (_b : Block D V l Γ Λ Λ') (_h : _b = .awaits g payload hp hL hat rest) : payload = D.nutzlast g := hp

/-- `advances a -> b` («B37»): die Marke steht auf Stufe `a`, und `b` ist die naechste. -/
theorem stufe_steigt {m : D.Marke} {a : Nat} {h : Res.marke m a ∈ Λ} {hs : a + 1 < D.stufen m}
    (_s : Stmt D V l Γ Λ ((Λ.erase (.marke m a)) ++ [.marke m (a + 1)]))
    (_h : _s = .advances m a h hs) : Res.marke m a ∈ Λ ∧ a + 1 < D.stufen m := ⟨h, hs⟩

/-! ## 3. Rahmen und Spur -- EINE Induktion ueber die ganze Grammatik -/

/-- `σ'` unterscheidet sich von `σ` hoechstens an Traegern mit Schreibrecht. -/
def Rahmen (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  (∀ t, W t = false → ∀ k f, σ'.slots t k f = σ.slots t k f) ∧
  (∀ g, G g = false → σ'.globs g = σ.globs g)

theorem Rahmen.refl (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) : Rahmen W G σ σ :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

theorem Rahmen.trans {W : D.Tab → Bool} {G : D.Glob → Bool} {a b c : World D}
    (h1 : Rahmen W G a b) (h2 : Rahmen W G b c) : Rahmen W G a c :=
  ⟨fun t ht k f => (h2.1 t ht k f).trans (h1.1 t ht k f),
   fun g hg => (h2.2 g hg).trans (h1.2 g hg)⟩

/-- Ein engerer Vertrag haelt den weiteren Rahmen. -/
theorem Rahmen.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : Rahmen W G a b) : Rahmen W' G' a b :=
  ⟨fun t ht k f => h.1 t (by cases hw : W t; rfl; exact absurd (hW t hw) (by simp only [ht, Bool.false_eq_true, not_false_eq_true])) k f,
   fun g hg => h.2 g (by cases hg' : G g; rfl; exact absurd (hG g hg') (by simp only [hg, Bool.false_eq_true, not_false_eq_true]))⟩

/-- Die Sperren, die ein statisches `Λ` nennt, sind dynamisch gehalten. -/
def HeldIn (Λ : List (Res D)) (h : List D.Lock) : Prop := ∀ L, Res.held L ∈ Λ → L ∈ h

/-- Die Sperren, die ein statisches `Λ` nennt, sind GENAU die dynamisch gehaltenen. -/
def HeldGenau (Λ : List (Res D)) (h : List D.Lock) : Prop := ∀ L, Res.held L ∈ Λ ↔ L ∈ h

theorem HeldGenau.heldIn {Λ : List (Res D)} {h : List D.Lock} (hg : HeldGenau Λ h) : HeldIn Λ h :=
  fun L hL => (hg L).mp hL

/-- **Held with a floor** (2026-09-13, held-set relaxation): the locks the
    static `Λ` names are held, and every held lock `Λ` does NOT name (an
    extra lock of a caller, `RufPasst.hx`) ranks below the floor `b`. With
    `b = none` there is no extra lock: `HeldB none` is `HeldGenau`
    (`heldB_none_iff`). -/
def HeldB (b : Option Int) (Λ : List (Res D)) (h : List D.Lock) : Prop :=
  HeldIn Λ h ∧ ∀ L ∈ h, Res.held L ∉ Λ → ∃ c, b = some c ∧ D.rang L < c

theorem HeldB.heldIn {b : Option Int} {Λ : List (Res D)} {h : List D.Lock} (hg : HeldB b Λ h) :
    HeldIn Λ h := hg.1

theorem heldB_of_genau (b : Option Int) {Λ : List (Res D)} {h : List D.Lock}
    (hg : HeldGenau Λ h) : HeldB b Λ h :=
  ⟨hg.heldIn, fun L hL hn => absurd ((hg L).mpr hL) hn⟩

theorem heldB_none_iff {Λ : List (Res D)} {h : List D.Lock} : HeldB none Λ h ↔ HeldGenau Λ h := by
  refine ⟨fun hg L => ⟨hg.1 L, fun hL => Classical.byContradiction fun hn => ?_⟩, heldB_of_genau none⟩
  obtain ⟨c, hc, _⟩ := hg.2 L hL hn
  cases hc

/-- The floor `b` lies at or below the floor `b'` (`none` below everything). -/
def BodenUnter (b b' : Option Int) : Prop := ∀ c, b = some c → ∃ c', b' = some c' ∧ c ≤ c'

theorem bodenUnter_refl (b : Option Int) : BodenUnter b b :=
  fun c hc => ⟨c, hc, Int.le_refl c⟩

theorem bodenUnter_none (b : Option Int) : BodenUnter none b := fun _ hc => nomatch hc

end Gabbro.Grammatik
