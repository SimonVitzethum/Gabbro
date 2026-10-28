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
import Grammatik.Kern.Semantik.Semantik

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
theorem zeiger_hat_waechter {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr n rw)}
    {ht : D.tabNr n = some t} {i : Expr D Γ Λ (.index (D.count t))} {hL : darf D t Λ}
    (_e : Expr D Γ Λ (D.typ t f)) (_h : _e = .thru p t ht f i hL) : darf D t Λ := hL

/-- Eine Bytelesung liegt in der Tabelle: `hi + n ≤ count` («SG-16»). -/
theorem bytes_in_tabelle {t : D.Tab} {f : D.Feld t} {hf} {n : Nat} {i : Expr D Γ Λ (.int lo hi)}
    {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t} {hL}
    (_e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (_h : _e = .getBytes t f hf n i hlo hhi hL) :
    0 ≤ lo ∧ hi + n ≤ D.count t := ⟨hlo, hhi⟩

/-- Eine Zuweisung an einen Slot hat das Schreibrecht ihres Vertrags. -/
theorem zuweisung_hat_recht {t : D.Tab} {f : D.Feld t} {i} {e} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignSlot t f i e hw hL) : V.schreibt t = true := hw

/-- Eine Zuweisung DURCH einen Zeiger verlangt einen `rw`-Zeiger UND das Schreibrecht. -/
theorem zeiger_schreibt_mit_recht {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr n true)}
    {ht} {i} {e} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignThru p t ht f i e hw hL) : V.schreibt t = true := hw

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
    Untermulti ((D.konsumiert f).map (Res.vonMarke D)) Λ ∧
    (∀ L, L ∈ D.haelt f → Res.held L ∈ Λ) ∧
    (∀ t, D.schreibt f t = true → V.schreibt t = true) := ⟨hp.hk, hp.hh, hp.hw⟩

/-- Ein Ruf DURCH einen Funktionszeiger hat dasselbe in der Hand («B8»). -/
theorem zeigerruf_hat_alles {p : Expr D Γ Λ (.fnptr n)} {args} {hp : RufPasst D V (D.sigNr n) Λ} {hr}
    (_s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ)) (_h : _s = .callInd p args hp hr) :
    Untermulti ((D.sigNr n).konsumiert.map (Res.vonMarke D)) Λ ∧
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

/-- Eine Veroeffentlichung nimmt GENAU die erklaerte Nutzlast mit (`V001`-`V004`). -/
theorem publish_paart {g : D.Glob} {e} {payload : List D.Glob} {hp : payload = D.nutzlast g} {hw} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .publish g e payload hp hw hL) : payload = D.nutzlast g := hp

/-- Ein `awaits` nimmt dieselbe Nutzlast entgegen. -/
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

/-- Supplies `HeldIn` from a `HeldIn`, `HeldGenau` or `HeldB` in context (the
    side condition of machine G since the held-set relaxation). -/
macro "held_tac" : tactic => `(tactic| first
  | assumption
  | exact HeldGenau.heldIn (by assumption)
  | exact HeldB.heldIn (by assumption))

def OrtDarf (Λ : List (Res D)) : D.Tab ⊕ D.Glob → Prop
  | .inl t => darf D t Λ
  | .inr g => gdarf D g Λ

/-- Ein GUTES Ereignis: der Zugriff traegt die Waechter seines Traegers, und jede Sperre, die
    sein `Λ` nennt, ist gehalten. -/
def Ereignis.gut : Ereignis D → Prop
  | .zugriff t _ Λ h => darf D t Λ ∧ HeldIn Λ h
  | .gzugriff g _ Λ h => gdarf D g Λ ∧ HeldIn Λ h
  -- Nehmen einer Sperre: ueber allem Gehaltenen im Rang (H006), also nicht schon gehalten.
  | .nimmt L h => (∀ M ∈ h, D.rang M < D.rang L) ∧ L ∉ h
  | .gibt _ => True
  -- An answer from outside: no cell, no lock.
  | .fremd _ => True

/-- Ein Ereignis PASST zu seiner Nachwelt (dem Rest der Spur hinter ihm): die Sperren, die es
    als gehalten aufzeichnet, sind genau die dort offenen. -/
def Ereignis.passt : Ereignis D → List (Ereignis D) → Prop
  | .zugriff _ _ _ h, s => h = offen s
  | .gzugriff _ _ _ h, s => h = offen s
  | .nimmt _ h, s => h = offen s
  | .gibt _, _ => True
  | .fremd _, _ => True

/-- Eine Spur ist KONSISTENT, wenn jedes Ereignis zu seinem Rest passt. -/
def Konsistent (s : List (Ereignis D)) : Prop :=
  ∀ (n : Nat) (e : Ereignis D), s[n]? = some e → e.passt (s.drop (n + 1))

theorem konsistent_nil : Konsistent ([] : List (Ereignis D)) := by
  unfold Konsistent; intro n e h; simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at h

theorem konsistent_cons {e : Ereignis D} {s : List (Ereignis D)} (he : e.passt s) (hs : Konsistent s) :
    Konsistent (e :: s) := by
  unfold Konsistent; intro n e' h
  cases n with
  | zero => simp only [List.length_cons, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at h; subst h; exact he
  | succ n => simp only [List.getElem?_cons_succ] at h; exact hs n e' h

/-- Von `σ` nach `σ'`: die offenen Sperren sind dieselben (jedes `locks` ist geschlossen), jedes
    neue Ereignis ist gut, und eine konsistente Spur bleibt konsistent. -/
def Brav (σ σ' : World D) : Prop :=
  σ'.haelt = σ.haelt ∧ (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧ (Konsistent σ.spur → Konsistent σ'.spur)

theorem Brav.refl (σ : World D) : Brav σ σ := ⟨rfl, fun e he => .inl he, id⟩

theorem Brav.trans {a b c : World D} (h1 : Brav a b) (h2 : Brav b c) : Brav a c :=
  ⟨h2.1.trans h1.1, fun e he => match h2.2.1 e he with
    | .inl hb => h1.2.1 e hb
    | .inr g => .inr g, fun k => h2.2.2 (h1.2.2 k)⟩

/-- Aus leerer Spur ist jede zurueckbleibende Spur konsistent: `[]` ist es
    (`konsistent_nil`), und `Brav` traegt Konsistenz vorwaerts. -/
theorem Brav.konsistent_von_leer {a b : World D} (h : Brav a b) (hempty : a.spur = []) :
    Konsistent b.spur := by
  have hk : Konsistent a.spur := by rw [hempty]; exact konsistent_nil
  exact h.2.2 hk

/-- Aus leerer Spur ist jedes zurueckbleibende Ereignis gut: es steht nicht in
    `[]`, also bleibt nur die zweite Haelfte von `Brav`. -/
theorem Brav.gut_von_leer {a b : World D} (h : Brav a b) (hempty : a.spur = [])
    {e : Ereignis D} (he : e ∈ b.spur) : e.gut := by
  rcases h.2.1 e he with hmem | hg
  · rw [hempty] at hmem; simp only [List.not_mem_nil] at hmem
  · exact hg

/-- Konsistenz ueberlebt das Vergessen der aeltesten Ereignisse: der Kopf einer
    konsistenten Spur passt zu seinem Rest, also ist der Rest konsistent. -/
theorem Konsistent.drop1 {e : Ereignis D} {s : List (Ereignis D)} (h : Konsistent (e :: s)) :
    Konsistent s := by
  unfold Konsistent at h ⊢
  intro m e' hm
  have h' := h (m + 1) e' (by simpa using hm)
  simpa using h'

/-- ... und damit jede Endstrecke. -/
theorem Konsistent.drop (s : List (Ereignis D)) (h : Konsistent s) (k : Nat) :
    Konsistent (s.drop k) := by
  induction k generalizing s with
  | zero => simpa using h
  | succ k ih =>
    cases s with
    | nil => exact konsistent_nil
    | cons e s => simpa using ih _ (h.drop1)

/-- Rahmen UND Spur. -/
def Gut (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ Brav σ σ'

theorem Gut.refl (W G) (σ : World D) : Gut W G σ σ := ⟨Rahmen.refl _ _ _, Brav.refl _⟩
theorem Gut.trans {W G} {a b c : World D} (h1 : Gut W G a b) (h2 : Gut W G b c) : Gut W G a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
theorem Gut.weiter {W W' : D.Tab → Bool} {G G' : D.Glob → Bool} {a b : World D}
    (hW : ∀ t, W t = true → W' t = true) (hG : ∀ g, G g = true → G' g = true)
    (h : Gut W G a b) : Gut W' G' a b := ⟨h.1.weiter hW hG, h.2⟩
theorem Gut.haelt {W G} {a b : World D} (h : Gut W G a b) : b.haelt = a.haelt := h.2.1
theorem Gut.heldIn {W G} {a b : World D} (h : Gut W G a b) (hh : HeldIn Λ a.haelt) : HeldIn Λ b.haelt := by
  rw [h.haelt]; exact hh
theorem Gut.heldGenau {W G} {a b : World D} (h : Gut W G a b) (hh : HeldGenau Λ a.haelt) :
    HeldGenau Λ b.haelt := by
  rw [h.haelt]; exact hh
theorem Gut.heldB {W G} {bo : Option Int} {a b : World D} (h : Gut W G a b) (hh : HeldB bo Λ a.haelt) :
    HeldB bo Λ b.haelt := by
  rw [h.haelt]; exact hh

/-- Ein Weltumbau, der Slots und Globale laesst, haelt den Rahmen. -/
theorem rahmen_gleich {W G} {σ σ' : World D} (hs : σ'.slots = σ.slots) (hg : σ'.globs = σ.globs) :
    Rahmen W G σ σ' := ⟨fun t _ k f => by rw [hs], fun g _ => by rw [hg]⟩

/-- Ein Zugriffsereignis, das die Sperren `h` aufzeichnet. -/
def Ereignis.zugriffMit (h : List D.Lock) : Ereignis D → Prop
  | .zugriff _ _ _ h' => h' = h
  | .gzugriff _ _ _ h' => h' = h
  | .nimmt _ _ => False
  | .gibt _ => False
  -- An answer from outside records no lock and changes none: it may sit among the accesses.
  | .fremd _ => True

theorem offen_append_zugriffe (h : List D.Lock) : ∀ (es s : List (Ereignis D)),
    (∀ e ∈ es, e.zugriffMit h) → offen (es ++ s) = offen s := by
  intro es
  induction es with
  | nil => intro s _; rfl
  | cons e es ih =>
      intro s hz
      have he := hz e List.mem_cons_self
      have ih' := ih s (fun e' he' => hz e' (List.mem_cons_of_mem _ he'))
      cases e <;> simp only [Ereignis.zugriffMit] at he <;> simp only [List.cons_append, offen, ih']

/-- Reading preserves the held locks: `lese` only prefixes `zugriff`
    events, which `offen` ignores. -/
theorem lese_haelt (σ : World D) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob)) :
    (σ.lese Λ orte).haelt = σ.haelt := by
  show offen ((orte.map fun o => match o with
      | .inl t => Ereignis.zugriff t false Λ σ.haelt
      | .inr g => Ereignis.gzugriff g false Λ σ.haelt) ++ σ.spur) = offen σ.spur
  exact offen_append_zugriffe σ.haelt _ _ (fun e he => by
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
    cases o <;> simp only [Ereignis.zugriffMit])

theorem konsistent_merke (h : List D.Lock) : ∀ (es s : List (Ereignis D)),
    (∀ e ∈ es, e.zugriffMit h) → h = offen s → Konsistent s → Konsistent (es ++ s) := by
  intro es
  induction es with
  | nil => intro s _ _ hs; exact hs
  | cons e es ih =>
      intro s hz hh hs
      have he := hz e List.mem_cons_self
      have hrest : ∀ e' ∈ es, e'.zugriffMit h := fun e' he' => hz e' (List.mem_cons_of_mem _ he')
      simp only [List.cons_append]
      apply konsistent_cons _ (ih s hrest hh hs)
      cases e <;> simp only [Ereignis.zugriffMit] at he <;>
        simp only [Ereignis.passt, he, hh, offen_append_zugriffe h es s hrest]

theorem gut_merke {W G} (σ : World D) (es : List (Ereignis D)) (hz : ∀ e ∈ es, e.zugriffMit σ.haelt)
    (h : ∀ e ∈ es, e.gut) : Gut W G σ (σ.merke es) :=
  ⟨rahmen_gleich rfl rfl,
   show offen (es ++ σ.spur) = offen σ.spur from offen_append_zugriffe _ es σ.spur hz,
   fun e he => by
    simp only [World.merke, List.mem_append] at he
    rcases he with he | he
    · exact .inr (h e he)
    · exact .inl he,
   fun k => konsistent_merke σ.haelt es σ.spur hz rfl k⟩

/-- **Asking outside the program is a good step**: the question is recorded, no cell changes, no lock moves. -/
theorem gut_fragt {W G} (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : Gut W G σ (σ.fragt q) :=
  gut_merke σ [.fremd q] (fun e he => by simp only [List.mem_singleton] at he; subst he; exact True.intro)
    (fun e he => by simp only [List.mem_singleton] at he; subst he; exact True.intro)

theorem fragt_haelt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) : (σ.fragt q).haelt = σ.haelt := rfl

theorem gut_lese {W G} (σ : World D) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob))
    (ho : ∀ o ∈ orte, OrtDarf Λ o) (hh : HeldIn Λ σ.haelt) : Gut W G σ (σ.lese Λ orte) := by
  apply gut_merke
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨o, _, rfl⟩ := he
    cases o <;> simp only [Ereignis.zugriffMit]
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨o, ho', rfl⟩ := he
    cases o with
    | inl t => exact ⟨ho _ ho', hh⟩
    | inr g => exact ⟨ho _ ho', hh⟩

theorem storeSlot_andere (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (t' : D.Tab) (ht : t' ≠ t) (k' : Int) (f' : D.Feld t') :
    (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
  simp only [World.storeSlot, ht, ↓reduceDIte]

theorem storeGlob_andere (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) (g' : D.Glob) (hg : g' ≠ g) :
    (σ.storeGlob g v).globs g' = σ.globs g' := by
  simp only [World.storeGlob, hg, ↓reduceDIte]

theorem rahmen_storeSlot (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (t : D.Tab)
    (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f)) (hw : W t = true) :
    Rahmen W G σ (σ.storeSlot t k f v) := by
  refine ⟨fun t' ht' k' f' => ?_, fun g _ => rfl⟩
  have : t' ≠ t := fun h => by subst h; rw [hw] at ht'; cases ht'
  exact storeSlot_andere σ t k f v t' this k' f'

theorem rahmen_storeGlob (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (g : D.Glob)
    (v : Wert D (D.gtyp g)) (hg : G g = true) : Rahmen W G σ (σ.storeGlob g v) := by
  refine ⟨fun _ _ _ _ => rfl, fun g' hg' => ?_⟩
  have : g' ≠ g := fun h => by subst h; rw [hg] at hg'; cases hg'
  exact storeGlob_andere σ g v g' this

theorem gut_schreibSlot {W G} (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int) (f : D.Feld t)
    (v : Wert D (D.typ t f)) (hw : W t = true) (hL : darf D t Λ) (hh : HeldIn Λ σ.haelt) :
    Gut W G σ (σ.schreibSlot t Λ k f v) :=
  Gut.trans ⟨rahmen_storeSlot W G σ t k f v hw, rfl, fun e he => .inl he, id⟩
    (gut_merke _ _ (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; simp only [Ereignis.zugriffMit]; rfl)
      (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; exact ⟨hL, hh⟩))

theorem gut_schreibGlob {W G} (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    (hg : G g = true) (hL : gdarf D g Λ) (hh : HeldIn Λ σ.haelt) : Gut W G σ (σ.schreibGlob g Λ v) :=
  Gut.trans ⟨rahmen_storeGlob W G σ g v hg, rfl, fun e he => .inl he, id⟩
    (gut_merke _ _ (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; simp only [Ereignis.zugriffMit]; rfl)
      (by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he; exact ⟨hL, hh⟩))

theorem gut_schreibBytes {W G} (σ : World D) (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) (hw : W t = true) (hL : darf D t Λ) :
    ∀ (bs : List Byte) (k : Int), HeldIn Λ σ.haelt → Gut W G σ (σ.schreibBytes t f hf Λ k bs) := by
  intro bs
  induction bs generalizing σ with
  | nil => intro k _; exact Gut.refl _ _ _
  | cons b bs ih =>
      intro k hh
      simp only [World.schreibBytes]
      have h1 := gut_schreibSlot (W := W) (G := G) σ t Λ k f
        (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255))) hw hL hh
      exact h1.trans (ih _ _ (h1.heldIn hh))


end Gabbro.Grammatik
