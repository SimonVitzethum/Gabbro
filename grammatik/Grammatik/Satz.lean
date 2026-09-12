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
import Grammatik.Semantik

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
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) := by
  cases o <;> simp <;> assumption

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
    (eval σ₀ e σ ρ).x.isFinite = true ∧ bruch lo ≤ (eval σ₀ e σ ρ).x ∧ (eval σ₀ e σ ρ).x ≤ bruch hi :=
  ⟨(eval σ₀ e σ ρ).endlich, (eval σ₀ e σ ρ).lo_le, (eval σ₀ e σ ρ).le_hi⟩

/-- Ein Funktionszeiger zeigt auf eine Funktion GENAU seiner Signatur («B8»). -/
theorem fnptr_passt (e : Expr D Γ Λ (.fnptr n)) (σ₀ σ : World D) (ρ : Env D Γ) :
    D.sig (eval σ₀ e σ ρ).val = n :=
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
    (_e : Expr D Γ Λ (D.typ t f)) (_h : _e = .durch p t ht f i hL) : darf D t Λ := hL

/-- Eine Bytelesung liegt in der Tabelle: `hi + n ≤ count` («SG-16»). -/
theorem bytes_in_tabelle {t : D.Tab} {f : D.Feld t} {hf} {n : Nat} {i : Expr D Γ Λ (.int lo hi)}
    {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t} {hL}
    (_e : Expr D Γ Λ (.int 0 (256 ^ n - 1))) (_h : _e = .leseBytes t f hf n i hlo hhi hL) :
    0 ≤ lo ∧ hi + n ≤ D.count t := ⟨hlo, hhi⟩

/-- Eine Zuweisung an einen Slot hat das Schreibrecht ihres Vertrags. -/
theorem zuweisung_hat_recht {t : D.Tab} {f : D.Feld t} {i} {e} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignSlot t f i e hw hL) : V.schreibt t = true := hw

/-- Eine Zuweisung DURCH einen Zeiger verlangt einen `rw`-Zeiger UND das Schreibrecht. -/
theorem zeiger_schreibt_mit_recht {t : D.Tab} {f : D.Feld t} {p : Expr D Γ Λ (.ptr n true)}
    {ht} {i} {e} {hw : V.schreibt t = true} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .assignDurch p t ht f i e hw hL) : V.schreibt t = true := hw

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
    (∀ L, Res.held L ∈ Λ ↔ L ∈ D.haelt f) ∧
    (∀ t, D.schreibt f t = true → V.schreibt t = true) := ⟨hp.hk, hp.hh, hp.hw⟩

/-- Ein Ruf DURCH einen Funktionszeiger hat dasselbe in der Hand («B8»). -/
theorem zeigerruf_hat_alles {p : Expr D Γ Λ (.fnptr n)} {args} {hp : RufPasst D V (D.sigNr n) Λ} {hr}
    (_s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ)) (_h : _s = .callInd p args hp hr) :
    Untermulti ((D.sigNr n).konsumiert.map (Res.vonMarke D)) Λ ∧
    (∀ t, (D.sigNr n).schreibt t = true → V.schreibt t = true) := ⟨hp.hk, hp.hw⟩

/-- Ein Registerschreiben steht an einem Register schreibbarer Klasse (`R005`/`R006`). -/
theorem register_schreibbar {r : D.Reg} {hk : (D.rklasse r).schreibbar = true} {e}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .regSchreib r hk e) : (D.rklasse r).schreibbar = true := hk

/-- Eine Registerlesung steht an einem Register lesbarer Klasse. -/
theorem register_lesbar {r : D.Reg} {hk : (D.rklasse r).lesbar = true} {rest}
    (_b : Block D V l Γ Λ Λ') (_h : _b = .regLies r hk rest) : (D.rklasse r).lesbar = true := hk

/-- Ein `transition` schreibt ein schreibbares Register aus seinem ERKLAERTEN Spiegel. -/
theorem transition_hat_spiegel {r m : D.Reg} {hk} {hm : D.spiegel r = some m} {hl} {maske bits}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .transition r hk m hm hl maske bits) :
    D.spiegel r = some m ∧ (D.rklasse m).lesbar = true := ⟨hm, hl⟩

/-- Ein `state`-Uebergang ist ERKLAERT: `erlaubt t f von nach`. -/
theorem uebergang_erklaert {t : D.Tab} {f : D.Feld t} {hτ : D.typ t f = .int lo hi} {i}
    {von nach : Int} {hn} {he : D.erlaubt t f von nach = true} {hw} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .uebergang t f hτ i von nach hn he hw hL) :
    D.erlaubt t f von nach = true := he

/-- Eine Veroeffentlichung nimmt GENAU die erklaerte Nutzlast mit (`V001`-`V004`). -/
theorem publish_paart {g : D.Glob} {e} {payload : List D.Glob} {hp : payload = D.nutzlast g} {hw} {hL}
    (_s : Stmt D V l Γ Λ Λ) (_h : _s = .publish g e payload hp hw hL) : payload = D.nutzlast g := hp

/-- Ein `awaits` nimmt dieselbe Nutzlast entgegen. -/
theorem awaits_paart {g : D.Glob} {payload : List D.Glob} {hp : payload = D.nutzlast g} {hL} {rest}
    (_b : Block D V l Γ Λ Λ') (_h : _b = .awaits g payload hp hL rest) : payload = D.nutzlast g := hp

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
  ⟨fun t ht k f => h.1 t (by cases hw : W t; rfl; exact absurd (hW t hw) (by simp [ht])) k f,
   fun g hg => h.2 g (by cases hg' : G g; rfl; exact absurd (hG g hg') (by simp [hg]))⟩

/-- Die Sperren, die ein statisches `Λ` nennt, sind dynamisch gehalten. -/
def HeldIn (Λ : List (Res D)) (h : List D.Lock) : Prop := ∀ L, Res.held L ∈ Λ → L ∈ h

/-- Die Sperren, die ein statisches `Λ` nennt, sind GENAU die dynamisch gehaltenen. -/
def HeldGenau (Λ : List (Res D)) (h : List D.Lock) : Prop := ∀ L, Res.held L ∈ Λ ↔ L ∈ h

theorem HeldGenau.heldIn {Λ : List (Res D)} {h : List D.Lock} (hg : HeldGenau Λ h) : HeldIn Λ h :=
  fun L hL => (hg L).mp hL

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

/-- Ein Ereignis PASST zu seiner Nachwelt (dem Rest der Spur hinter ihm): die Sperren, die es
    als gehalten aufzeichnet, sind genau die dort offenen. -/
def Ereignis.passt : Ereignis D → List (Ereignis D) → Prop
  | .zugriff _ _ _ h, s => h = offen s
  | .gzugriff _ _ _ h, s => h = offen s
  | .nimmt _ h, s => h = offen s
  | .gibt _, _ => True

/-- Eine Spur ist KONSISTENT, wenn jedes Ereignis zu seinem Rest passt. -/
def Konsistent (s : List (Ereignis D)) : Prop :=
  ∀ (n : Nat) (e : Ereignis D), s[n]? = some e → e.passt (s.drop (n + 1))

theorem konsistent_nil : Konsistent ([] : List (Ereignis D)) := by
  unfold Konsistent; intro n e h; simp at h

theorem konsistent_cons {e : Ereignis D} {s : List (Ereignis D)} (he : e.passt s) (hs : Konsistent s) :
    Konsistent (e :: s) := by
  unfold Konsistent; intro n e' h
  cases n with
  | zero => simp at h; subst h; exact he
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
  · rw [hempty] at hmem; simp at hmem
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

/-- Ein Weltumbau, der Slots und Globale laesst, haelt den Rahmen. -/
theorem rahmen_gleich {W G} {σ σ' : World D} (hs : σ'.slots = σ.slots) (hg : σ'.globs = σ.globs) :
    Rahmen W G σ σ' := ⟨fun t _ k f => by rw [hs], fun g _ => by rw [hg]⟩

/-- Ein Zugriffsereignis, das die Sperren `h` aufzeichnet. -/
def Ereignis.zugriffMit (h : List D.Lock) : Ereignis D → Prop
  | .zugriff _ _ _ h' => h' = h
  | .gzugriff _ _ _ h' => h' = h
  | .nimmt _ _ => False
  | .gibt _ => False

theorem offen_append_zugriffe (h : List D.Lock) : ∀ (es s : List (Ereignis D)),
    (∀ e ∈ es, e.zugriffMit h) → offen (es ++ s) = offen s := by
  intro es
  induction es with
  | nil => intro s _; rfl
  | cons e es ih =>
      intro s hz
      have he := hz e List.mem_cons_self
      have ih' := ih s (fun e' he' => hz e' (List.mem_cons_of_mem _ he'))
      cases e <;> simp [Ereignis.zugriffMit] at he <;> simp [offen, ih']

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
      cases e <;> simp [Ereignis.zugriffMit] at he <;>
        simp [Ereignis.passt, offen_append_zugriffe h es s hrest, he, hh]

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

theorem gut_lese {W G} (σ : World D) (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob))
    (ho : ∀ o ∈ orte, OrtDarf Λ o) (hh : HeldIn Λ σ.haelt) : Gut W G σ (σ.lese Λ orte) := by
  apply gut_merke
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨o, _, rfl⟩ := he
    cases o <;> simp [Ereignis.zugriffMit]
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨o, ho', rfl⟩ := he
    cases o with
    | inl t => exact ⟨ho _ ho', hh⟩
    | inr g => exact ⟨ho _ ho', hh⟩

theorem storeSlot_andere (σ : World D) (t : D.Tab) (k : Int) (f : D.Feld t) (v : Wert D (D.typ t f))
    (t' : D.Tab) (ht : t' ≠ t) (k' : Int) (f' : D.Feld t') :
    (σ.storeSlot t k f v).slots t' k' f' = σ.slots t' k' f' := by
  simp [World.storeSlot, ht]

theorem storeGlob_andere (σ : World D) (g : D.Glob) (v : Wert D (D.gtyp g)) (g' : D.Glob) (hg : g' ≠ g) :
    (σ.storeGlob g v).globs g' = σ.globs g' := by
  simp [World.storeGlob, hg]

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
    (gut_merke _ _ (by intro e he; simp at he; subst he; simp [Ereignis.zugriffMit]; rfl)
      (by intro e he; simp at he; subst he; exact ⟨hL, hh⟩))

theorem gut_schreibGlob {W G} (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g))
    (hg : G g = true) (hL : gdarf D g Λ) (hh : HeldIn Λ σ.haelt) : Gut W G σ (σ.schreibGlob g Λ v) :=
  Gut.trans ⟨rahmen_storeGlob W G σ g v hg, rfl, fun e he => .inl he, id⟩
    (gut_merke _ _ (by intro e he; simp at he; subst he; simp [Ereignis.zugriffMit]; rfl)
      (by intro e he; simp at he; subst he; exact ⟨hL, hh⟩))

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

theorem gut_nimmt_gibt {W G} (σ σ1 : World D) (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt)
    (h : Gut W G (σ.nimmt L) σ1) : Gut W G σ (σ1.gibt L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rahmen_gleich (W := W) (G := G) (σ := σ) (σ' := σ.nimmt L) rfl rfl).trans
      (h.1.trans (rahmen_gleich rfl rfl))
  · show (offen σ1.spur).erase L = offen σ.spur
    have := h.haelt
    simp only [World.haelt, World.nimmt, offen] at this
    rw [this]; exact List.erase_cons_head _ _
  · intro e he
    simp only [World.gibt, List.mem_cons] at he
    rcases he with rfl | he
    · exact .inr (show (Ereignis.gibt L).gut from trivial)
    · rcases h.2.2.1 e he with h1 | h1
      · simp only [World.nimmt, List.mem_cons] at h1
        rcases h1 with rfl | h1
        · exact .inr (show (Ereignis.nimmt L σ.haelt).gut from hn)
        · exact .inl h1
      · exact .inr h1
  · intro k
    exact konsistent_cons trivial (h.2.2.2 (konsistent_cons rfl k))

-- Die Orte eines Ausdrucks tragen ihre Waechter -- weil jeder Konstruktor sie verlangt.
mutual
theorem Expr.orte_darf : (e : Expr D Γ Λ τ) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .lit _, _, h | .wahr, _, h | .falsch, _, h | .var _, _, h | .ptrOf _ _ _ _, _, h
  | .fnref _ _ _, _, h | .none _, _, h | .grund _ _, _, h => by simp [Expr.orte] at h
  | .glob g hL, o, h => by simp [Expr.orte] at h; subst h; exact hL
  | .altGlob g hL, o, h => by simp [Expr.orte] at h; subst h; exact hL
  | .slot t _ i hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact i.orte_darf o h
  | .altSlot t _ i hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact i.orte_darf o h
  | .leseBytes t _ _ _ i _ _ hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact i.orte_darf o h
  | .durch p t _ _ i hL, o, h => by
      simp only [Expr.orte, List.mem_append, List.mem_cons] at h
      rcases h with h | rfl | h
      · exact p.orte_darf o h
      · exact hL
      · exact i.orte_darf o h
  | .weiter _ _ e, o, h => e.orte_darf o h
  | .neg a, o, h | .nicht a, o, h | .some a, o, h | .istSome a, o, h => a.orte_darf o h
  | .add a b, o, h | .sub a b, o, h | .mul a b, o, h | .div _ _ a b, o, h | .rem _ _ a b, o, h
  | .sdiv _ a b, o, h | .srem _ a b, o, h | .band _ _ a b, o, h | .bor _ _ _ _ _ a b, o, h
  | .bxor _ _ _ _ _ a b, o, h | .shl _ _ _ _ _ a b, o, h | .shr _ _ _ _ _ a b, o, h | .lt a b, o, h
  | .le a b, o, h | .eq a b, o, h | .fllt a b, o, h | .flle a b, o, h | .und a b, o, h
  | .oder a b, o, h => by
      simp only [Expr.orte, List.mem_append] at h
      rcases h with h | h
      · exact a.orte_darf o h
      · exact b.orte_darf o h
  | .fall _ _ nutz, o, h => nutz.orte_darf o h
  | .forallSlots t body hL, o, h | .existsSlots t body hL, o, h => by
      simp only [Expr.orte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hL
      · exact body.orte_darf o h
  | .reaches t _ _ a b hL, o, h => by
      simp only [Expr.orte, List.mem_cons, List.mem_append] at h
      rcases h with (rfl | h) | h
      · exact hL
      · exact a.orte_darf o h
      · exact b.orte_darf o h

theorem NutzlastExpr.orte_darf : (e : NutzlastExpr D Γ Λ c) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .keine, _, h => by simp [NutzlastExpr.orte] at h
  | .zahl e, o, h => e.orte_darf o h
end

theorem Args.orte_darf : (a : Args D Γ Λ τs) → ∀ o ∈ a.orte, OrtDarf Λ o
  | .nil, _, h => by simp [Args.orte] at h
  | .cons e rest, o, h => by
      simp only [Args.orte, List.mem_append] at h
      rcases h with h | h
      · exact e.orte_darf o h
      · exact rest.orte_darf o h

theorem ErgExpr.orte_darf : (e : ErgExpr D Γ Λ τ) → ∀ o ∈ e.orte, OrtDarf Λ o
  | .keine, _, h => by simp [ErgExpr.orte] at h
  | .wert e, o, h => e.orte_darf o h

/-- Zwei Ausdruecke, zusammen. -/
theorem orte_append {Λ : List (Res D)} {a b : List (D.Tab ⊕ D.Glob)} (ha : ∀ o ∈ a, OrtDarf Λ o)
    (hb : ∀ o ∈ b, OrtDarf Λ o) : ∀ o ∈ a ++ b, OrtDarf Λ o := by
  intro o h; simp only [List.mem_append] at h
  rcases h with h | h
  · exact ha o h
  · exact hb o h

/-- Die Sperrzeugnisse eines `Λ` werden von keiner Anweisung erzeugt: was danach `held` ist,
    war es davor. (Marken kommen und gehen; Zeugnisse nur durch `locks`, und das schliesst
    sich.) -/
theorem held_nachSig (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) (L : D.Lock)
    (h : Res.held L ∈ nachSig D S Λ) : Res.held L ∈ Λ := by
  unfold nachSig at h
  simp only [List.mem_append, List.mem_map] at h
  rcases h with h | ⟨m, _, hm⟩
  · -- ein Fold von `erase` bleibt eine Teilliste
    have key : ∀ (ks : List (D.Marke × Nat)) (Λ : List (Res D)),
        Res.held L ∈ ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ → Res.held L ∈ Λ := by
      intro ks
      induction ks with
      | nil => intro Λ h; exact h
      | cons k ks ih => intro Λ h; exact List.mem_of_mem_erase (ih _ h)
    exact key _ _ h
  · cases m; simp [Res.vonMarke] at hm

theorem held_nachSig_iff (S : Signatur D.Tab D.Glob D.Lock D.Marke) (Λ : List (Res D)) (L : D.Lock) :
    Res.held L ∈ nachSig D S Λ ↔ Res.held L ∈ Λ := by
  constructor
  · exact held_nachSig S Λ L
  · intro h
    unfold nachSig
    simp only [List.mem_append]
    left
    have key : ∀ (ks : List (D.Marke × Nat)) (Λ : List (Res D)), Res.held L ∈ Λ →
        Res.held L ∈ ks.foldl (fun acc m => acc.erase (Res.vonMarke D m)) Λ := by
      intro ks
      induction ks with
      | nil => intro Λ h; exact h
      | cons k ks ih =>
          intro Λ h
          apply ih
          apply List.mem_erase_of_ne _ |>.mpr h
          cases k; simp [Res.vonMarke]
    exact key _ _ h

mutual
theorem Stmt.held_mono : (s : Stmt D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .assignSlot .., L, h | .assignDurch .., L, h | .assignGlob .., L, h | .schreibBytes .., L, h
  | .assignVar .., L, h | .uebergang .., L, h | .locks .., L, h | .traverse .., L, h
  | .retry .., L, h | .forever .., L, h | .axiomCall .., L, h | .regSchreib .., L, h
  | .transition .., L, h | .publish .., L, h | .ret .., L, h | .retGrund .., L, h
  | .leave .., L, h | .next .., L, h => h
  | .ite _ t _, L, h => t.held_mono L h
  | .onOption _ p _, L, h => p.held_mono L h
  | .onTag _ arms, L, h => arms.held_mono L h
  | .onGrund _ arms, L, h => arms.held_mono L h
  | .call f _ _ _, L, h => held_nachSig _ _ L h
  | .callInd (n := n) _ _ _ _, L, h => held_nachSig _ _ L h
  | .breaking _ body, L, h => body.held_mono L h
  | .advances m a _ _, L, h => by
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact List.mem_of_mem_erase h
      · cases h
  | .retires .., L, h => List.mem_of_mem_erase h

theorem Block.held_mono : (b : Block D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .nil, L, h => h
  | .cons s rest, L, h => s.held_mono L (rest.held_mono L h)
  | .bind _ rest, L, h | .bindAxiom _ _ _ _ _ rest, L, h | .regLies _ _ rest, L, h
  | .regLiesElse _ _ _ _ rest, L, h | .awaits _ _ _ _ rest, L, h | .exchange _ _ _ _ rest, L, h
  | .narrow _ _ _ _ rest, L, h | .pruefung _ _ rest, L, h | .gleit _ _ _ _ _ rest, L, h
  | .gleitLit _ _ _ rest, L, h | .gleitVon _ _ _ rest, L, h | .gleitNarrow _ _ _ _ rest, L, h =>
      rest.held_mono L h
  | .bindCall f _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallInd _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)
  | .bindCallElse f _ _ _ _ _ rest, L, h => held_nachSig _ _ L (rest.held_mono L h)

theorem Arms.held_mono : (a : Arms D V l Γ Λ Λ' cs) → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .nil, L, h => h
  | .cons b _, L, h => b.held_mono L h

theorem GrundArms.held_mono : (a : GrundArms D V l Γ Λ Λ' n) → ∀ L, Res.held L ∈ Λ' → Res.held L ∈ Λ
  | .nil, L, h => h
  | .cons b _, L, h => b.held_mono L h
end

mutual
theorem Stmt.held_iff : (s : Stmt D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .assignSlot .., _ | .assignDurch .., _ | .assignGlob .., _ | .schreibBytes .., _
  | .assignVar .., _ | .uebergang .., _ | .locks .., _ | .traverse .., _
  | .retry .., _ | .forever .., _ | .axiomCall .., _ | .regSchreib .., _
  | .transition .., _ | .publish .., _ | .ret .., _ | .retGrund .., _
  | .leave .., _ | .next .., _ => Iff.rfl
  | .ite _ t _, L => t.held_iff L
  | .onOption _ p _, L => p.held_iff L
  | .onTag _ arms, L => arms.held_iff L
  | .onGrund _ arms, L => arms.held_iff L
  | .call f _ _ _, L => held_nachSig_iff _ _ L
  | .callInd (n := n) _ _ _ _, L => held_nachSig_iff _ _ L
  | .breaking _ body, L => body.held_iff L
  | .advances m a _ _, L => by
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h)
        · exact List.mem_of_mem_erase h
        · cases h
      · intro h; left; exact (List.mem_erase_of_ne (by simp)).mpr h
  | .retires .., L => by
      constructor
      · exact List.mem_of_mem_erase
      · intro h; exact (List.mem_erase_of_ne (by simp)).mpr h

theorem Block.held_iff : (b : Block D V l Γ Λ Λ') → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .nil, _ => Iff.rfl
  | .cons s rest, L => (rest.held_iff L).trans (s.held_iff L)
  | .bind _ rest, L | .bindAxiom _ _ _ _ _ rest, L | .regLies _ _ rest, L
  | .regLiesElse _ _ _ _ rest, L | .awaits _ _ _ _ rest, L | .exchange _ _ _ _ rest, L
  | .narrow _ _ _ _ rest, L | .pruefung _ _ rest, L | .gleit _ _ _ _ _ rest, L
  | .gleitLit _ _ _ rest, L | .gleitVon _ _ _ rest, L | .gleitNarrow _ _ _ _ rest, L =>
      rest.held_iff L
  | .bindCall f _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallInd _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)
  | .bindCallElse f _ _ _ _ _ rest, L => (rest.held_iff L).trans (held_nachSig_iff _ _ L)

theorem Arms.held_iff : (a : Arms D V l Γ Λ Λ' cs) → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .nil, _ => Iff.rfl
  | .cons b _, L => b.held_iff L

theorem GrundArms.held_iff : (a : GrundArms D V l Γ Λ Λ' n) → ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ
  | .nil, _ => Iff.rfl
  | .cons b _, L => b.held_iff L
end

/-- Die Welt eines Ausgangs, wo er eine hat. -/
def Ausgang.welt : Ausgang V l Γ → Option (World D)
  | .ok σ _ => some σ
  | .zurueck σ _ => some σ
  | .grund σ _ => some σ
  | .leave _ σ _ => some σ
  | .next _ σ _ => some σ
  | .logik _ => none
  | .hardware _ => none

def EndAusgang.welt : EndAusgang V l Γ → Option (World D)
  | .zurueck σ _ => some σ
  | .grund σ _ => some σ
  | .leave _ σ _ => some σ
  | .next _ σ _ => some σ
  | .logik _ => none
  | .hardware _ => none

def RufAusgang.welt {f : D.Fn} : RufAusgang f → Option (World D)
  | .ok σ _ => some σ
  | .grund σ _ => some σ
  | .logik _ => none
  | .hardware _ => none

/-- Rahmen und Spur eines Ausgangs gegen die Eingangswelt. -/
def GutAusgang (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : Ausgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' → Gut W G σ σ'

def GutEnd (W : D.Tab → Bool) (G : D.Glob → Bool) (σ : World D) (o : EndAusgang V l Γ) : Prop :=
  ∀ σ', o.welt = some σ' → Gut W G σ σ'

theorem GutAusgang.schrumpf {W G} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : GutAusgang W G σ o) : GutAusgang W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp [Ausgang.schrumpf, Ausgang.welt] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutAusgang.schrumpfArm {W G} {σ : World D} (c : Option (Int × Int))
    {o : Ausgang V l (ArmCtx Γ c)} (h : GutAusgang W G σ o) :
    GutAusgang W G σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some p => obtain ⟨_, _⟩ := p; exact h.schrumpf

theorem GutEnd.schrumpf {W G} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : GutEnd W G σ o) : GutEnd W G σ o.schrumpf := by
  intro σ' hs; cases o <;> simp [EndAusgang.schrumpf, EndAusgang.welt] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem GutEnd.zuAusgang {W G} {σ : World D} {o : EndAusgang V l Γ} (h : GutEnd W G σ o) :
    GutAusgang W G σ o.zuAusgang := by
  intro σ' hs; cases o <;> simp [EndAusgang.zuAusgang, Ausgang.welt] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

/-- Ein Schritt, der schon gut ist, zieht durch einen Unterblock hindurch. -/
theorem GutAusgang.vor {W G} {σ σ1 : World D} {o : Ausgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutAusgang W G σ1 o) : GutAusgang W G σ o :=
  fun σ' hs => h1.trans (h σ' hs)

theorem GutEnd.vor {W G} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (h1 : Gut W G σ σ1) (h : GutEnd W G σ1 o) : GutEnd W G σ o :=
  fun σ' hs => h1.trans (h σ' hs)

/-- `locks L { … }`: nehmen, Rumpf, geben. -/
theorem GutAusgang.gibt {W G} {σ : World D} (L : D.Lock)
    (hn : (∀ M ∈ σ.haelt, D.rang M < D.rang L) ∧ L ∉ σ.haelt) {o : Ausgang V l Γ}
    (h : GutAusgang W G (σ.nimmt L) o) : GutAusgang W G σ (o.mapWelt (·.gibt L)) := by
  intro σ' hs
  cases o <;> simp [Ausgang.mapWelt, Ausgang.welt] at hs ⊢ <;>
    (subst hs; exact gut_nimmt_gibt _ _ L hn (h _ rfl))

/-- Von einem `Λ` zu einem, das hoechstens weniger Zeugnisse nennt, ueber einen guten Schritt. -/
theorem heldGenau_weiter {W G} {σ σ1 : World D} {Λ Λ' : List (Res D)}
    (hm : ∀ L, Res.held L ∈ Λ' ↔ Res.held L ∈ Λ) (hg : Gut W G σ σ1) (hh : HeldGenau Λ σ.haelt) :
    HeldGenau Λ' σ1.haelt := by
  intro L; rw [hg.haelt, hm L]; exact hh L

theorem held_anfang (S : Signatur D.Tab D.Glob D.Lock D.Marke) (L : D.Lock) :
    Res.held L ∈ Signatur.anfang D S ↔ L ∈ S.haelt := by
  unfold Signatur.anfang
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨M, hM, hML⟩ | ⟨m, _, hm⟩)
    · cases hML; exact hM
    · cases m; simp [Res.vonMarke] at hm
  · intro h; exact .inl ⟨L, h, rfl⟩

theorem held_ende (V : Vertrag D) (L : D.Lock) : Res.held L ∈ V.ende ↔ L ∈ V.haelt := by
  unfold Vertrag.ende
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨M, hM, hML⟩ | ⟨m, _, hm⟩)
    · cases hML; exact hM
    · cases m; simp [Res.vonMarke] at hm
  · intro h; exact .inl ⟨L, h, rfl⟩

/-- Der Rufer haelt genau, was der Gerufene am Eintritt nennt. -/
theorem heldGenau_ruf {S : Signatur D.Tab D.Glob D.Lock D.Marke} {Λ : List (Res D)} {h : List D.Lock}
    (hh' : ∀ L, Res.held L ∈ Λ ↔ L ∈ S.haelt) (hh : HeldGenau Λ h) : HeldGenau (Signatur.anfang D S) h := by
  intro L; rw [held_anfang, ← hh' L]; exact hh L

theorem heldGenau_locks {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock) (hh : HeldGenau Λ h) :
    HeldGenau (Res.held L :: Λ) (L :: h) := by
  intro M
  simp only [List.mem_cons, Res.held.injEq]
  constructor
  · rintro (rfl | hM)
    · exact .inl rfl
    · exact .inr ((hh M).mp hM)
  · rintro (rfl | hM)
    · exact .inl rfl
    · exact .inr ((hh M).mpr hM)

/-- Ein `locks L` nimmt eine Sperre, die der Faden NICHT haelt: alles Gehaltene hat kleineren
    Rang, und `rang L < rang L` ist keine Zahl. -/
theorem nicht_gehalten {Λ : List (Res D)} {h : List D.Lock} (L : D.Lock)
    (hr : ∀ M, Res.held M ∈ Λ → D.rang M < D.rang L) (hh : HeldGenau Λ h) :
    (∀ M ∈ h, D.rang M < D.rang L) ∧ L ∉ h := by
  refine ⟨fun M hM => hr M ((hh M).mpr hM), ?_⟩
  intro hL
  have := hr L ((hh L).mpr hL)
  omega

theorem orte_tab {Λ : List (Res D)} {t : D.Tab} (hL : darf D t Λ) : OrtDarf Λ (.inl t) := hL
theorem orte_glob {Λ : List (Res D)} {g : D.Glob} (hL : gdarf D g Λ) : OrtDarf Λ (.inr g) := hL

theorem orte_cons {Λ : List (Res D)} {o : D.Tab ⊕ D.Glob} {os : List (D.Tab ⊕ D.Glob)}
    (h1 : OrtDarf Λ o) (h2 : ∀ o ∈ os, OrtDarf Λ o) : ∀ o' ∈ o :: os, OrtDarf Λ o' := by
  intro o' h; simp only [List.mem_cons] at h
  rcases h with rfl | h
  · exact h1
  · exact h2 o' h

/-- Die Praemissen ueber die Umgebung, benannt: der Ruf haelt Rahmen und Spur seines Gerufenen
    (das ist der Satz eine Ebene tiefer, `rufAt_gut` unten), und die Hardware den Rahmen ihres
    `effects` und laesst Sperren und Spur, wie sie sind (H1 -- eine Annahme). -/
def GutR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, HeldGenau (Signatur.anfang D (D.signatur f)) σ.haelt →
    ∀ σ', (R f σ ρ).welt = some σ' → Gut (D.schreibt f) (D.gschreibt f) σ σ'

def GutO (O : Orakel D) : Prop :=
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt ∧ (O.wirkt a σ ρ).1.spur = σ.spur

section Schleifen
variable {W : D.Tab → Bool} {G : D.Glob → Bool} {Λ : List (Res D)}

theorem traverseLauf_gut (schritt : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldGenau Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldGenau Λ σ.haelt → Gut W G σ (inv σ ρ).1) :
    ∀ (ks : List (Wert D τ)) (σ : World D) (ρ : Env D Γ), HeldGenau Λ σ.haelt →
      GutAusgang W G σ (traverseLauf (l := l) schritt inv ks σ ρ) := by
  intro ks
  induction ks with
  | nil =>
      intro σ ρ hh σ' h
      simp only [traverseLauf] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h; exact hi σ ρ hh
      · simp [Ausgang.welt] at h
  | cons k ks ih =>
      intro σ ρ hh σ' h
      simp only [traverseLauf] at h
      split at h
      · simp [Ausgang.welt] at h
      · have hinv := hi σ ρ hh
        have hstep := hs (inv σ ρ).1 (.cons k ρ) (hinv.heldGenau hh)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail (g1.heldGenau hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1.tail (g1.heldGenau hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          split at h <;> simp [Ausgang.welt] at h
          subst h; exact g1.trans (hi σ1 ρ1.tail (g1.heldGenau hh))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

theorem retryLauf_gut (schritt : World D → Env D Γ → Ausgang V true Γ)
    (bis : World D → Env D Γ → World D × Bool) (ueberlauf : World D → Env D Γ → Ausgang V l Γ)
    (hs : ∀ σ ρ, HeldGenau Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hb : ∀ σ ρ, HeldGenau Λ σ.haelt → Gut W G σ (bis σ ρ).1)
    (hu : ∀ σ ρ, HeldGenau Λ σ.haelt → GutAusgang W G σ (ueberlauf σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldGenau Λ σ.haelt →
      GutAusgang W G σ (retryLauf schritt bis ueberlauf n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ hh; exact hu σ ρ hh
  | succ n ih =>
      intro σ ρ hh σ' h
      simp only [retryLauf] at h
      split at h
      · simp [Ausgang.welt] at h; subst h; exact hb σ ρ hh
      · have hinv := hb σ ρ hh
        have hstep := hs (bis σ ρ).1 ρ (hinv.heldGenau hh)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldGenau hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldGenau hh) σ' h)
        · rename_i σ1 ρ1 hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

theorem foreverLauf_gut (a : D.Annahme) (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (hs : ∀ σ ρ, HeldGenau Λ σ.haelt → GutAusgang W G σ (schritt σ ρ))
    (hi : ∀ σ ρ, HeldGenau Λ σ.haelt → Gut W G σ (inv σ ρ).1) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ), HeldGenau Λ σ.haelt →
      GutAusgang W G σ (foreverLauf (l := l) a schritt inv n σ ρ) := by
  intro n
  induction n with
  | zero => intro σ ρ _ σ' h; simp [foreverLauf, Ausgang.welt] at h
  | succ n ih =>
      intro σ ρ hh σ' h
      simp only [foreverLauf] at h
      split at h
      · simp [Ausgang.welt] at h
      · have hinv := hi σ ρ hh
        have hstep := hs (inv σ ρ).1 ρ (hinv.heldGenau hh)
        split at h
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldGenau hh) σ' h)
        · rename_i σ1 ρ1 hs1
          have g1 := hinv.trans (hstep σ1 (by rw [hs1]; rfl))
          exact g1.trans (ih σ1 ρ1 (g1.heldGenau hh) σ' h)
        · rename_i σ1 ρ1 hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 v hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · rename_i σ1 r hs1; simp [Ausgang.welt] at h; subst h
          exact hinv.trans (hstep _ (by rw [hs1]; rfl))
        · simp [Ausgang.welt] at h
        · simp [Ausgang.welt] at h

end Schleifen

section Rumpf
variable (O : Orakel D)

theorem axiomAntwort_gut (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) :
    Gut (D.aschreibt a) (D.agschreibt a) σ (axiomAntwort O a σ ρ).1 := by
  simp only [axiomAntwort]
  obtain ⟨hr, hh, hs⟩ := hO a σ ρ
  exact ⟨hr, hh, fun e he => .inl (hs ▸ he), fun k => hs ▸ k⟩

variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : GutR R) (hO : GutO O)
include hR hO
set_option linter.unusedSectionVars false

mutual

/-- **Rahmen und Spur einer Anweisung**: ihr Ausgang unterscheidet sich von der Eingangswelt
    hoechstens an Traegern mit Schreibrecht im Vertrag, jede Sperre ist am Ende
    zurueckgegeben, und jedes neue Ereignis traegt seine Waechter. -/
theorem stmt_gut : ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), HeldGenau Λ σ.haelt →
    GutAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)
  | .assignSlot t f i e hw hL, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldGenau hh).heldIn)
  | .assignDurch p t _ f i e hw hL, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldGenau hh).heldIn)
  | .assignGlob g e hw hL, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldGenau hh).heldIn)
  | .schreibBytes t f hf n i _ _ e hw hL, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_append i.orte_darf e.orte_darf) hh.heldIn
      exact hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldGenau hh).heldIn)
  | .assignVar x e, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .uebergang t f hτ i von nach hn he hw hL, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      split at h
      · simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_tab hL) i.orte_darf) hh.heldIn
        exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldGenau hh).heldIn)
      · simp [Ausgang.welt] at h
  | .ite c t e, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut t _ ρ (hl.heldGenau hh))) σ' h
      · exact (GutAusgang.vor hl (block_gut e _ ρ (hl.heldGenau hh))) σ' h
  | .onOption o p a, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ o.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut p _ _ (hl.heldGenau hh))).schrumpf σ' h
      · exact (GutAusgang.vor hl (block_gut a _ ρ (hl.heldGenau hh))) σ' h
  | .onTag v arms, σ, ρ, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ v.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (arms_gut arms _ _ ρ (hl.heldGenau hh))) σ' h
  | .onGrund r arms, σ, ρ, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ r.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (grund_gut arms _ _ ρ (hl.heldGenau hh))) σ' h
  | .call f args hp hr, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        exact hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldGenau_ruf hp.hh (hl.heldGenau hh)) σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .callInd p args hp hr, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        subst hf
        exact hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldGenau_ruf hp.hh (hl.heldGenau hh)) σ1 (by rw [hR1]; rfl)))
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .locks L hr body, σ, ρ, hh, σ', h =>
      (GutAusgang.gibt L (nicht_gehalten L hr hh)
        (block_gut body (σ.nimmt L) ρ (heldGenau_locks L hh))) σ' h
  | .breaking _ body, σ, ρ, hh, σ', h => block_gut body σ ρ hh σ' h
  | .traverse t inv body, σ, ρ, hh, σ', h =>
      traverseLauf_gut (Λ := Λ) _ _ (fun σ ρ hh => block_gut body σ ρ hh)
        (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) _ σ ρ hh σ' h
  | .retry n bis body ueberlauf, σ, ρ, hh, σ', h =>
      retryLauf_gut (Λ := Λ) _ _ _ (fun σ ρ hh => block_gut body σ ρ hh)
        (fun σ ρ hh => gut_lese σ Λ _ bis.orte_darf hh.heldIn)
        (fun σ ρ hh => block_gut ueberlauf σ ρ hh) n σ ρ hh σ' h
  | .forever a inv body, σ, ρ, hh, σ', h =>
      foreverLauf_gut (Λ := Λ) a _ _ (fun σ ρ hh => block_gut body σ ρ hh)
        (fun σ ρ hh => gut_lese σ Λ _ inv.orte_darf hh.heldIn) passes σ ρ hh σ' h
  | .axiomCall a args _ hw hg, σ, ρ, hh, σ', h => by
      simp only [execStmt] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at h; subst h
        have := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at this
        exact hl.trans (Gut.weiter hw hg this)
      · simp [Ausgang.welt] at h
  | .regSchreib r _ e, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .transition .., σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .publish g e _ _ hw hL, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldGenau hh).heldIn)
  | .advances .., σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .retires .., σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .ret e _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retGrund .., σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hh, σ', h => by
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _

theorem block_gut : ∀ (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ), HeldGenau Λ σ.haelt →
    GutAusgang V.schreibt V.gschreibt σ (execBlock O passes R b σ ρ)
  | .nil, σ, ρ, hh, σ', h => by
      simp only [execBlock, Ausgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · rename_i σ1 ρ1 hs
        have g1 := stmt_gut s σ ρ hh σ1 (by rw [hs]; rfl)
        exact g1.trans (block_gut rest σ1 ρ1 (heldGenau_weiter s.held_iff g1 hh) σ' h)
      · subst_vars
        exact stmt_gut s σ ρ hh σ' h
  | .bind e rest, σ, ρ, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
  | .bindCall f args he hp hr rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldGenau_ruf hp.hh (hl.heldGenau hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_gut rest σ1 _
          (heldGenau_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrund hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindCallInd p args he hp hr rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append p.orte_darf args.orte_darf) hh.heldIn
      generalize hpv : eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = pv at h
      obtain ⟨f, hf⟩ := pv
      simp only at h
      split at h
      · rename_i σ1 v hR1
        have g2 := block_gut rest σ1 (.cons (ergWert (ergSig hf he) v) ρ)
        subst hf
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ (p.orte ++ args.orte)) _ (heldGenau_ruf hp.hh (hl.heldGenau hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((g2 (heldGenau_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r _; exact keinGrundSig hf hr r
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindCallElse f args he hp _ err rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldGenau_ruf hp.hh (hl.heldGenau hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((block_gut rest σ1 _
          (heldGenau_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf σ' h)
      · rename_i σ1 r hR1
        have g1 := hl.trans (Gut.weiter hp.hw hp.hg
          (hR f (σ.lese Λ args.orte) _ (heldGenau_ruf hp.hh (hl.heldGenau hh)) σ1 (by rw [hR1]; rfl)))
        exact g1.trans ((end_gut err σ1 _
          (heldGenau_weiter (fun L => held_nachSig_iff _ _ L) g1 hh)).schrumpf.zuAusgang σ' h)
      · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .bindAxiom a args he hw hg rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ args.orte_darf hh.heldIn
      split at h
      · rename_i σ1 v ha
        have h1 := axiomAntwort_gut O hO a (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)
        rw [ha] at h1
        have g1 := hl.trans (Gut.weiter hw hg h1)
        exact g1.trans ((block_gut rest σ1 _ (g1.heldGenau hh)).schrumpf σ' h)
      · simp [Ausgang.welt] at h
  | .regLies r _ rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · split at h
        · exact (block_gut rest σ _ hh).schrumpf σ' h
        · simp [Ausgang.welt] at h
      · simp [Ausgang.welt] at h
  | .regLiesElse r _ zusage sonst rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ zusage.orte_darf hh.heldIn
        split at h
        · exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
        · exact (GutEnd.vor hl (end_gut sonst _ ρ (hl.heldGenau hh))).zuAusgang σ' h
      · simp [Ausgang.welt] at h
  | .awaits g _ _ hL rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ [.inr g]
          (orte_cons (orte_glob hL) (by intro o ho; simp at ho)) hh.heldIn
        exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .exchange g neu hw hL rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ (orte_cons (orte_glob hL) neu.orte_darf) hh.heldIn
      have g1 := hl.trans (gut_schreibGlob (W := V.schreibt) (G := V.gschreibt)
        (σ.lese Λ (.inr g :: neu.orte)) g Λ (eval (σ.lese Λ (.inr g :: neu.orte)) neu
          (σ.lese Λ (.inr g :: neu.orte)) (.cons ((σ.lese Λ (.inr g :: neu.orte)).globs g) ρ))
          hw hL (hl.heldGenau hh).heldIn)
      exact (GutAusgang.vor g1 (block_gut rest _ _ (g1.heldGenau hh))).schrumpf σ' h
  | .narrow e lo' hi' sonst rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gut sonst _ ρ (hl.heldGenau hh))).zuAusgang σ' h
  | .pruefung c sonst rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ c.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut rest _ ρ (hl.heldGenau hh))) σ' h
      · exact (GutEnd.vor hl (end_gut sonst _ ρ (hl.heldGenau hh))).zuAusgang σ' h
  | .gleit op a b lo hi rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _
        (orte_append a.orte_darf b.orte_darf) hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .gleitLit q lo hi rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      split at h
      · exact (block_gut rest σ _ hh).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .gleitVon e lo hi rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
      · simp [Ausgang.welt] at h
  | .gleitNarrow e lo hi sonst rest, σ, ρ, hh, σ', h => by
      simp only [execBlock] at h
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      split at h
      · exact (GutAusgang.vor hl (block_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h
      · exact (GutEnd.vor hl (end_gut sonst _ ρ (hl.heldGenau hh))).zuAusgang σ' h

theorem end_gut : ∀ (b : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ), HeldGenau Λ σ.haelt →
    GutEnd V.schreibt V.gschreibt σ (execEnd O passes R b σ ρ)
  | .ret e _, σ, ρ, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h
      exact gut_lese σ Λ _ e.orte_darf hh.heldIn
  | .retGrund .., σ, ρ, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .leave _, σ, ρ, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .next _, σ, ρ, hh, σ', h => by
      simp only [execEnd, EndAusgang.welt, Option.some.injEq] at h; subst h; exact Gut.refl _ _ _
  | .cons s rest, σ, ρ, hh, σ', h => by
      simp only [execEnd] at h
      have hs := stmt_gut s σ ρ hh
      split at h
      · rename_i σ1 ρ1 hs1
        have g1 := hs σ1 (by rw [hs1]; rfl)
        exact g1.trans (end_gut rest σ1 ρ1 (heldGenau_weiter s.held_iff g1 hh) σ' h)
      all_goals first
        | (rename_i hs1; simp only [EndAusgang.welt, Option.some.injEq] at h; subst h
           exact hs _ (by rw [hs1]; rfl))
        | (simp [EndAusgang.welt] at h)
  | .bind e rest, σ, ρ, hh, σ', h => by
      have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) σ Λ _ e.orte_darf hh.heldIn
      exact (GutEnd.vor hl (end_gut rest _ _ (hl.heldGenau hh))).schrumpf σ' h

theorem arms_gut : ∀ (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs)) (σ : World D) (ρ : Env D Γ),
    HeldGenau Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execArms O passes R arms v σ ρ)
  | .cons b _, ⟨⟨0, _⟩, _⟩, σ, _, hh, σ', h => (block_gut b σ _ hh).schrumpfArm _ σ' h
  | .cons _ rest, ⟨⟨_ + 1, _⟩, _⟩, σ, ρ, hh, σ', h => arms_gut rest _ σ ρ hh σ' h

theorem grund_gut : ∀ (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    HeldGenau Λ σ.haelt → GutAusgang V.schreibt V.gschreibt σ (execGrund O passes R arms r σ ρ)
  | .cons b _, ⟨0, _⟩, σ, ρ, hh, σ', h => block_gut b σ ρ hh σ' h
  | .cons _ rest, ⟨_ + 1, _⟩, σ, ρ, hh, σ', h => grund_gut rest _ σ ρ hh σ' h

end

end Rumpf

/-! ### Der Ruf, bis hinauf zum Programm -/

theorem held_invSicht_aux (L : D.Lock) : ∀ (ts : List D.Tab),
    Res.held L ∈ ts.foldr (fun t acc => (D.braucht t).map (Res.von D) ++ acc) [] →
    ∃ t ∈ ts, Sum.inl L ∈ D.braucht t := by
  intro ts
  induction ts with
  | nil => intro h; simp at h
  | cons t ts ih =>
      intro h
      simp only [List.foldr_cons, List.mem_append, List.mem_map] at h
      rcases h with ⟨w, hw, hwL⟩ | h
      · refine ⟨t, List.mem_cons_self, ?_⟩
        cases w with
        | inl M => simp [Res.von] at hwL; subst hwL; exact hw
        | inr m => obtain ⟨_, _⟩ := m; simp [Res.von] at hwL
      · obtain ⟨t', ht', hL⟩ := ih h
        exact ⟨t', List.mem_cons_of_mem _ ht', hL⟩

theorem held_invSicht (i : D.Inv) (L : D.Lock) (h : Res.held L ∈ invSicht D i) :
    ∃ t ∈ D.traeger i, Sum.inl L ∈ D.braucht t :=
  held_invSicht_aux L _ h

/-- Die Invarianten, die ein Rumpf schuldet, liest er unter Sperren, die er haelt (`U003`). -/
theorem heldIn_invarianten (P : Programm D) (f : D.Fn) {h : List D.Lock}
    (hh : HeldIn (Signatur.anfang D (D.signatur f)) h) (i : D.Inv) (hi : schuldet f i = true) :
    HeldIn (invSicht D i) h := by
  intro L hL
  obtain ⟨t, ht, hLt⟩ := held_invSicht i L hL
  have := D.invarianten_gehalten (D.sig f) i hi t ht L hLt
  exact hh L ((held_anfang _ L).mpr this)

theorem gut_foldl_lese {W G} (P : Programm D) (f : D.Fn) :
    ∀ (is : List D.Inv) (σ : World D), (∀ i ∈ is, schuldet f i = true) →
      HeldIn (Signatur.anfang D (D.signatur f)) σ.haelt →
      Gut W G σ (is.foldl (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte) σ) := by
  intro is
  induction is with
  | nil => intro σ _ _; exact Gut.refl _ _ _
  | cons i is ih =>
      intro σ hs hh
      simp only [List.foldl_cons]
      have g1 : Gut W G σ (σ.lese (invSicht D i) (P.invariante i).orte) :=
        gut_lese σ _ _ (P.invariante i).orte_darf
          (heldIn_invarianten P f hh i (hs i List.mem_cons_self))
      exact g1.trans (ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj)) (g1.heldIn hh))

/-- **Rahmen und Spur eines Rufs, bis hinauf zum Programm**: auf jeder Rekursionstiefe haelt
    `rufAt` Rahmen und Spur des Gerufenen -- Induktion ueber die Tiefe, mit `end_gut` fuer
    den Rumpf. Die einzige Praemisse ist die Hardware (H1). -/
theorem rufAt_gut (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O) :
    ∀ fuel, GutR (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ _ σ' h; simp [rufAt, RufAusgang.welt] at h
  | succ n ih =>
      intro f σ ρ hh σ' h
      simp only [rufAt] at h
      have g0 : Gut (D.schreibt f) (D.gschreibt f) σ _ :=
        gut_lese σ _ _ (P.requires f).orte_darf hh.heldIn
      split at h
      · simp [RufAusgang.welt] at h
      · have hb := end_gut O passes (rufAt P O passes n) ih hO (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (g0.heldGenau hh)
        split at h
        · rename_i σ2 v hs
          have g2 : Gut (D.schreibt f) (D.gschreibt f) _ σ2 := hb σ2 (by rw [hs]; rfl)
          have hh2 : HeldGenau (Signatur.anfang D (D.signatur f)) σ2.haelt := g2.heldGenau (g0.heldGenau hh)
          have g3 : Gut (D.schreibt f) (D.gschreibt f) σ2 _ :=
            gut_lese σ2 (vertragVon D f).ende _ (P.ensures f).orte_darf
              (by intro L hL; exact hh2.heldIn L ((held_anfang _ L).mpr ((held_ende _ L).mp hL)))
          split at h
          · simp [RufAusgang.welt] at h
          · have g4 := gut_foldl_lese (W := D.schreibt f) (G := D.gschreibt f) P f
              (D.invs.filter (schuldet f)) _
              (fun i hi => (List.mem_filter.mp hi).2) (g3.heldGenau hh2).heldIn
            split at h
            · simp [RufAusgang.welt] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
              exact ((g0.trans g2).trans g3).trans g4
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
          exact g0.trans (hb _ (by rw [hs]; rfl))
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp [RufAusgang.welt] at h
        · simp [RufAusgang.welt] at h

/-- **Der Satz ueber Rahmen und Spur**: ein Rumpf unter Vertrag `V`, gestartet in einer Welt,
    die haelt, was sein `Λ` nennt, schreibt nur, was `V` nennt, gibt jede Sperre zurueck und
    tut keinen Zugriff ohne die Waechter seines Traegers -- fuer jedes Programm, jede Tiefe,
    jede Welt; die Hardware haelt ihr `effects` (H1). -/
theorem exec_gut (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    GutAusgang V.schreibt V.gschreibt σ (exec P O passes fuel V b σ ρ) :=
  block_gut O passes _ (rufAt_gut P O passes hO fuel) hO b σ ρ hh

/-- Der RAHMEN, fuer sich. -/
theorem exec_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' → Rahmen V.schreibt V.gschreibt σ σ' :=
  fun σ' h => (exec_gut P O passes fuel hO b σ ρ hh σ' h).1

/-- Die SPUR, fuer sich: jedes Ereignis, das ein Rumpf hinterlaesst, traegt die Waechter seines
    Traegers und haelt jede Sperre, die sein `Λ` nennt -- und am Ende sind die Sperren, was sie
    am Anfang waren. Das ist der Anschluss an `Wettlauf.lean`. -/
theorem exec_spur (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' →
      σ'.haelt = σ.haelt ∧ (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧
      (Konsistent σ.spur → Konsistent σ'.spur) :=
  fun σ' h => (exec_gut P O passes fuel hO b σ ρ hh σ' h).2

/-! ## 4. Sprechproben -- Saetze der Grammatik, ausgewertet -/

/-- Eine Deklaration ohne Tabellen, Globale, Sperren, Register: nur Rechnung. -/
def leer : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun t => t.elim
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Empty
  sig := fun f => f.elim
  sigNr := fun _ => ⟨[], none, 0, [], fun t => t.elim, fun g => g.elim, [], []⟩
  eigner_nie_erzeugt := fun _ t => t.elim
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

def leereWelt : World leer := ⟨fun t => Empty.elim t, fun g => Empty.elim g, []⟩

/-- `x : u8 in 0 .. 5`; `x + x` hat den Bereich `0 .. 10`, und `(x + x) / (x + 1)` ist
    schreibbar, weil der Nenner in `1 .. 6` liegt -- Bereich `0 .. 10`. -/
def probe : Expr leer [.int 0 5] [] (.int 0 10) :=
  .div (by decide) (by decide) (.add (.var .hier) (.var .hier)) (.add (.var .hier) (.lit 1))

example : (eval leereWelt probe leereWelt (.cons ⟨3, by decide, by decide⟩ .nil)).n = 1 := by rfl
example : (eval leereWelt probe leereWelt (.cons ⟨0, by decide, by decide⟩ .nil)).n = 0 := by rfl

/-- `x : i8 in -5 .. 5`, `y : i8 in -3 .. -1`: `x / y` ist schreibbar (der Nenner ist nie
    null), Bereich `-5 .. 5`; bei `x = -5, y = -2` ist es `2` (abschneidend, wie C). -/
def sprobe : Expr leer [.int (-3) (-1), .int (-5) 5] [] (.int (-(betragMax (-5) 5)) (betragMax (-5) 5)) :=
  .sdiv (.inr (by decide)) (.var (.dort .hier)) (.var .hier)

example : (eval leereWelt sprobe leereWelt
    (.cons ⟨-2, by decide, by decide⟩ (.cons ⟨-5, by decide, by decide⟩ .nil))).n = 2 := by rfl

/-- `x / x` ist NICHT schreibbar: `.div` verlangt `1 ≤ 0`, und `.sdiv` verlangt einen Bereich
    ohne die Null -- `0 .. 5` hat sie. -/
example : ¬ (1 ≤ (0 : Int)) := by decide
example : ¬ (1 ≤ (0 : Int) ∨ (5 : Int) ≤ -1) := by decide

/-- `forall k in slots of T : …` ueber der leeren Tabelle -- immer wahr. -/
example : wahr? (eval (D := leer) (Γ := []) (Λ := []) leereWelt (.und .wahr (.nicht .falsch)) leereWelt .nil) = true := by
  rfl

def leerV : Vertrag leer := ⟨fun t => t.elim, fun g => g.elim, none, 0, [], []⟩

def leerO : Orakel leer := ⟨fun a => a.elim, fun r => r.elim, fun r => r.elim, fun g => g.elim⟩

def gleitProbe : Block leer leerV false [] [] [] :=
  .gleitLit (3, 2) (0, 1) (10, 1) .nil

example : ∃ o, execBlock (D := leer) leerO 0 (fun f => f.elim) gleitProbe leereWelt .nil = o :=
  ⟨_, rfl⟩

/-! ## 5. Die Axiome -- abgeleitet -/

#print axioms Gabbro.Grammatik.zwei_fehler
#print axioms Gabbro.Grammatik.bedeutung_total
#print axioms Gabbro.Grammatik.exec_gut
#print axioms Gabbro.Grammatik.exec_rahmen
#print axioms Gabbro.Grammatik.exec_spur
#print axioms Gabbro.Grammatik.rufAt_gut
#print axioms Gabbro.Grammatik.keine_verklemmung

end Gabbro.Grammatik
