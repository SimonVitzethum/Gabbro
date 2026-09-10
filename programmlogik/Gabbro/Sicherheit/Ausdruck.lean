/-
  Datei:      Gabbro/Sicherheit/Ausdruck.lean
  Gegenstand: **Der Sicherheitssatz fuer AUSDRUECKE** -- ein Ausdruck, den der Pruefer
              annimmt, wird in `Body.lean`s Semantik NIE `none`, und sein Wert hat die
              Gestalt, die der Pruefer ihm gerechnet hat.

  Angelegt 2026-09-09. **Die Frage, die dieser Ordner beantworten soll:**

  > Deckt die Grammatik samt ihren Paessen JEDEN Fehler ab, so dass der einzige Fehler,
  > den ein angenommenes Gabbro-Programm noch haben kann, die Logik des Schreibers ist?

  `Coverage.lean` beantwortet sie als KLASSIFIKATION: jede Form bekommt ein Urteil.
  Was dort NICHT steht, ist der SEMANTISCHE Satz -- dass ein angenommenes Programm im
  Modell an keiner Stelle stecken bleibt, die nicht `requires` oder `invariant` heisst.
  `Body.lean` hat den Begriff dafuer (`Outcome.stuck`, `eval … = none`), aber keinen
  Satz, der ihn fuer angenommene Programme AUSSCHLIESST. **Das ist der Satz, der hier
  anfaengt.** Er hat zwei Haelften; diese Datei ist die erste (Ausdruecke), die zweite
  steht in `Anweisung.lean`.

  WAS MODELLIERT WIRD
    Ein PRUEFER als Algorithmus, nicht als Relation: `schluss` rechnet zu einem Ausdruck
    die Gestalt (`Shape`) aus, die er tragen wird -- oder `none`, und `none` ist die
    ABSAGE des Pruefers. Er rechnet so, wie `SPRACHE.md` §3 M1 es sagt: Bereiche werden
    durch die Arithmetik getragen (`M104`), ein Nenner muss die Null ausschliessen
    (`M102`), ein Index muss in `0 ..< count` liegen (`M103`), ein `match` findet nur
    Faelle, die der Typ erklaert (`D005`).

    Der Satz `schluss_sicher` sagt dann: liegt die Welt in ihrer Typisierung (`WF`) und
    liegen die Lokalen in ihrer (`WFL`), so liefert `eval` einen Wert dieser Gestalt.
    **Kein `none`** -- also keine Division durch null, kein Bitoperator auf einer
    negativen Zahl, keine Gestaltverwechslung, kein Index ausserhalb.

  QUELLSAETZE
    dokumente/SPRACHE.md:677   -- "Every operation must stay inside the range of its
                                  result type; […] compile error, not a runtime check.
                                  Division and remainder demand a denominator whose range
                                  excludes zero."
    dokumente/SYNTAX.md:715    -- "M1 acts here and nowhere else"
    dokumente/SYNTAX.md:719    -- "`%` and `/` by `u32 in 0..n` are not writable"
    dokumente/SYNTAX.md:1027   -- "`match` is exhaustive -- there is no catch-all branch"
    programmlogik/Gabbro/Body.lean, `binop`  -- "A zero denominator gets the model STUCK",
                                  "A bit mask, over the NON-NEGATIVE integers and nowhere else"
    passlogik/Passlogik/Bereich.lean -- `add_korrekt`, `sub_korrekt`, `mul_korrekt`: die
                                  Ueberdeckung, hier NEU bewiesen, weil die beiden
                                  Lake-Projekte einander nicht importieren.

  ANGENOMMEN STATT BEWIESEN
    (S1) Die Typisierung der Welt ist je Traeger und Feld EINHEITLICH im Index:
         `Γ (.slot c k f) = Σ c f` fuer jedes `k` in `0 ..< count c`. So schreibt der
         Erzeuger `Γ` aus den Deklarationen; hier ist es die Praemisse `Deklariert`.
    (S2) Fuer `reaches`/`chain` muss das `via`-Feld an JEDEM Index eine Option tragen,
         nicht nur in `0 ..< count` -- `chase` folgt einem `present m` ohne
         Schranke. **Das ist ein FUND, kein Modellfehler:** `Shape.opt` traegt keinen
         Bereich, also ist `option index into T` im Modell ein Zeiger ohne Schranke.
         Siehe `Sicherheit.lean`, Fund 2.
    (S3) `wrapTo` liefert `.int` ohne Bereich. Dass `wrap b sg n` in `[0, 2^b)` bzw.
         `[-2^(b-1), 2^(b-1))` liegt, ist ein zweiter Satz und steht hier nicht.
    (S4) Division, Rest, Schiebe- und Bitoperationen liefern `.int` ohne Bereich. Der
         Pruefer (`typen.rs`) rechnet dort Schranken; hier steht nur, dass sie NICHT
         STECKEN BLEIBEN. Die Schranken sind der naechste Satz (`Sicherheit.lean`, §3).
-/
import Gabbro.Body

namespace Gabbro.Sicherheit

open Gabbro.Body

/-! ## 0. Intervalle -- das Stueck `Bereich.lean`, das hier gebraucht wird -/

def imin (a b : Int) : Int := if a ≤ b then a else b
def imax (a b : Int) : Int := if a ≤ b then b else a

theorem imin_le_left (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
theorem le_imax_left (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
theorem le_imax_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega

/-- Das Vier-Ecken-Produkt -- `mul_korrekt` aus `Bereich.lean`, hier als Hilfssatz. -/
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

/-! ## 1. Die Typisierung der LOKALEN, neben der der Welt aus `Body.lean` -/

/-- Die Gestalt jedes lokalen Namens -- was `let` und die Parameter erklaert haben.
    `none` heisst: der Name traegt keine Gestalt, und der Pruefer liest ihn dann nicht. -/
abbrev Lokal := String → Option Shape

/-- Die Lokalen liegen in ihrer Typisierung -- das Gegenstueck zu `WF` fuer `local'`. -/
def WFL (Δ : Lokal) (β : Binding) : Prop :=
  ∀ n sh, Δ n = some sh → (β n).hasShape sh = true

/-- Die Gestalt je Traeger und SLOTFELD, einheitlich im Index (S1), und je Traeger die
    `count`-Schranke. So steht es in der Deklaration; `Γ` ist daraus abgeleitet. -/
structure Deklaration where
  slot   : String → String → Option Shape
  count  : String → Int
  /-- Felder eines Verbunds oder `format` (`.field c f`). -/
  feld   : String → String → Option Shape
  /-- `static`s und `atomic`s (`.global g`). -/
  global : String → Option Shape

/-- **(S1)** `Γ` IST die Deklaration: an jedem Index innerhalb der Schranke traegt das
    Slotfeld die erklaerte Gestalt; Feld und Global ebenso. -/
def Deklariert (D : Deklaration) (Γ : Typing) : Prop :=
  (∀ c k f, 0 ≤ k → k < D.count c → Γ (.slot c k f) = D.slot c f)
  ∧ (∀ c f, Γ (.field c f) = D.feld c f)
  ∧ (∀ g, Γ (.global g) = D.global g)

/-! ## 2. Der Pruefer als ALGORITHMUS -- was M1 an einem Ausdruck rechnet

    `schluss` gibt `none` zurueck, wo der Pruefer ABSAGT. Jede Absage traegt in der
    Bemerkung daneben die Kennung des Passes, die sie in `gabbro-check` traegt. -/

/-- Ist die Gestalt eine Zahl -- und mit welchem Bereich? `.int` ist die Zahl ohne
    erklaerten Bereich (`u64` ohne `in`, Ergebnis einer Division, …). -/
def zahl : Shape → Option (Option (Int × Int))
  | .int => some none
  | .intIn lo hi => some (some (lo, hi))
  | _ => none

/-- Der Bereich einer Zahlgestalt, wo einer steht. -/
def bereich : Shape → Option (Int × Int)
  | .intIn lo hi => some (lo, hi)
  | _ => none

/-- Die Arithmetik des Passes ueber zwei Zahlgestalten: mit Bereich, wenn beide einen
    tragen (`M104` rechnet dann das Ergebnisintervall), sonst `.int`. -/
def arith (op : BinOp) (a b : Shape) : Option Shape :=
  match zahl a, zahl b with
  | some (some (lo1, hi1)), some (some (lo2, hi2)) =>
      match op with
      | .add => some (.intIn (lo1 + lo2) (hi1 + hi2))
      | .sub => some (.intIn (lo1 - hi2) (hi1 - lo2))
      | .mul => some (.intIn (imin (imin (lo1*lo2) (lo1*hi2)) (imin (hi1*lo2) (hi1*hi2)))
                             (imax (imax (lo1*lo2) (lo1*hi2)) (imax (hi1*lo2) (hi1*hi2))))
      -- `M102`: der Nenner schliesst die Null aus, oder der Pass sagt ab.
      | .div | .rem => if 0 < lo2 ∨ hi2 < 0 then some .int else none
      -- `M137`/`M104`: Bitoperatoren und Schiebungen nur ueber NICHTNEGATIVEN Bereichen.
      | .band | .bor | .bxor | .shl | .shr => if 0 ≤ lo1 ∧ 0 ≤ lo2 then some .int else none
      | _ => none
  -- Ohne Bereich auf einer Seite: Addition und Co. bleiben Zahlen; Division, Rest und
  -- Bits brauchen einen Bereich, sonst weiss der Pass nichts ueber den Nenner (`M102`).
  | some _, some _ =>
      match op with
      | .add | .sub | .mul => some .int
      | _ => none
  | _, _ => none

/-- Der Vergleich: Zahlen liefern `bool`; `==`/`!=` stehen ueber ALLEN Werten. -/
def vergleich (op : BinOp) (a b : Shape) : Option Shape :=
  match op with
  | .eq | .ne => some .bool
  | .lt | .le | .gt | .ge => match zahl a, zahl b with
      | some _, some _ => some .bool
      | _, _ => none
  | .and | .or => match a, b with
      | .bool, .bool => some .bool
      | _, _ => none
  | _ => none

/-- Ein `tagged`-Fall, den der Typ erklaert, mit einer Nutzlast, die passt (`D005`, `M106`). -/
def fallPasst (cases : List (String × Option (Option (Int × Int)))) (t : String)
    (nutz : Option Shape) : Bool :=
  cases.any fun c =>
    c.1 == t &&
    match c.2, nutz with
    | none, none => true
    | some none, some sh => (zahl sh).isSome
    | some (some (lo, hi)), some (.intIn lo' hi') => decide (lo ≤ lo' ∧ hi' ≤ hi)
    | _, _ => false

/-- **Der Pruefer.** `schluss D Δ e = some sh`: der Pass nimmt `e` an und gibt ihm die
    Gestalt `sh`; `none` ist die Absage. -/
def schluss (D : Deklaration) : Lokal → Expr → Option Shape
  | _, .lit v =>
      -- Ein Literal traegt seine eigene Gestalt: eine Zahl den Punktbereich `[n, n]`.
      match v with
      | .int n => some (.intIn n n)
      | .bool _ => some .bool
      | .absent => some .opt
      | .present _ => some .opt
      | .reason _ => none
      | .tagged _ _ => none
  | Δ, .name n => Δ n
  | _, .global g => D.global g
  | Δ, .place c i f =>
      -- `M103`: der Index liegt in `0 ..< count`, oder der Pass sagt ab.
      match schluss D Δ i with
      | some (.intIn lo hi) => if 0 ≤ lo ∧ hi < D.count c then D.slot c f else none
      | _ => none
  | _, .fieldOf c f => D.feld c f
  | Δ, .un .not a =>
      match schluss D Δ a with
      | some .bool => some .bool
      | _ => none
  | Δ, .un .neg a =>
      match schluss D Δ a with
      | some .int => some .int
      | some (.intIn lo hi) => some (.intIn (-hi) (-lo))
      | _ => none
  | Δ, .bin op a b =>
      match schluss D Δ a, schluss D Δ b with
      | some sa, some sb =>
          match arith op sa sb with
          | some sh => some sh
          | none => vergleich op sa sb
      | _, _ => none
  | Δ, .someOf a =>
      match schluss D Δ a with
      | some sh => if (zahl sh).isSome then some .opt else none
      | none => none
  | Δ, .forallSlots v n b =>
      -- Der Binder traegt den Indexbereich der Domaene (`slots of`: `0 ..< count`).
      match schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b with
      | some .bool => some .bool
      | _ => none
  | Δ, .existsSlots v n b =>
      match schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b with
      | some .bool => some .bool
      | _ => none
  | Δ, .reaches c a z via _ =>
      -- (S2): das `via`-Feld ist an jedem Index eine Option, sonst Absage.
      match schluss D Δ a, schluss D Δ z, D.slot c via with
      | some sa, some sz, some .opt => if (zahl sa).isSome ∧ (zahl sz).isSome then some .bool else none
      | _, _, _ => none
  | Δ, .chainFrom c h x via _ =>
      match schluss D Δ h, schluss D Δ x, D.slot c via with
      | some .opt, some sx, some .opt => if (zahl sx).isSome then some .bool else none
      | _, _, _ => none
  | _, .hasShape _ _ => some .bool
  | Δ, .wrapTo _ _ a =>
      match schluss D Δ a with
      | some sh => if (zahl sh).isSome then some .int else none
      | none => none
  | _, .tagOf _ none => none
  | _, .tagOf _ (some _) => none
  -- **Ein `tagged`-Wert ohne Zieltyp hat keine Gestalt** -- `Coverage.lean` nennt die
  -- Form `constructedValue` und sagt sie ab; der Pruefer kennt den Typ nur aus dem ZIEL
  -- (`M106`), und ein Ausdruck allein hat keines. Hier ebenso: `none`. Die Ableitung
  -- gegen ein Ziel steht in `Anweisung.lean` (`fallPasst`).

/-! ## 3. Der Satz -- ein angenommener Ausdruck wird nie `none`, und sein Wert passt -/

/-- **(S2) als Praemisse:** das `via`-Feld ist an JEDEM Index option-gestaltig. -/
def KettenWohlgeformt (D : Deklaration) (σ : World) : Prop :=
  ∀ c via k, D.slot c via = some .opt → (σ (.slot c k via)).hasShape .opt = true

theorem zahl_some_int {sh : Shape} {v : Value} (hz : (zahl sh).isSome = true)
    (hv : v.hasShape sh = true) : ∃ n, v = .int n := by
  cases sh <;> simp [zahl] at hz
  · exact Value.hasShape_int_true v hv
  · obtain ⟨n, hn, _⟩ := Value.hasShape_intIn_true v _ _ hv; exact ⟨n, hn⟩

theorem zahl_some_of_zahl {sh : Shape} {r : Option (Int × Int)} (h : zahl sh = some r) :
    (zahl sh).isSome = true := by rw [h]; rfl

theorem bereich_of_zahl {sh : Shape} {lo hi : Int} (h : zahl sh = some (some (lo, hi))) :
    sh = .intIn lo hi := by
  cases sh <;> simp [zahl] at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

theorem int_of_zahl_none {sh : Shape} (h : zahl sh = some none) : sh = .int := by
  cases sh <;> simp [zahl] at h; rfl

/-- `allBelow` ueber einer Funktion, die immer einen `bool` liefert, liefert einen `bool`. -/
theorem allBelow_bool (f : Nat → Option Value) :
    ∀ n, (∀ k, k < n → ∃ b, f k = some (.bool b)) → ∃ b, allBelow f n = some (.bool b) := by
  intro n
  rw [allBelow_eq]
  induction n with
  | zero => intro _; exact ⟨true, rfl⟩
  | succ n ih =>
      intro hf
      obtain ⟨a, ha⟩ := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨b, hb⟩ := hf n (Nat.lt_succ_self n)
      exact ⟨a && b, by simp [allBelowImpl, ha, hb]⟩

theorem anyBelow_bool (f : Nat → Option Value) :
    ∀ n, (∀ k, k < n → ∃ b, f k = some (.bool b)) → ∃ b, anyBelow f n = some (.bool b) := by
  intro n
  rw [anyBelow_eq]
  induction n with
  | zero => intro _; exact ⟨false, rfl⟩
  | succ n ih =>
      intro hf
      obtain ⟨a, ha⟩ := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨b, hb⟩ := hf n (Nat.lt_succ_self n)
      exact ⟨a || b, by simp [anyBelowImpl, ha, hb]⟩

/-- `chase` ueber wohlgeformten Ketten liefert einen `bool` -- mit jedem Treibstoff. -/
theorem chase_bool (σ : World) (c via : String) (to : Int)
    (hk : ∀ k, (σ (.slot c k via)).hasShape .opt = true) :
    ∀ n k, ∃ b, chase σ c via to k n = some (.bool b) := by
  intro n
  rw [chase_eq]
  induction n with
  | zero => intro k; exact ⟨_, rfl⟩
  | succ n ih =>
      intro k
      simp only [chaseImpl]
      split
      · exact ⟨true, rfl⟩
      · rcases Value.hasShape_opt_true _ (hk k) with h | ⟨m, h⟩
        · rw [h]; exact ⟨false, rfl⟩
        · rw [h]; exact ih m

/-- **Der Rumpf eines Quantors**: unter dem Binder mit dem Indexbereich `0 ..< n` liefert
    er fuer jeden GERUFENEN Index einen `bool`. Herausgezogen, weil `forall` und `exists`
    denselben Schritt brauchen. -/
theorem quant_rumpf (D : Deklaration) (Γ : Typing) {b : Expr}
    (ih : ∀ (Δ : Lokal) (s : State) (sh : Shape), WF Γ s.world → WFL Δ s.local' →
        KettenWohlgeformt D s.world → schluss D Δ b = some sh →
        ∃ v, eval s b = some v ∧ v.hasShape sh = true)
    (Δ : Lokal) (s : State) (n : Int) {v : String}
    (hw : WF Γ s.world) (hl : WFL Δ s.local') (hk : KettenWohlgeformt D s.world)
    (hb : schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b = some .bool) :
    ∀ k : Nat, k < n.toNat →
      ∃ t, eval { s with local' := bindLocal s.local' v (.int k) } b = some (.bool t) := by
  intro k hkn
  have hl' : WFL (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m)
      (bindLocal s.local' v (.int k)) := by
    intro m sh hm
    by_cases hmv : m = v
    · subst hmv; simp at hm; subst hm
      simp [Value.hasShape]
      omega
    · simp [hmv] at hm; simpa [bindLocal, hmv] using hl m sh hm
  obtain ⟨t, ht, hts⟩ := ih _ ⟨s.world, bindLocal s.local' v (.int k)⟩ _ hw hl' hk hb
  obtain ⟨tb, rfl⟩ := Value.hasShape_bool_true t hts
  exact ⟨tb, ht⟩

/-- Der Sicherheitssatz fuer Ausdruecke. **BEWEIST NICHT**, dass der Pruefer in
    `gabbro-check` dasselbe rechnet wie `schluss` -- das ist die Naht (`W16`), und sie
    steht in keiner Zeile hier. Er beweist: WENN ein Pruefer so rechnet, DANN bleibt kein
    angenommener Ausdruck stecken. -/
theorem schluss_sicher (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ) :
    ∀ (e : Expr) (Δ : Lokal) (s : State) (sh : Shape),
      WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world →
      schluss D Δ e = some sh →
      ∃ v, eval s e = some v ∧ v.hasShape sh = true
  | .lit v, Δ, s, sh => by
      intro _ _ _ h
      cases v <;> simp [schluss] at h <;> subst h
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
      · exact ⟨_, rfl, by simp [Value.hasShape]⟩
  | .name n, Δ, s, sh => by
      intro _ hl _ h
      exact ⟨_, rfl, hl n sh h⟩
  | .global g, Δ, s, sh => by
      intro hw _ _ h
      refine ⟨_, rfl, hw _ sh ?_⟩
      rw [hD.2.2 g]; exact h
  | .place c i f, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD i
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i lo hi hi'
        split at h
        · rename_i hb
          obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk hi'
          obtain ⟨k, hk', hlo, hhi⟩ := Value.hasShape_intIn_true v lo hi hvs
          subst hk'
          refine ⟨_, ?_, hw (.slot c k f) sh ?_⟩
          · simp [eval, hv]
          · rw [hD.1 c k f (by omega) (by omega)]; exact h
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .fieldOf c f, Δ, s, sh => by
      intro hw _ _ h
      refine ⟨_, rfl, hw _ sh ?_⟩
      rw [hD.2.1 c f]; exact h
  | .un op a, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD a
      intro hw hl hk h
      cases op with
      | not =>
          simp only [schluss] at h
          split at h
          · rename_i ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
            cases h
            simp [eval, hv, unop, Value.hasShape]
          · exact absurd h (by simp)
      | neg =>
          simp only [schluss] at h
          split at h
          · rename_i ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨n, rfl⟩ := Value.hasShape_int_true v hvs
            cases h
            simp [eval, hv, unop, Value.hasShape]
          · rename_i lo hi ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v lo hi hvs
            cases h
            simp [eval, hv, unop, Value.hasShape]; omega
          · exact absurd h (by simp)
  | .bin op a b, Δ, s, sh => by
      have iha := schluss_sicher D Γ hD a
      have ihb := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa sb ha hb
        obtain ⟨va, hva, hvas⟩ := iha Δ s _ hw hl hk ha
        obtain ⟨vb, hvb, hvbs⟩ := ihb Δ s _ hw hl hk hb
        -- Zwei Faelle: Arithmetik oder Vergleich.
        split at h
        · -- Arithmetik
          rename_i sh' harith
          cases h
          unfold arith at harith
          split at harith
          · -- beide mit Bereich: `M104` rechnet das Intervall
            rename_i lo1 hi1 lo2 hi2 hz1 hz2
            have ea := bereich_of_zahl hz1; have eb := bereich_of_zahl hz2
            subst ea; subst eb
            obtain ⟨x, rfl, hx1, hx2⟩ := Value.hasShape_intIn_true va lo1 hi1 hvas
            obtain ⟨y, rfl, hy1, hy2⟩ := Value.hasShape_intIn_true vb lo2 hi2 hvbs
            cases op with
            | add => cases harith; simp [eval, hva, hvb, binop, Value.hasShape]; omega
            | sub => cases harith; simp [eval, hva, hvb, binop, Value.hasShape]; omega
            | mul =>
                cases harith
                simp only [eval, hva, hvb, binop, Value.hasShape, Option.some.injEq,
                  exists_eq_left', decide_eq_true_eq]
                exact produkt_in_ecken lo1 hi1 lo2 hi2 x y hx1 hx2 hy1 hy2
            | div =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  have hy : y ≠ 0 := by omega
                  simp [eval, hva, hvb, binop, hy, Value.hasShape]
                · cases harith
            | rem =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  have hy : y ≠ 0 := by omega
                  simp [eval, hva, hvb, binop, hy, Value.hasShape]
                · cases harith
            | band =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  simp [eval, hva, hvb, binop, bits, show 0 ≤ x by omega, show 0 ≤ y by omega,
                    Value.hasShape]
                · cases harith
            | bor =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  simp [eval, hva, hvb, binop, bits, show 0 ≤ x by omega, show 0 ≤ y by omega,
                    Value.hasShape]
                · cases harith
            | bxor =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  simp [eval, hva, hvb, binop, bits, show 0 ≤ x by omega, show 0 ≤ y by omega,
                    Value.hasShape]
                · cases harith
            | shl =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  simp [eval, hva, hvb, binop, show 0 ≤ x by omega, show 0 ≤ y by omega,
                    Value.hasShape]
                · cases harith
            | shr =>
                dsimp only at harith
                split at harith
                · rename_i hc; cases harith
                  simp [eval, hva, hvb, binop, show 0 ≤ x by omega, show 0 ≤ y by omega,
                    Value.hasShape]
                · cases harith
            | eq => cases harith
            | ne => cases harith
            | lt => cases harith
            | le => cases harith
            | gt => cases harith
            | ge => cases harith
            | and => cases harith
            | or => cases harith
          · -- eine Seite ohne Bereich: nur `+`, `-`, `*` bleiben Zahlen
            rename_i hz1 hz2
            obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
            obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
            cases op <;> cases harith
            all_goals simp [eval, hva, hvb, binop, Value.hasShape]
          · cases harith
        · -- Vergleich
          rename_i harith
          unfold vergleich at h
          cases op with
          | eq => cases h; simp [eval, hva, hvb, binop, Value.hasShape]
          | ne => cases h; simp [eval, hva, hvb, binop, Value.hasShape]
          | lt =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | le =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | gt =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | ge =>
              dsimp only at h
              split at h
              · rename_i hz1 hz2; cases h
                obtain ⟨x, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz1) hvas
                obtain ⟨y, rfl⟩ := zahl_some_int (zahl_some_of_zahl hz2) hvbs
                simp [eval, hva, hvb, binop, Value.hasShape]
              · cases h
          | and =>
              dsimp only at h
              split at h
              · cases h
                obtain ⟨x, rfl⟩ := Value.hasShape_bool_true va hvas
                obtain ⟨y, rfl⟩ := Value.hasShape_bool_true vb hvbs
                simp [eval, hva, hvb, andBool, Value.hasShape]
              · cases h
          | or =>
              dsimp only at h
              split at h
              · cases h
                obtain ⟨x, rfl⟩ := Value.hasShape_bool_true va hvas
                obtain ⟨y, rfl⟩ := Value.hasShape_bool_true vb hvbs
                simp [eval, hva, hvb, orBool, Value.hasShape]
              · cases h
          | add => cases h
          | sub => cases h
          | mul => cases h
          | div => cases h
          | rem => cases h
          | band => cases h
          | bor => cases h
          | bxor => cases h
          | shl => cases h
          | shr => cases h
      · cases h
  | .someOf a, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD a
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa ha
        split at h
        · rename_i hz
          cases h
          obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
          obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
          simp [eval, hv, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .forallSlots v n b, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨t, ht⟩ := allBelow_bool _ n.toNat (quant_rumpf D Γ ih Δ s n hw hl hk hb)
        simp [eval, ht, Value.hasShape]
      · exact absurd h (by simp)
  | .existsSlots v n b, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD b
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i hb
        cases h
        obtain ⟨t, ht⟩ := anyBelow_bool _ n.toNat (quant_rumpf D Γ ih Δ s n hw hl hk hb)
        simp [eval, ht, Value.hasShape]
      · exact absurd h (by simp)
  | .reaches c a z via cnt, Δ, s, sh => by
      have iha := schluss_sicher D Γ hD a
      have ihz := schluss_sicher D Γ hD z
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa sz ha hz hvia
        split at h
        · rename_i hzz
          cases h
          obtain ⟨va, hva, hvas⟩ := iha Δ s _ hw hl hk ha
          obtain ⟨vz, hvz, hvzs⟩ := ihz Δ s _ hw hl hk hz
          obtain ⟨k, rfl⟩ := zahl_some_int hzz.1 hvas
          obtain ⟨t, rfl⟩ := zahl_some_int hzz.2 hvzs
          obtain ⟨b, hb⟩ := chase_bool s.world c via t (fun k => hk c via k hvia) cnt.toNat k
          simp [eval, hva, hvz, hb, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .chainFrom c hd x via cnt, Δ, s, sh => by
      have ihh := schluss_sicher D Γ hD hd
      have ihx := schluss_sicher D Γ hD x
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sx hh hx hvia
        split at h
        · rename_i hzz
          cases h
          obtain ⟨vh, hvh, hvhs⟩ := ihh Δ s _ hw hl hk hh
          obtain ⟨vx, hvx, hvxs⟩ := ihx Δ s _ hw hl hk hx
          obtain ⟨t, rfl⟩ := zahl_some_int hzz hvxs
          rcases Value.hasShape_opt_true vh hvhs with rfl | ⟨m, rfl⟩
          · simp [eval, hvh, hvx, Value.hasShape]
          · obtain ⟨b, hb⟩ := chase_bool s.world c via t (fun k => hk c via k hvia) cnt.toNat m
            simp [eval, hvh, hvx, hb, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .hasShape n sh', Δ, s, sh => by
      intro _ _ _ h
      simp only [schluss] at h; cases h
      exact ⟨_, rfl, by simp [Value.hasShape]⟩
  | .wrapTo b sg a, Δ, s, sh => by
      have ih := schluss_sicher D Γ hD a
      intro hw hl hk h
      simp only [schluss] at h
      split at h
      · rename_i sa ha
        split at h
        · rename_i hz
          cases h
          obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
          obtain ⟨n, rfl⟩ := zahl_some_int hz hvs
          simp [eval, hv, Value.hasShape]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .tagOf t p, Δ, s, sh => by
      intro _ _ _ h
      cases p <;> simp [schluss] at h

end Gabbro.Sicherheit
