module

public import Passlogik.Kosten.Teil1

@[expose] public section

namespace Passlogik.Kosten
variable {F : Type u}

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
-- SYMBOLISCHEN `held` -- `K010` verlangt `constexpr`, und `LANGUAGE.md`:1282 sagt warum:
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
  | nil => simp only [List.map_nil, List.sum_nil, summe_held, Std.le_refl]
  | cons L rest ih =>
      have h1 : kosten L ≤ L.held := h L (List.mem_cons_self ..)
      have h2 := ih (fun M hm => h M (List.mem_cons_of_mem _ hm))
      simp only [List.map_cons, List.sum_cons, summe_held]
      omega


#print axioms Passlogik.Kosten.wartezeit_ist_summe
/-! ## 8. Die Schleifenschranke multipliziert

    `LANGUAGE.md`:940: "a traversal counts body costs x domain bound". Der Satz steckt
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
