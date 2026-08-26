/-
  Datei:      Passlogik/Wirkung.lean
  Gegenstand: Die WIRKUNGSHUELLE ueber dem Aufrufgraphen und die LOKALE TEILMENGENREGEL.

  MODELLIERT WIRD
    Ein Rufgraph mit je Funktion einer deklarierten Wirkungsmenge (`effects { … }`), der
    eigenen Wirkung des Rumpfes, und die semantische Wirkung als transitive Vereinigung
    laengs des Graphen. Der Satz: die LOKALE Kantenbedingung `E008` traegt die GLOBALE
    Aussage -- ohne Fixpunktrechnung.

  QUELLSAETZE
    dokumente/SPRACHE.md:930  -- `effects` in `fndecl`, PFLICHT ausser bei `spec fn`
    dokumente/SPRACHE.md:937  -- "`effects` is obligatory and not fail-open; whoever
                                 touches nothing writes `effects { pure }`, and that is
                                 checked."
    dokumente/SYNTAX.md:743   -- `efflist = eff { "," eff }`,
                                 `eff = "reads" place | "writes" place | "locks" [shared]
                                  place | "masks" ident | "allocs" ident |
                                  "consumes" place | "publishes" place | "diverges" |
                                  "pure"`
    gabbro paesse --je-satz   -- Satz `wirkungen.abschluss`:
        HOLDS: "The declared `effects` of a function are closed over its call hull: every
        effect a reachable callee has has a counterpart in the caller's list. **This holds
        whether the hull is complete or not** -- the hull is a LOWER bound, so everything
        IN it really happens and demanding that it be declared is sound regardless of what
        is missing."
    gabbro paesse --je-satz   -- Satz `wirkungen.rahmen` (E005/E010/E011),
                                 Satz `wirkungen.pflicht` (E001-E004)
    messung/PASSREGISTER.md:  -- der Fund vom 2026-08-24: "Am Zyklus wurde `E009` gesetzt
                                 und VOR JEDER `E008`-Pruefung zurueckgekehrt; eine
                                 unaufloesbare Kante tief unten entwertete `E008` fuer die
                                 ganze Rufkette."

  ANGENOMMEN STATT BEWIESEN
    (B1) `eigen f` -- was der Rumpf von `f` SELBST tut -- wird als gegeben genommen. Dass
         `wirkungen.rs` diese Menge richtig aus dem Rumpf abliest, ist eine Aussage ueber
         den Anweisungsabstieg. Das Passregister nennt dort mehrere Luecken (`let … else`,
         das `until`-Praedikat, den Gegenstand eines `traverse`), und der Anweisungsabstieg
         ist genau die Klasse W16. **Er steht hier nicht.**
    (B2) Fuer eine `extern fn` gibt es KEINE Rumpfpruefung. Ihre deklarierten Wirkungen
         gehen als Wahrheit in jeden Rufer ein. Das ist eine ANNAHME, und §6 macht sie
         sichtbar statt sie wegzulassen.
    (B3) Die Vergleichbarkeit zweier Orte (`writes c.slots` deckt `writes c.slots[3]`) ist
         hier eine gegebene Relation. §7 zeigt, was daran haengt.
-/

namespace Passlogik.Wirkung

/-! ## 1. Mengen ohne `mathlib`

    Eine Menge ist ein Praedikat. Das genuegt fuer alles unten -- **Endlichkeit wird
    nirgends gebraucht**, und das ist selbst ein Ergebnis: der Satz haengt nicht an der
    Zahl der Funktionen, sondern an der Form der Induktion.
-/

abbrev Menge (α : Type u) := α → Prop

def teilmenge {α : Type u} (A B : Menge α) : Prop := ∀ x, A x → B x

infix:50 " ⊑ " => teilmenge

theorem teilmenge_refl {α : Type u} (A : Menge α) : A ⊑ A := fun _ h => h

theorem teilmenge_trans {α : Type u} {A B C : Menge α}
    (h1 : A ⊑ B) (h2 : B ⊑ C) : A ⊑ C := fun x h => h2 x (h1 x h)

def leere {α : Type u} : Menge α := fun _ => False

theorem leere_ist_kleinste {α : Type u} (A : Menge α) : (leere : Menge α) ⊑ A :=
  fun _ h => h.elim

/-! ## 2. Die Wirkungsatome -- die Tafel aus `SYNTAX.md`:743, eins zu eins -/

/-- Ein Ort im Programm (ein `place` der Grammatik), abstrakt. -/
structure Ort where
  id : Nat
deriving DecidableEq, Repr

/-- Eine Sperre, eine Maske, ein Vorrat: benannte Dinge ohne Ortsstruktur. -/
structure Name where
  id : Nat
deriving DecidableEq, Repr

/-- **`eff` aus `SYNTAX.md`:744.** `pure` steht bewusst NICHT hier drin: `pure` ist die
    LEERE Menge, nicht ein Atom. *Das ist eine Modellentscheidung mit einer Folge -- siehe
    `pure_ist_leer` unten.* -/
inductive Wkg where
  | reads      : Ort  → Wkg
  | writes     : Ort  → Wkg
  | locks      : Name → Wkg
  | locksShared : Name → Wkg
  | masks      : Name → Wkg
  | allocs     : Name → Wkg
  | consumes   : Ort  → Wkg
  | publishes  : Ort  → Wkg
  | diverges   : Wkg
deriving DecidableEq, Repr

/-- `effects { pure }` heisst: die Menge ist leer. `SPRACHE.md`:937 -- "whoever touches
    nothing writes `effects { pure }`". -/
def pure_menge : Menge Wkg := leere

theorem pure_ist_leer : ∀ w, ¬ pure_menge w := fun _ h => h

/-! ## 3. Das Programm: ein Rufgraph mit drei Beschriftungen -/

/-- `F` ist der Typ der Funktionen. **Er ist NICHT endlich verlangt** -- der Hauptsatz
    braucht keine Endlichkeit, und das ist der Grund, warum er Zyklen vertraegt. -/
structure Programm (F : Type u) where
  /-- Die Rufkante. `ruft f g` heisst: der Rumpf von `f` ruft `g`. -/
  ruft  : F → F → Prop
  /-- Was `f` in seiner `effects`-Klausel DEKLARIERT. -/
  dekl  : F → Menge Wkg
  /-- Was der Rumpf von `f` SELBST tut, ohne die Gerufenen. (B1) -/
  eigen : F → Menge Wkg

variable {F : Type u}

/-! ## 4. Was der Pass PRUEFT -- zwei lokale Bedingungen, je eine Zeile

    Beide sind LOKAL: die erste sieht einen Rumpf, die zweite eine Kante. **Keine der
    beiden sieht den Graphen.** Genau das ist der Ertrag -- eine Fixpunktrechnung
    braeuchte man erst, wenn die deklarierten Mengen AUSGERECHNET statt GEPRUEFT wuerden.
-/

/-- **`E005`/`E010`/`E011` -- der Rahmen.** Was der Rumpf selbst tut, steht in seiner
    Liste. -/
def rahmen_haelt (P : Programm F) : Prop := ∀ f, P.eigen f ⊑ P.dekl f

/-- **`E008` -- die lokale Teilmengenregel.** Ueber jeder Rufkante gilt
    `Gerufener.deklariert ⊆ Rufer.deklariert`. -/
def kante_haelt (P : Programm F) : Prop := ∀ f g, P.ruft f g → P.dekl g ⊑ P.dekl f

/-! ## 5. Die Huelle, und der Satz

    Die Erreichbarkeit ist eine INDUKTIV erzeugte Relation. **Darin liegt der ganze
    Trick:** ein Zyklus im Graphen erzeugt keine unendliche Ableitung -- jede einzelne
    Ableitung von `erreicht f g` ist endlich, auch wenn der Graph kreist. Die Induktion
    laeuft ueber die ABLEITUNG, nicht ueber den Graphen.
-/

inductive erreicht (r : F → F → Prop) : F → F → Prop where
  | hier  (f : F) : erreicht r f f
  | ueber {f g h : F} : r f g → erreicht r g h → erreicht r f h

theorem erreicht_trans {r : F → F → Prop} {f g h : F}
    (h1 : erreicht r f g) (h2 : erreicht r g h) : erreicht r f h := by
  induction h1 with
  | hier _ => exact h2
  | ueber e _ ih => exact erreicht.ueber e (ih h2)

/-- **Die SEMANTISCHE Wirkung von `f`:** alles, was ein von `f` aus erreichbarer Rumpf
    tut. Das ist die Groesse, ueber die der Satz spricht -- nicht die deklarierte. -/
def sem (P : Programm F) (f : F) : Menge Wkg :=
  fun w => ∃ g, erreicht P.ruft f g ∧ P.eigen g w

/-- Der Kern: die lokale Kantenregel pflanzt sich laengs JEDER Ableitung fort. -/
theorem dekl_monoton {P : Programm F} (hk : kante_haelt P) {f g : F}
    (h : erreicht P.ruft f g) : P.dekl g ⊑ P.dekl f := by
  induction h with
  | hier f => exact teilmenge_refl _
  | ueber e _ ih => exact teilmenge_trans ih (hk _ _ e)

/-- ## DER SATZ

    **Erfuellt jede Rufkante `Gerufener.deklariert ⊆ Rufer.deklariert`, und deckt jede
    Liste den eigenen Rumpf, so umfasst die deklarierte Menge des Rufers die transitive
    semantische Wirkung seines Rumpfes.**

    *Das ist der Satz, der eine Fixpunktrechnung aus der Vertrauensbasis entliesse:
    geprueft werden zwei lokale Bedingungen, behauptet wird eine globale.* -/
-- BEWEIST NICHT: dass `P.eigen` die wirkliche Wirkung des Rumpfes IST (B1). Der Satz
-- verschiebt die Frage von der HUELLE zum RUMPFABSTIEG -- und genau dort liegen die
-- Luecken, die das Passregister zu `wirkungen.rahmen` nennt.
-- BEWEIST AUCH NICHT: Vollstaendigkeit. Ein Effekt, den `dekl f` fuehrt und den kein
-- erreichbarer Rumpf hat, faellt hier nicht auf -- die Richtung ist eine Teilmenge, kein
-- Gleichheitssatz. Das ist gewollt: mehr zu deklarieren als man tut, ist erlaubt.
theorem huelle_deckt {P : Programm F}
    (hr : rahmen_haelt P) (hk : kante_haelt P) (f : F) :
    sem P f ⊑ P.dekl f := by
  intro w hw
  obtain ⟨g, hreach, heig⟩ := hw
  exact dekl_monoton hk hreach w (hr g w heig)


#print axioms Passlogik.Wirkung.huelle_deckt
/-! ### 5.1 Zyklen ausdruecklich eingeschlossen

    Der Satz oben nennt keine Bedingung an `ruft`. Um das SICHTBAR zu machen -- und weil
    das Passregister genau an dieser Stelle einen Fehler getragen hat -- steht hier ein
    Programm mit einem echten Zyklus, und der Satz gilt daran.
-/

/-- Zwei Funktionen, die einander rufen. -/
inductive Zwei where | a | b
deriving DecidableEq, Repr

def wechselseitig : Programm Zwei where
  ruft := fun x y => (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .a)
  dekl := fun _ w => w = .writes ⟨0⟩ ∨ w = .reads ⟨1⟩
  eigen := fun f w => match f with
    | .a => w = .writes ⟨0⟩
    | .b => w = .reads ⟨1⟩

theorem wechselseitig_hat_zyklus : wechselseitig.ruft .a .b ∧ wechselseitig.ruft .b .a :=
  ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem wechselseitig_rahmen : rahmen_haelt wechselseitig := by
  intro f w hw
  cases f <;> simp_all [wechselseitig]

theorem wechselseitig_kante : kante_haelt wechselseitig := by
  intro f g _ w hw; exact hw

/-- **Der Satz gilt am Zyklus.** Die Induktion laeuft ueber die Ableitung, nicht ueber
    den Graphen -- und `a` erreicht `b`, `b` erreicht `a`, `a` erreicht `a` ueber zwei
    Kanten, ohne dass der Beweis das stoert. -/
theorem zyklus_stoert_nicht (f : Zwei) : sem wechselseitig f ⊑ wechselseitig.dekl f :=
  huelle_deckt wechselseitig_rahmen wechselseitig_kante f


#print axioms Passlogik.Wirkung.zyklus_stoert_nicht
/-! ## 6. Die Huelle ist eine UNTERE Schranke -- Soundness unter Unvollstaendigkeit

    Das Passregister (2026-08-24): *"the hull is a LOWER bound, so everything IN it really
    happens and demanding that it be declared is sound regardless of what is missing."*

    **Und der Fehler, den derselbe Eintrag beschreibt:** bis dahin kehrte der Pass am
    Zyklus VOR jeder `E008`-Pruefung zurueck. Eine unaufloesbare Kante tief unten
    entwertete `E008` fuer die ganze Rufkette. *Zehn Korpusstellen waren betroffen.*
    Beides steht hier als Satz.
-/

/-- `P` sieht weniger Kanten als `Q`, hat aber dieselben Rumpfwirkungen und dieselben
    Deklarationen: `P` ist die UNVOLLSTAENDIGE Sicht des Passes auf `Q`. -/
structure Teilsicht (P Q : Programm F) : Prop where
  kanten : ∀ f g, P.ruft f g → Q.ruft f g
  eigen  : ∀ f, P.eigen f ⊑ Q.eigen f

theorem erreicht_monoton {r r' : F → F → Prop}
    (h : ∀ f g, r f g → r' f g) {f g : F} (he : erreicht r f g) : erreicht r' f g := by
  induction he with
  | hier f => exact erreicht.hier f
  | ueber e _ ih => exact erreicht.ueber (h _ _ e) ih

/-- Die Huelle waechst mit dem Graphen. **Das ist die "untere Schranke", praezise.** -/
theorem sem_monoton {P Q : Programm F} (h : Teilsicht P Q) (f : F) :
    sem P f ⊑ sem Q f := by
  intro w ⟨g, hreach, heig⟩
  exact ⟨g, erreicht_monoton h.kanten hreach, h.eigen g w heig⟩


#print axioms Passlogik.Wirkung.sem_monoton
/-- **Die ABSAGE bleibt gueltig, auch wenn die Huelle unvollstaendig ist.**

    Findet der Pass ueber der Teilsicht eine Wirkung, die nicht deklariert ist, so ist sie
    auch ueber der vollen Sicht nicht deklariert -- die Absage ist keine Folge der Luecke.
    *Das ist der Satz, der die Korrektur vom 2026-08-24 traegt.* -/
-- BEWEIST NICHT: die Gegenrichtung, und das ist der ganze Punkt. Ein Programm, das ueber
-- der Teilsicht DURCHGEHT, kann ueber der vollen Sicht fallen -- siehe
-- `vollstaendigkeit_geht_verloren`. Verloren ist die VOLLSTAENDIGKEIT, nicht die
-- Widerlegung; `E009` ist als Hinweis genau dafuer da.
theorem absage_haelt_unter_unvollstaendigkeit {P Q : Programm F}
    (h : Teilsicht P Q) (f : F) (hfall : ¬ (sem P f ⊑ P.dekl f)) (hd : P.dekl = Q.dekl) :
    ¬ (sem Q f ⊑ Q.dekl f) := by
  intro hq
  apply hfall
  intro w hw
  rw [hd]
  exact hq w (sem_monoton h f w hw)


#print axioms Passlogik.Wirkung.absage_haelt_unter_unvollstaendigkeit
/-- **Und was wirklich verloren geht: die Vollstaendigkeit.** Es gibt eine Teilsicht, unter
    der ein Programm durchgeht und unter der vollen Sicht faellt. -/
theorem vollstaendigkeit_geht_verloren :
    ∃ (P Q : Programm Zwei), Teilsicht P Q ∧ P.dekl = Q.dekl ∧
      (sem P .a ⊑ P.dekl .a) ∧ ¬ (sem Q .a ⊑ Q.dekl .a) := by
  -- `a` deklariert nichts, ruft aber (in der vollen Sicht) `b`, das schreibt.
  let d : Zwei → Menge Wkg := fun _ => leere
  let e : Zwei → Menge Wkg := fun f w => match f with
    | .a => False
    | .b => w = .writes ⟨0⟩
  refine ⟨⟨fun _ _ => False, d, e⟩, ⟨fun x y => x = .a ∧ y = .b, d, e⟩, ⟨?_, ?_⟩, rfl, ?_, ?_⟩
  · intro f g h; exact h.elim
  · intro f w h; exact h
  · intro w ⟨g, hreach, heig⟩
    cases hreach with
    | hier _ => exact heig
    | ueber e _ => exact e.elim
  · intro hq
    have : sem (F := Zwei) ⟨fun x y => x = .a ∧ y = .b, d, e⟩ .a (.writes ⟨0⟩) :=
      ⟨.b, erreicht.ueber ⟨rfl, rfl⟩ (erreicht.hier _), rfl⟩
    exact hq _ this


#print axioms Passlogik.Wirkung.vollstaendigkeit_geht_verloren
/-! ### 6.1 Der Fehler vom 2026-08-24, als Satz

    *"Am Zyklus wurde `E009` gesetzt und VOR JEDER `E008`-Pruefung zurueckgekehrt."*
    Modelliert: eine Pruefung, die an einem Zyklus schweigt, laesst eine wirkliche
    Verletzung durch.
-/

/-- Die ALTE Pruefung: sie prueft die Kantenbedingung nur, wenn der Graph zyklenfrei ist. -/
def alte_pruefung (P : Programm F) : Prop :=
  (∃ f, erreicht P.ruft f f ∧ (∃ g, P.ruft f g)) ∨ (rahmen_haelt P ∧ kante_haelt P)

/-- **Die alte Pruefung ist nicht sound.** Es gibt ein Programm, das sie passiert und
    dessen deklarierte Menge die semantische Wirkung NICHT umfasst. -/
-- BEWEIST NICHT: dass der Rust genau diese Form hatte. Diese Datei liest keinen Rust.
-- Modelliert ist die im Passregister BESCHRIEBENE Form: am Zyklus wird zurueckgekehrt,
-- bevor `E008` geprueft wird.
theorem alte_pruefung_laesst_durch :
    ∃ P : Programm Zwei, alte_pruefung P ∧ ¬ (sem P .a ⊑ P.dekl .a) := by
  -- `a` und `b` rufen einander (der Zyklus), `b` schreibt, `a` deklariert nichts.
  refine ⟨⟨fun x y => (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .a),
           fun _ => leere,
           fun f w => match f with | .a => False | .b => w = .writes ⟨0⟩⟩, ?_, ?_⟩
  · left
    exact ⟨.a, erreicht.ueber (Or.inl ⟨rfl, rfl⟩) (erreicht.ueber (Or.inr ⟨rfl, rfl⟩)
             (erreicht.hier _)), ⟨.b, Or.inl ⟨rfl, rfl⟩⟩⟩
  · intro h
    exact h (.writes ⟨0⟩) ⟨.b, erreicht.ueber (Or.inl ⟨rfl, rfl⟩) (erreicht.hier _), rfl⟩


#print axioms Passlogik.Wirkung.alte_pruefung_laesst_durch
/-! ## 7. `effects` ist NICHT fail-open -- und was passierte, wenn es das waere

    `SPRACHE.md`:937: *"`effects` is obligatory and not fail-open [...] a tool that reads a
    missing clause as 'no effects' rewards leaving it out."*

    Die Gefahr ist NICHT bei einer Funktion mit sichtbarem Rumpf -- dort faellt die
    fehlende Klausel am Rahmen auf. Sie ist bei einer, deren Rumpf der Pruefer nicht sieht.
-/

/-- Was der Pruefer vom Rumpf SIEHT. Fuer eine `extern fn` ist das nichts. -/
structure Sicht (P : Programm F) where
  gesehen : F → Menge Wkg
  /-- Was gesehen wird, geschieht wirklich. -/
  ehrlich : ∀ f, gesehen f ⊑ P.eigen f
  /-- Und fuer die Funktionen mit sichtbarem Rumpf ist es alles. -/
  sichtbar : F → Prop
  vollstaendig_wo_sichtbar : ∀ f, sichtbar f → P.eigen f ⊑ gesehen f

/-- Der Rahmentest, wie ein Pruefer ihn wirklich fuehren kann: gegen das GESEHENE. -/
def rahmen_gesehen {P : Programm F} (S : Sicht P) : Prop := ∀ f, S.gesehen f ⊑ P.dekl f

/-- **Der Satz, ehrlich formuliert.** Er braucht (B2) als ausdrueckliche Praemisse: fuer
    jede Funktion ohne sichtbaren Rumpf ist die Deklaration eine ANNAHME. -/
-- BEWEIST NICHT: dass die Annahme `fremd_ehrlich` fuer irgendein konkretes Programm
-- gilt. Sie ist unbeweisbar innerhalb der Sprache -- der Rumpf steht in C. Was hier steht,
-- ist ihre Buchung: OHNE sie gibt es den Satz nicht, und `gabbro zeugnis` zaehlt genau
-- diese Flaeche.
theorem huelle_deckt_mit_fremden {P : Programm F} (S : Sicht P)
    (hg : rahmen_gesehen S)
    (fremd_ehrlich : ∀ f, ¬ S.sichtbar f → P.eigen f ⊑ P.dekl f)
    (hk : kante_haelt P) (f : F) :
    sem P f ⊑ P.dekl f := by
  refine huelle_deckt ?_ hk f
  intro g w hw
  by_cases hs : S.sichtbar g
  · exact hg g w (S.vollstaendig_wo_sichtbar g hs w hw)
  · exact fremd_ehrlich g hs w hw


#print axioms Passlogik.Wirkung.huelle_deckt_mit_fremden
/-- **Und ohne die Annahme faellt der Satz.** Liest ein Werkzeug eine fehlende Klausel als
    "keine Wirkung", so passiert ein Programm den Rahmentest, dessen fremder Rumpf
    schreibt -- und die Absage kommt nirgends. *Das ist der Anreiz, gegen den `E001`
    steht.* -/
theorem fail_open_bricht_den_satz :
    ∃ (P : Programm Zwei) (S : Sicht P),
      rahmen_gesehen S ∧ kante_haelt P ∧ ¬ (sem P .a ⊑ P.dekl .a) := by
  -- `b` ist fremd (kein sichtbarer Rumpf), schreibt wirklich, und deklariert nichts,
  -- weil die Klausel fehlt und "fehlt" als leer gelesen wird.
  refine ⟨⟨fun x y => x = .a ∧ y = .b,
           fun _ => leere,
           fun f w => match f with | .a => False | .b => w = .writes ⟨0⟩⟩,
          ⟨fun _ => leere, ?_, fun f => f = .a, ?_⟩, ?_, ?_, ?_⟩
  · intro f w h; exact h.elim
  · intro f hf w hw; cases f
    · exact hw
    · exact absurd hf (by intro h; cases h)
  · intro f w h; exact h.elim
  · intro f g _ w hw; exact hw
  · intro h
    exact h (.writes ⟨0⟩) ⟨.b, erreicht.ueber ⟨rfl, rfl⟩ (erreicht.hier _), rfl⟩


#print axioms Passlogik.Wirkung.fail_open_bricht_den_satz
/-! ## 8. FUND: was `E008` wirklich vergleicht -- die GROBE Deckung

    Das Passregister sagt zu `wirkungen.abschluss`:
    *"places are compared only for known world state: for everything else only the KIND is
    compared, so `writes a` covers `writes b`."*

    **Damit gilt der Satz aus §5 NICHT ueber `Wkg`, sondern ueber der ART.** Das ist eine
    echt schwaechere Aussage, und sie steht hier so da.
-/

/-- Die ART einer Wirkung -- was uebrig bleibt, wenn der Ort wegfaellt. -/
inductive Art where
  | reads | writes | locks | locksShared | masks | allocs | consumes | publishes | diverges
deriving DecidableEq, Repr

def art : Wkg → Art
  | .reads _ => .reads      | .writes _ => .writes
  | .locks _ => .locks      | .locksShared _ => .locksShared
  | .masks _ => .masks      | .allocs _ => .allocs
  | .consumes _ => .consumes | .publishes _ => .publishes
  | .diverges => .diverges

/-- Das Bild einer Wirkungsmenge unter `art`. -/
def arten (A : Menge Wkg) : Menge Art := fun a => ∃ w, A w ∧ art w = a

/-- Die GROBE Deckung, die der Pass fuer nicht-weltliche Orte fuehrt. -/
def deckt_grob (A B : Menge Wkg) : Prop := arten A ⊑ arten B

theorem teilmenge_dann_grob {A B : Menge Wkg} (h : A ⊑ B) : deckt_grob A B := by
  intro a ⟨w, hw, harts⟩
  exact ⟨w, h w hw, harts⟩

/-- **Und die Umkehrung gilt nicht.** `writes a` deckt grob `writes b` -- die
    Ortsinformation ist weg. *Der Satz aus §5 ist also ueber `Wkg` nur so stark, wie der
    Ortsvergleich es hergibt; ueber `Art` ist er unbedingt.* -/
-- BEWEIST NICHT: dass der heutige Pruefer an jeder Stelle grob vergleicht. Das
-- Passregister sagt, er vergleiche Orte fuer BEKANNTEN Weltzustand (`static`, `atomic`,
-- `table`, `device`, `state`) und sonst nur die Art. Modelliert ist die zweite Haelfte,
-- weil sie die schwaechere ist.
theorem grob_deckt_mehr :
    ∃ A B : Menge Wkg, deckt_grob A B ∧ ¬ (A ⊑ B) := by
  refine ⟨fun w => w = .writes ⟨1⟩, fun w => w = .writes ⟨0⟩, ?_, ?_⟩
  · intro a ⟨w, hw, ha⟩
    exact ⟨.writes ⟨0⟩, rfl, by rw [← ha, hw]; rfl⟩
  · intro h
    have := h (.writes ⟨1⟩) rfl
    simp [Wkg.writes.injEq, Ort.mk.injEq] at this


#print axioms Passlogik.Wirkung.grob_deckt_mehr
/-- **Der Satz aus §5 unter der groben Deckung.** Er gilt -- ueber `Art`. Das ist die
    Aussage, die ein Pruefer mit grobem Ortsvergleich wirklich herstellt. -/
theorem huelle_deckt_grob {P : Programm F}
    (hr : ∀ f, deckt_grob (P.eigen f) (P.dekl f))
    (hk : ∀ f g, P.ruft f g → deckt_grob (P.dekl g) (P.dekl f)) (f : F) :
    arten (sem P f) ⊑ arten (P.dekl f) := by
  have mono : ∀ {g}, erreicht P.ruft f g → arten (P.dekl g) ⊑ arten (P.dekl f) := by
    intro g h
    induction h with
    | hier _ => exact teilmenge_refl _
    | ueber e _ ih => exact teilmenge_trans ih (hk _ _ e)
  intro a ⟨w, ⟨g, hreach, heig⟩, ha⟩
  exact mono hreach a (hr g a ⟨w, heig, ha⟩)


#print axioms Passlogik.Wirkung.huelle_deckt_grob
/-! ## 9. Was diese Datei ausdruecklich NICHT beweist

    1. **Kein Pfad-, sondern ein MENGENabschluss.** `sem` vereinigt ueber alle
       erreichbaren Ruempfe. Dass zwei Wirkungen auf EINEM Pfad zusammentreffen, sagt
       das nicht -- die Sperrordnung (`Rang.lean`) braucht genau das und rechnet darum
       anders.
    2. **Keine Aussage ueber `E009`.** Der dritte Zustand ist ein Hinweis ueber die
       VOLLSTAENDIGKEIT; §6 zeigt, dass die Widerlegung ihn nicht braucht.
    3. **Keine Aussage ueber `E011`** (`traverse … touches`) und keine ueber die
       `effects`-Klauseln an `retry`/`forever` -- das Passregister haelt fest, dass
       letztere ueberhaupt keinen Leser haben.
    4. **Nichts ueber `E010`s Reichweite.** Die Leseseite ist auf bekannten Weltzustand
       gezogen; Parameter und Konstanten fallen still heraus. Das ist eine Aussage ueber
       `P.eigen` (B1), nicht ueber die Huelle.
-/

end Passlogik.Wirkung
