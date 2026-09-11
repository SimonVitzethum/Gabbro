/-
  Datei:      Grammatik/Ziel.lean
  Gegenstand: **DAS ZIEL**, als Satz ueber der Grammatik -- unabhaengig vom `.rs`-Code.

  > Wer ein Gabbro-Programm verifiziert, beweist NUR seine eigene Logik und seine
  > Hardwaremassnahmen. Den Rest tragen Gabbro und CompCert -- angenommen, Gabbro
  > ist formal verifiziert.

  Was das hier heisst, und warum es nicht vom Pruefer (`.rs`) abhaengt:

    * Die Grammatik ist `Syntax.lean` (getypte Familie): was sie nicht ableitet,
      ist nicht schreibbar -- kein Pass kann es vergessen, weil es keinen Term
      dafuer gibt.
    * Die Bedeutung ist `Semantik.lean` (`eval`/`exec`, totale Funktionen): jeder
      Ausgang ist Kontrollfluss, `logik` oder `hardware` (`zwei_fehler`).
    * Der Rahmen und die Spur sind `Satz.lean` (`exec_rahmen`, `exec_spur`,
      `exec_gut`): ein Rumpf schreibt nur, was sein Vertrag nennt, und jeder
      Zugriff traegt die Waechter seines Traegers.
    * Die Wettlaeufe sind `Wettlauf.lean` (`kein_wettlauf`,
      `kein_wettlauf_global`, `keine_ueberkreuzung`): ueber JEDER Verschraenkung
      solcher Spuren ist ein bewachter Traeger geordnet oder `atomic`.
    * Die Stabilitaet ist `InterferenzAllgemein.lean` (`allgemeinStabil`):
      gueltige und schrittweise erhaltene Zusicherungen gelten an der letzten
      Welt der Kette.
    * Die Komposition ist `Komposition.lean` (`UmgebungOk`, `SchleifenOk`):
      die Ruf- und Schleifenordnung als Gestalt, noch ohne Beweis.
    * Das Geteilte ist `Geteilt.lean` (`geteilt_treu`): als ungeteilt
      Erklaertes erreicht hoechstens ein Faden -- gerechnet, nicht angenommen.
    * Die Zeit ist geteilt («SG-22», `SYNTAX.md` §18): das Budget
      (`costs`, `held <=`, `bounded`, `per_pass … ops`) ist Logik am
      Deklarierten; die Frist (`deadline … arch … falsifier …`) ist das
      Hardware-Ergebnis `fortschritt` -- dieselbe Annahme, die `forever`
      traegt, mit ihrer Sonde.
    * Die C-Seite ist unten als GESCHLOSSENE Liste (`CForm`) geschrieben: was
      nie emittiert wird, braucht keine Semantik. Die Absenkung
      (`Absenkung`) erweitert jede Gabbro-Primitive begrenzt; quantitatives
      CompCert erhaelt die `ops`-Zahl von C nach Asm. Wanduhr und Zyklen
      betreten nie die Logik -- sie betreten durch `deadline` und ihre Sonde.

  QUELLE: `dokumente/SYNTAX.md` §18 (vierte Fassung, 2026-09-09).
  KEIN Import aus `crates/`, `programmlogik/`, `passlogik/` oder `Body.lean`:
  `lakefile.toml` laesst das nicht zu -- was hier steht, gilt mit DIESER Syntax,
  gleichgueltig, was der heutige `.rs`-Code tut oder laesst.

  GRENZEN, gemessen am 2026-09-10 (`messung/ZIEL-BEWERTUNG-2026-09-10.md`):
  kein Satz fuehrt `exec`-Spuren in `Gesittet` ueber (die Bruecke steht in
  `Wettlauf.lean` als `lauf_aus_brav`, mit W3-W5 als Prämissen); die gueltige
  sequenzielle Logik unter Verschraenkung (Owicki-Gries-Schritt) steht nirgends;
  die Frist ist hier nur benannt (`fristAlsAnnahme`) -- gemessen wird sie von
  der Sonde (`sonden/sonde_tick.c`, Probenwaehrung, kein Beweis).
-/
import Grammatik.Wettlauf
import Grammatik.Zucker
import Grammatik.InterferenzAllgemein
import Grammatik.Komposition
import Grammatik.Geteilt
import Grammatik.Fristlauf
import Grammatik.Maschine

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Die C-Seite -- geschlossen, nicht "C" -/

/-- Die Zielformen, ueber die der Absenkungsvertrag spricht -- 19 benannte
    Gestalten, KEINE geschlossene Liste. Dass der Erzeuger nur diese schreibt,
    ist unbewiesen: `dokumente/BEWEIS.md`, Gegenstand 2, misst 64 Formen im
    Erzeugnis, davon 30 ohne Entscheid (u.a. Zeigerarithmetik an 491 Stellen).
    Wer die Liste schliesst, entscheidet die 19 (`?:` als Muster) oder nimmt
    sie aus dem Erzeuger. -/
inductive CForm where
  | statisch | extern | zuweisung | wenn | schalter | zaehlSchleife
  | rueckgabe | sprungAlsSchleifenende | ruf | literal | name | feld
  | index | wahlLesen | atomar | beschraenkt | fluechtig | noreturn | asmEins
  deriving DecidableEq, Repr

/-- Die Absenkung ALS ANNAHME: jede Gabbro-Primitive wuerde zu einer BEGRENZTEN
    Liste von C-Formen. `ops` zaehlt die Gabbro-Seite; erhalten wuerde die Zahl
    ein quantitatives CompCert (CerCo, nicht der Produktionsuebersetzer). -/
structure Absenkung where
  proPrimitiv : Nat
  begrenzt : proPrimitiv ≤ 18

/-- Die Zahl, auf der der Vertrag ruhen wuerde -- TEILGEMESSEN seit 2026-09-10
    (`messung/ABSENKUNG-MESSUNG.md`, Entscheid `messung/ABSENKUNG-SCHRANKEN-ENTSCHEID.md`):
    `17` ist das statisch gezaehlte Maximum je Gabbro-Primitiv (staerkste Zeile:
    `Schleife`/`traverse over descendants of`, `emit.rs:8523-8560`); die Schranke
    `18` ist das Maximum plus eins Kopfraum. Der Lauf ueber echte Erzeugnisse mit
    einem Lexer (`ABSENKUNG-ZAEHLUNG.md` §2) steht noch aus -- er kann das Maximum
    nur bestaetigen oder heben, nie unter `17` senken. CompCert beweist ohnehin
    Semantikerhaltung, keine Kostenerhaltung (sequenziell, rennfrei, ohne
    `__asm__`, ohne C11-`_Atomic`: 39 `_Atomic`, 120 `volatile`, 2 `__asm__` im
    eigenen Erzeugnis). -/
def absenkung : Absenkung := ⟨17, by decide⟩

/-- FRAGMENT BOUNDARY (p13): what IS modeled here is the NUMERIC bound only --
    the witness `17` and the cap `18` on `proPrimitiv`. What is NOT modeled:
    the lowering MAP itself (Gabbro primitive to `List CForm`), per-primitive
    expansion, C semantics, and quantitative CompCert preservation. Those stay
    assumptions and cuts (see `Erhaltung.lean` P2/C2, `Budget.lean` C3). The
    lemmas below discharge the obligation register for the modeled fragment:
    the witness keeps the bound, and anything under the witness keeps it too.
    Rust `absenkung.rs` stays unwired and is not read here. -/
theorem absenkung_wert : absenkung.proPrimitiv = 17 := rfl

/-- The witness discharges the bound the structure demands. -/
theorem absenkung_haelt_schranke : absenkung.proPrimitiv ≤ 18 :=
  absenkung.begrenzt

/-- Anything under the measured maximum stays under the witness. -/
theorem absenkung_unter_maximum (n : Nat) (h : n ≤ 17) :
    n ≤ absenkung.proPrimitiv := h

/-- The witness preserves the cap transitively: under the witness is under 18. -/
theorem absenkung_monoton (n : Nat) (h : n ≤ absenkung.proPrimitiv) :
    n ≤ 18 :=
  Nat.le_trans h absenkung.begrenzt

/-! ## 2. Das Ziel -- ein Satz je Zeile -/

/-- Jeder Ausgang ist Kontrollfluss, Logik oder Hardware -- kein dritter. -/
theorem ziel_zwei_fehler (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) :=
  zwei_fehler o

/-- Jede Bedeutung existiert -- `exec` ist eine Funktion. -/
theorem ziel_total (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    ∃ o : Ausgang V l Γ, exec P O passes fuel V b σ ρ = o :=
  bedeutung_total P O passes fuel b σ ρ

/-- Determinismus: dieselbe Bedeutung, dieselben Eingaben, derselbe Ausgang.
    (Dass `exec` eine Definition ist, IST der Beweis.) -/
theorem ziel_deterministisch (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) :
    exec P O passes fuel V b σ ρ = exec P O passes fuel V b σ ρ := rfl

/-- Der Rahmen: ein Rumpf schreibt nur, was sein Vertrag nennt. -/
theorem ziel_rahmen (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' →
      Rahmen V.schreibt V.gschreibt σ σ' :=
  exec_rahmen P O passes fuel hO b σ ρ hh

/-- Die Spur: jeder Zugriff traegt die Waechter seines Traegers. -/
theorem ziel_spur (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt) :
    ∀ σ', (exec P O passes fuel V b σ ρ).welt = some σ' →
      σ'.haelt = σ.haelt ∧ (∀ e ∈ σ'.spur, e ∈ σ.spur ∨ e.gut) ∧
      (Konsistent σ.spur → Konsistent σ'.spur) :=
  exec_spur P O passes fuel hO b σ ρ hh

/-- Kein Datenwettlauf auf einem Traeger -- ueber jeder Verschraenkung. -/
theorem ziel_wettlauf (l : Lauf D) (hg : Gesittet l) (i j : Nat) (hij : i < j)
    (f g : Faden) (hfg : f ≠ g) (t : D.Tab) (w w' : Bool)
    (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.zugriff t w Λ h)))
    (hj : l[j]? = some (Schritt.mk g (.zugriff t w' Λ' h'))) :
    HB l i j :=
  kein_wettlauf l hg i j hij f g hfg t w w' Λ Λ' h h' hi hj

/-- Kein Datenwettlauf auf einem Global -- oder es ist `atomic`, und dann
    ordnet die Maschine (A10, `hardware (sichtbarkeit)`). -/
theorem ziel_wettlauf_global (l : Lauf D) (hg : Gesittet l) (i j : Nat) (hij : i < j)
    (f g : Faden) (hfg : f ≠ g) (x : D.Glob) (w w' : Bool)
    (Λ Λ' : List (Res D)) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.gzugriff x w Λ h)))
    (hj : l[j]? = some (Schritt.mk g (.gzugriff x w' Λ' h'))) :
    HB l i j ∨ D.atomar x = true :=
  kein_wettlauf_global l hg i j hij f g hfg x w w' Λ Λ' h h' hi hj

/-- Keine Ueberkreuzung der Sperrordnung -- die Wartekette hat keinen Anfang. -/
theorem ziel_ordnung (l : Lauf D) (hg : Gesittet l) (i j : Nat) (f g : Faden)
    (L1 L2 : D.Lock) (h h' : List D.Lock)
    (hi : l[i]? = some (Schritt.mk f (.nimmt L2 h)))
    (hj : l[j]? = some (Schritt.mk g (.nimmt L1 h')))
    (h1 : L1 ∈ h) (h2 : L2 ∈ h') : False :=
  keine_ueberkreuzung l hg i j f g L1 L2 h h' hi hj h1 h2

/-! ## 2b. From `exec` traces to `Gesittet` -- the narrowed class (p14)

    The gap named in GRENZEN above: no sentence carries `exec` traces into
    `Gesittet`; the bridge stands in `Wettlauf.lean` as `lauf_aus_brav`, with
    W3-W5 as premises. This section closes it as far as one body reaches, and
    narrows the trace class explicitly for the rest -- no `sorry`.

    What one body reaches: `ziel_brav_aus_exec` reads a single `exec` outcome
    as `Brav` (it IS `exec_spur`, whose conclusion is `Brav` unfolded). What no
    single-body sentence can reach: W3 (exclusion speaks about foreign lock
    primitives), W4 (one mark in one thread, across threads), W5 (an unshared
    carrier belongs to one thread -- the declaration). So the narrowed class
    `ExecEng` carries exactly those three shapes plus the `Einfaedig`
    construction for W4, and `ziel_gesittet_aus_exec_eng` builds `Gesittet`
    from it through `lauf_aus_brav` (W1, W2) and `gesittet_aus_einfaedig`
    (W3-W5). Each `ExecEng.provenienz` witness is closed per body by
    `ziel_brav_aus_exec`; the Owicki-Gries step (sequential contracts surviving
    interleaving) is NOT here -- it stands nowhere yet and stays open. -/

/-- A single `exec` outcome is `Brav`: the open locks are unchanged, every new
    event is good, and a consistent trace stays consistent. This is `exec_spur`
    read as `Brav` -- one provenance witness per body. -/
theorem ziel_brav_aus_exec (P : Programm D) (O : Orakel D) (passes fuel : Nat) (hO : GutO O)
    (b : Block D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ) (hh : HeldGenau Λ σ.haelt)
    (σ' : World D) (h : (exec P O passes fuel V b σ ρ).welt = some σ') :
    Brav σ σ' :=
  exec_spur P O passes fuel hO b σ ρ hh σ' h

/-- The narrowed trace class: per-thread `exec` provenance (`Brav` from empty
    traces, closed per body by `ziel_brav_aus_exec`), the interleaving shape,
    and exactly the three cross-thread premises no single body can close --
    W3 as exclusion, W4 as the `Einfaedig` construction over the projected run,
    W5 as the unshared-carrier shape. -/
structure ExecEng (l : Lauf D) (voll : Faden → List (Ereignis D)) (code : D.Marke → Nat) : Prop where
  /-- Per-thread provenance: each full trace is `Brav` from an empty trace. -/
  provenienz : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f
  /-- The observed sub-traces are tails of the full ones (interleaving). -/
  verschraenkung : IstVerschraenkung l voll
  /-- (W3) Exclusion: who takes `L` takes it while no other thread holds it. -/
  ausschluss : ∀ (j : Nat) (f : Faden) (L : D.Lock) (h : List D.Lock),
    l[j]? = some (Schritt.mk f (.nimmt L h)) → ∀ g, g ≠ f → ¬ l.haelt g L j
  /-- (W4) One mark in one thread, as the construction over the projected run. -/
  einfaedig : Marken.Einfaedig (laufProj code l)
  /-- (W5) An unshared carrier belongs to one thread. -/
  ungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob) (ei ej : Ereignis D),
    l[i]? = some (Schritt.mk f ei) → l[j]? = some (Schritt.mk g ej) →
    ei.traeger = some o → ej.traeger = some o →
    (match o with | .inl t => D.geteilt t = false | .inr x => D.ggeteilt x = false) → f = g

/-- **From `exec` traces to `Gesittet`, over the narrowed class.** W1 and W2
    come from `lauf_aus_brav` (per-thread `Brav` over empty traces, inherited
    over tails); W3-W5 travel in `ExecEng` and are consumed by
    `gesittet_aus_einfaedig`. -/
theorem ziel_gesittet_aus_exec_eng (l : Lauf D) (voll : Faden → List (Ereignis D))
    (code : D.Marke → Nat) (h : ExecEng l voll code) : Gesittet l := by
  obtain ⟨hvoll, hvers, hausschluss, heinfaedig, hungeteilt⟩ := h
  obtain ⟨hkons, hgut⟩ := lauf_aus_brav l voll hvoll hvers
  exact gesittet_aus_einfaedig l hkons hgut hausschluss code heinfaedig hungeteilt

#print axioms Gabbro.Grammatik.ziel_brav_aus_exec
#print axioms Gabbro.Grammatik.ziel_gesittet_aus_exec_eng

/-! ## 3. Die Zeit -- Budget als Logik, Frist als Hardware («SG-22») -/

/-- Das Budget (`costs`, `held <=`, `bounded`, `per_pass … ops`) ist eine Zahl
    am Deklarierten: statisch berechenbar, gegen die Deklaration gehalten.
    Die Frist (`deadline … arch … falsifier …`) ist KEIN zweites Budget:
    sie ist die benannte Umgebungsannahme -- `fortschritt`, mit ihrer Sonde. -/
def fristAlsAnnahme (a : D.Annahme) : Hardware D := .fortschritt a

/- ZURUECKGEZOGEN am 2026-09-10, und zwar der Satz, nicht die Definition:
   `ziel_zeit_ist_hardware` behauptete `∃ e, fristAlsAnnahme a = e` -- eine
   Existenzaussage ueber eine totale Funktion, die JEDER Definition gelingt.
   Nichts konnte sie beschaedigen, also mass sie nichts (dieselbe Klasse wie
   die trivialen `bedeutung_total`/`wert_total`, die der Ordner als trivial
   BESTAETIGT -- diese Zeile tat es nicht). Was bleibt, ist die Definition
   oben: die Abbildung Frist → Annahme. Gemessen wird die Frist von der Sonde
   (`sonden/sonde_tick.c`, Probenwaehrung R15/W10: Stichprobe, kein Beweis),
   nicht von einem Satz hier. -/

/-! ## 4. Die Unabhaengigkeit -- was hier NICHT gelesen wurde -/

/-- Das Ziel in einem Satz -- und zwar NUR dieser: jeder Fehler eines
    Ausgangs ist Kontrollfluss, Logik oder Hardware. Rahmen (`ziel_rahmen`),
    Spur (`ziel_spur`), Verschraenkung (`ziel_wettlauf`, `ziel_wettlauf_global`,
    `ziel_ordnung`), Fristabbildung (`fristAlsAnnahme`) und Absenkung
    (`Absenkung`, als Annahme) stehen als eigene Saetze daneben -- was hier
    stuende und dort beweist, waere ein Kommentar, der mehr behauptet als sein
    Satz. Nichts davon nennt einen Pass, eine Diagnose oder eine
    Erzeugerzeile. -/
theorem ziel (o : Ausgang V l Γ) :
    (∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
    (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
    (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e) :=
  zwei_fehler o

#print axioms Gabbro.Grammatik.ziel
#print axioms Gabbro.Grammatik.ziel_rahmen
#print axioms Gabbro.Grammatik.ziel_spur
#print axioms Gabbro.Grammatik.ziel_wettlauf
#print axioms Gabbro.Grammatik.ziel_wettlauf_global
#print axioms Gabbro.Grammatik.ziel_ordnung

/-! ## 5. The goal itself, as a theorem (Phase 5 formulation) -/

/-- **What a verified program still owes (`ziel_nutzer_last`).** Every outcome is
    control flow (`ok`, `zurueck`, `grund`, `leave`, `next`), the author's own
    logic (`logik`), or a NAMED hardware assumption (`hardware`) -- nothing else.
    That is the whole user-facing contract: prove your own logic, name your
    hardware assumptions; Gabbro and CompCert carry the rest (once Gabbro is
    verified).

    Rewritten 2026-09-11: the conclusion is no longer the bare `zwei_fehler`
    split (which held unconditionally, with all four premises discarded via
    `have _ :=`). It is now the per-run obligation conjunction below, and every
    premise is load-bearing -- each occurs in the proof term applied to one of
    the merged execution lemmas, so deleting any premise breaks elaboration.
    There is no `have _ := premise` anywhere in the proof, and no bare `Prop`
    slot that `False` could inhabit (the auditor's old probe
    `ziel_nutzer_last o hB False False ⟨0, by decide⟩` no longer elaborates:
    every slot now has a fixed shape).

    Each leg reuses a merged result instead of re-proving it:

    * Bridge leg (`Gesittet J.l`): `bruecke_exec_gesittet` (`Wettlauf.lean`)
      over the covered interleavings -- per-thread `Brav` provenance from
      `exec` traces (`hvoll`, closed per body by `ziel_brav_aus_exec`),
      the interleaving shape (`hvers`), and exactly the three cross-thread
      shapes no single body can close: W3 as `ForeignExclusion` (named-HW,
      `A_lock`), W4 as the `Einfaedig` construction (`hEin`), W5 inline
      (`hungeteilt`). The old universal `hBridge` (every interleaving is
      `Gesittet`) was too strong to ever discharge; the narrowed class is
      what `lauf_aus_brav` reaches. `hLink` ties the joint run to the
      covered trace (`J.l = run`).
    * Goodness leg (W1-W2): `lauf_aus_brav` (`Wettlauf.lean`) -- consistency
      and goodness inherited over suffixes from the same `hvoll`/`hvers`.
    * Sequential-logic leg: `stabil_from_spec` (`InterferenzAllgemein.lean`),
      i.e. the `ziel_seqLogic_aus_spec` discharge shape (§6 L2, w02 merged):
      sequential contract triples (`hSpec`, OWN-LOGIC) plus the
      interference-freedom check (`hFree`, OWN-LOGIC) yield stable contract
      assertions at the last world, modulo frame-locality (`hAb`,
      GABBRO-DUTY). The 2026-09-10 comment that this step "stands nowhere
      yet" is superseded: it stands at `InterferenzAllgemein.lean:1030`,
      bound at §6 below.
    * Probe leg: `sampling_closes_frist` (`Fristlauf.lean`, w04 merged) --
      with the residual spacing premise (`hspace`, NAMED-HW, per-use) every
      expiry strictly between check and use is caught, and `fristErgebnis`
      answers the named `fortschritt` assumption (the `fristAlsAnnahme`
      mapping).
    * Lowering leg: the `Absenkung` cap (`hLowering.begrenzt`) -- the contract
      the witness must keep. The measured witness (`absenkung`, 17 under 18)
      is the §6 L5 discharge (w05 merged); the count-preservation fragment
      for the modeled ops (`modell_erhaltung`, `modell_lauf_erhalten`) stands
      where the budget stands (`Budget.lean`, which imports this file, so it
      is cited, not imported).
    * Outcome leg: `zwei_fehler` -- the classification itself, still
      definitionally true, now carried as one leg among six rather than the
      whole conclusion. -/
theorem ziel_nutzer_last (o : Ausgang V l Γ)
    (run : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung run voll)
    (hausschluss : ForeignExclusion (D := D) run)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code run))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (carrier : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      run[i]? = some (Schritt.mk f ei) → run[j]? = some (Schritt.mk g ej) →
      ei.traeger = some carrier → ej.traeger = some carrier →
      (match carrier with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hLink : J.l = run)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hFree : InterferenceFree Nb J (SpecQ Pre Post Nb J))
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet J.l)
    ∧ ((∀ f j, Konsistent (run.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ run.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLink]
    exact bruecke_exec_gesittet run voll hvoll hvers hausschluss code hEin hungeteilt
  · exact lauf_aus_brav run voll hvoll hvers
  · exact stabil_from_spec Nb J I Pre Post hInv hDeck hAb hSpec hFree
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o

#print axioms Gabbro.Grammatik.ziel_nutzer_last

/-! ## 6. Discharge record (w06 proof architect, 2026-09-11)

    Verdict: CONDITIONAL -- see `messung/ZIEL-BEWEIS.md` §5 for the exact open
    list.     This section binds each PASSED wave result at Ziel level (theorem, or
    `def` for the witness itself, no `sorry`) and keeps each FAILED premise an explicit hypothesis: nothing
    is papered over, and nothing is duplicated across an import cycle.

    Ledger tags: OWN-LOGIC (the user's `Logik D`), NAMED-HW (a named
    `Hardware D` assumption with its probe), GABBRO-DUTY (a named
    checker-side duty, carried under the standing assumption that Gabbro is
    verified -- "Den Rest tragen Gabbro und CompCert").

    L1 (w01 `f890dac`, PASS, merged): the last open ruling-table slot is
    decided. The discharge theorem stands where the table stands --
    `tafel_geschlossen : satz_tafel` (`Erhaltung.lean:806`, with
    `entschiedenDec` at `:792`) -- because `Erhaltung` imports `Ziel`
    (`Erhaltung.lean:112`), so `Ziel` cannot import it back; this record
    names that theorem instead of duplicating it. The row
    (`Erhaltung.lean:305`) admits the fixed four-header preamble with price
    (cut C3, trust pinned by `cc -c`, never proved -- ledger NAMED-HW,
    toolchain assumption with its check).

    L2 (below, PASS, merged): the concrete sequential-logic shape behind
    `ziel_nutzer_last`'s abstract `hSeqLogic` slot.

    L5 (below, PASS, merged): the lowering witness and its bound, closed.
    The count-preservation fragment for the seven modeled ops stands where
    the budget stands -- `modell_lauf_erhalten` (`Budget.lean:690`,
    `modell_erhaltung` at `:681`) -- because `Budget` imports `Ziel`
    (`Budget.lean:92`), so `Ziel` cannot import it back; the measured bound
    (`ABSENKUNG-DURCHSETZUNG.md` §§5-6, fisch re-run, max 17) is cited, not
    re-stated.

    L3 (w03 `1fc7f4a`, FAIL partial, NOT merged): `hBridge` stays a
    hypothesis. Proved on the branch (read-only cite, no import):
    `bruecke_exec_gesittet` (`Wettlauf.lean:793`), `gut_without_suffix`
    (`:767`), `covered_prefix` (`:779`) -- with `ForeignExclusion` (`:760`,
    accepted as NAMED-HW, `A_lock`) as premise. OPEN: the W4 trace link
    (per-thread `Verlauf` through `exec` behind a real `Lauf` stands
    nowhere) and the W5 run-to-`Bau` wiring (cut C2).

    L4 (w04 `231c514`, FAIL partial, NOT merged): `hProbe` stays a
    hypothesis. Proved on the branch (read-only cite, no import):
    `TickClock.window` (`Fristlauf.lean:328`), `sampling_upholds_frist`
    (`:373`), `sampling_closes_frist` (`:395`). OPEN: the probe-to-grid
    link (C4 at `:82` -- the hardware keeping the grid is a per-use
    premise; `sonde_tick.c` is not a periodic sampler), per-use
    `deadlineSpacing` (`:388`, NAMED-HW), and 28 of 29 deadlines without a
    running probe.
-/

/-- L2 discharge (w02 `0bcff72`, PASS, merged): the concrete shape that fills
    `ziel_nutzer_last`'s abstract `hSeqLogic` slot -- sequential contract
    triples (`hSpec`, OWN-LOGIC: the user's requires/ensures) plus the
    interference-freedom check (`hFree`, OWN-LOGIC: the per-program
    Owicki-Gries obligation) yield stable contract assertions at the last
    world, modulo the frame-locality premise (`hAb`, GABBRO-DUTY: the
    checker's footprint duty, discharged downstream by
    `haengtAb_vertrag_gesamt` once both footprints lie in the signature
    frame). Proved by `stabil_from_spec`
    (`InterferenzAllgemein.lean:1030`, merged §19). -/
theorem ziel_seqLogic_aus_spec (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hFree : InterferenceFree Nb J (SpecQ Pre Post Nb J))
    (σ : World D) (hletzte : J.welten.getLast? = some σ)
    (f : Faden) (hf : f ∈ J.faeden) :
    SpecQ Pre Post Nb J f σ :=
  stabil_from_spec Nb J I Pre Post hInv hDeck hAb hSpec hFree σ hletzte f hf

/-- L5 discharge, witness (w05 `d3b0647`, PASS, merged): the `hLowering` slot
    of `ziel_nutzer_last` takes an `Absenkung` -- this is the measured one,
    `17` under `18` (fisch re-run `ABSENKUNG-DURCHSETZUNG.md` §5: seventeen
    units exit 0, T/V/R identical to lane-122, max 17 at
    Schleife/traverse-over-descendants-of). -/
def ziel_l5_absenkung_zeuge : Absenkung :=
  absenkung

/-- L5 discharge, bound: the witness keeps the cap. -/
theorem ziel_l5_schranke : absenkung.proPrimitiv ≤ 18 :=
  absenkung_haelt_schranke

/-- L5 discharge, maximum: the measured maximum sits under the witness
    (anything under 17 stays under it -- the lexer run can only confirm or
    raise, never lower below 17). -/
theorem ziel_l5_max : 17 ≤ absenkung.proPrimitiv :=
  absenkung_unter_maximum 17 (Nat.le_refl 17)

#print axioms Gabbro.Grammatik.ziel_seqLogic_aus_spec
#print axioms Gabbro.Grammatik.ziel_l5_absenkung_zeuge
#print axioms Gabbro.Grammatik.ziel_l5_schranke
#print axioms Gabbro.Grammatik.ziel_l5_max

/-! ## 7. Invariant-form discharge: no per-run interference proof (y02, 2026-09-11)

    The auditor's finding behind `InterferenzAllgemein.lean` §20: the §6
    discharge (`ziel_seqLogic_aus_spec`, bound to `stabil_from_spec`)
    books `hFree : InterferenceFree` as user OWN-LOGIC -- a per-run
    non-interference proof over every foreign step. For the covered class
    -- contract assertions in invariant (resource-invariant) form -- §20
    derives that check by construction (`interferenceFree_of_invariantForm`
    over `invErhalt_aus_Kontext`), and `stabil_from_spec_invariantForm`
    closes it to the last world with `hForm` in place of `hFree`. The
    theorem below is the Ziel-level binder §20 booked as remainder: same
    conclusion as `ziel_seqLogic_aus_spec`, with the FORM check owed
    instead of the per-run check. Non-invariant assertions over shared
    carriers still owe `hFree` exactly as §6 books it. -/

/-- L2-invariant discharge (y02): the invariant-form shape that fills
    `ziel_nutzer_last`'s sequential-logic slot without a per-run
    interference proof -- `hForm` (OWN-LOGIC: exhibit, per thread, the
    carrier whose invariant the contract conjunction coincides with) plus
    the unchanged `hInv` context premise. Proved by
    `stabil_from_spec_invariantForm` (`InterferenzAllgemein.lean`, §20). -/
theorem ziel_seqLogic_aus_spec_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (σ : World D) (hletzte : J.welten.getLast? = some σ)
    (f : Faden) (hf : f ∈ J.faeden) :
    SpecQ Pre Post Nb J f σ :=
  stabil_from_spec_invariantForm Nb J I Pre Post hInv hDeck hAb hSpec hForm σ hletzte f hf

#print axioms Gabbro.Grammatik.ziel_seqLogic_aus_spec_invariantForm

/-! ## 8. The goal from discipline: no assumed context, no per-run check (z03, 2026-09-11)

    What §5 still owes, and what this section stops owing. `ziel_nutzer_last`
    takes the strong `hInv : InvariantenKontext` -- the invariant at EVERY chain
    world -- as a premise, and the general `hFree : InterferenceFree` beside it;
    even the §7 invariant variant keeps `hInv` as a premise instead of deriving
    it. This section wires the goal to the derived side:

    * (a) `hInv` is DERIVED, not assumed: `invariantenKontext_aus_disziplin`
      (§21, read-only reuse) folds the per-carrier lemma over all carriers from
      entry (`hEntry` -- the invariant holds at the chain head),
      return-restoration (`hReturn` -- every writing step re-establishes what it
      owes at its end world under the guard), and the single watch premise per
      carrier (`hWatch` -- writing steps hold the guard). The premises are
      restated honestly in the callee's shape. For tables the watch discharges
      from `J.hSchuld` plus coverage (`wache_aus_schuld`, from `SchuldnerHaelt`
      §3 via U003 `Syntax.lean`:181, proved per body by `schuldnerHaelt_gilt`);
      for globals it stays checker-side -- see the §21 scope prose. No `sorry`,
      no `axiom`; `InterferenzAllgemein.lean` is not touched.
    * (b) `hFree` is DERIVED for the covered fragment, not owed per run: the
      sequential-logic leg runs through the §7 invariant variant
      (`ziel_seqLogic_aus_spec_invariantForm`), which takes `hForm :
      InvariantForm` (OWN-LOGIC: exhibit, per thread, the carrier whose
      invariant the contract conjunction coincides with) in place of `hFree`.
      The non-invariant fragment stays booked: assertions over shared carriers
      that are NOT in invariant form still owe `hFree` exactly as §6 books it.
    * (c) The CSL-exact reading travels as its own leg:
      `interferenceFree_wo_frei` (§21, read-only reuse) over one shared table
      carrier -- the standard CSL case -- with the conclusion gated on the guard
      being free at BOTH step worlds (`LockFrei L vor`, `LockFrei L nach`). Its
      premises (carrier `t₀`, guard `L`, frame-locality, guard link, entry,
      return, coverage `hCov`, uniform coincidence `hFormU`) are stated
      separately from the general discipline premises of (a) because the
      corollary takes them separately; `hFormU` (uniform: every thread
      coincides with `t₀`) is stronger than `hForm` (existential per thread)
      and feeds only this leg.

    Every premise below is load-bearing: each occurs in the proof term applied
    to one of the reused lemmas, so deleting any premise breaks elaboration.
    There is no `have _ :=` discard anywhere in the proof. The older variants
    (`ziel_nutzer_last`, `ziel_seqLogic_aus_spec`,
    `ziel_seqLogic_aus_spec_invariantForm`) stand untouched as corollaries and
    steps. -/

/-- The goal from discipline (z03): the `ziel_nutzer_last` conclusion with `hInv`
    derived from entry plus return-restoration plus watch
    (`invariantenKontext_aus_disziplin`, §21), `hFree` replaced by `hForm` for
    the invariant fragment (through the §7 variant
    `ziel_seqLogic_aus_spec_invariantForm`), and the CSL-exact LockFrei-gated
    reading as its own leg (`interferenceFree_wo_frei`, §21). Every premise is
    load-bearing -- each is applied in the proof term below. -/
theorem ziel_nutzer_last_aus_disziplin (o : Ausgang V l Γ)
    (run : Lauf D) (voll : Faden → List (Ereignis D))
    (hvoll : ∀ f, ∃ a b : World D, a.spur = [] ∧ Brav a b ∧ b.spur = voll f)
    (hvers : IstVerschraenkung run voll)
    (hausschluss : ForeignExclusion (D := D) run)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code run))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (carrier : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      run[i]? = some (Schritt.mk f ei) → run[j]? = some (Schritt.mk g ej) →
      ei.traeger = some carrier → ej.traeger = some carrier →
      (match carrier with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hLink : J.l = run)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (t₀ : D.Tab) (L : D.Lock)
    (WcL : D.Tab → Bool) (GcL : D.Glob → Bool)
    (hAbL : HaengtAb WcL GcL (I.inv (.inl t₀)))
    (hFrameTL : ∀ t : D.Tab, WcL t = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inl t)
    (hFrameGL : ∀ x : D.Glob, GcL x = true → (.inl t₀ : D.Tab ⊕ D.Glob) = .inr x)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hEntryL : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → I.inv (.inl t₀) σ₀)
    (hReturnL : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
        J.welten[k + 1]? = some nach → TraegerSchreibt (J.code g) (.inl t₀) = true →
          L ∈ D.haelt (J.code g) → I.inv (.inl t₀) nach)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hFormU : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ : World D),
      SpecQ Pre Post Nb J f σ ↔ I.inv (.inl t₀) σ)
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet J.l)
    ∧ ((∀ f j, Konsistent (run.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ run.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ (∀ (f : Faden), f ∈ J.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World D),
      g ∈ J.faeden → g ≠ f →
        J.schrittFaden[k]? = some g → J.welten[k]? = some vor →
          J.welten[k + 1]? = some nach →
            LockFrei (D := D) L vor → LockFrei (D := D) L nach →
              (SpecQ Pre Post Nb J f vor ↔ SpecQ Pre Post Nb J f nach)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLink]
    exact bruecke_exec_gesittet run voll hvoll hvers hausschluss code hEin hungeteilt
  · exact lauf_aus_brav run voll hvoll hvers
  · intro σ hletzte f hf
    exact ziel_seqLogic_aus_spec_invariantForm Nb J I Pre Post
      (invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD hGuardEx
        hEntry hReturn hWatch)
      hDeck hAb hSpec hForm σ hletzte f hf
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o
  · intro f hf k g vor nach hgm hne hkg hkv hkn hFreiVor hFreiNach
    exact interferenceFree_wo_frei Nb J I (SpecQ Pre Post Nb J) t₀ L WcL GcL
      hAbL hFrameTL hFrameGL hGuardT hEntryL hReturnL hCov hFormU
      f hf k g vor nach hgm hne hkg hkv hkn hFreiVor hFreiNach

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_disziplin

/-! ## 9. The goal from the machine: no bare run-side links (m02, 2026-09-11)

    What `ziel_nutzer_last` (§5) still owes on the run side, and what this
    section stops owing. The §5 bridge leg proves `Gesittet J.l` by rewriting
    the bare link `hLink : J.l = run` and applying `bruecke_exec_gesittet`,
    which takes the bare cross-thread shapes `hEin` (W4) and `hungeteilt`
    (W5) beside per-thread provenance (`hvoll`) and interleaving (`hvers`).
    This section replaces that whole premise bundle with one machine run:

    * (M) `M : MaschinenLauf D` (m01 `Maschine.lean`, consumed by
      fast-forward to `cd6e549`, file untouched) IS a reachable run: started
      threads (`hvoll`, closed per body by `exec_spur`), scheduler
      interleaving (`hvers`), the scheduler rule (W3, `hausschluss`), the
      single-thread construction (W4, `hEin` over the projected run), and the
      declaration side (W5, `hungeteilt`). There is no other way to build one.
    * (link) `hLink` is gone: the run side needs no equality and no
      `SerialLink` — `M.run` IS the run. The chain side (`J`, kept for the
      sequential-logic leg) is tied to the machine run only through the open
      chain-to-machine wiring booked below; nothing here asserts that link.
    * (W4) `hEin` is gone as a bare shape: W1, W2, and W4 come from
      `w1w2w4_aus_maschine` (grammar side plus construction), and the whole
      bundle from `gesittet_aus_maschine`. Where a `Verlauf` stands behind
      the run, the one-line closer is `einfaedig_aus_verlauf_getragen` (z05,
      `Marken.lean`): a carried projection IS the `hEin` shape — cited, not
      re-proved.
    * (W5) `hungeteilt` is gone as a bare shape: it travels inside `M` and is
      consumed by `gesittet_aus_maschine`, exactly as the bridge books the
      declaration side. The folded-run closer is `ungeteilt_aus_lauf` (z06,
      `Geteilt.lean` §11, narrowed to split-carrier closed-world runs) —
      cited, not re-proved; the run-to-`Bau` wiring across the fold (cut C2)
      stays open.
    * (worlds) Event-to-world is derived, not asserted: `maschinenWelten`
      folds the run's own events onto the start world, with length,
      last-spur, and goodness lemmas. This closes the step the §22 remainder
      books as open ("no event-to-world step semantics is built ... the
      bodies contribute worlds") — closed here for run worlds.
    * (order) Real reduction is derived, not linked: `reduktion_maschine`
      orders two conflicting accesses in `M.run` via `reduktion_seriell`
      with machine-derived `Gesittet` — no chain object, no `SerialLink`
      premise. Narrowing carried explicitly, never widened: single shared
      TABLE carrier (globals stay on the §§13-15 exception track), two
      conflicting accesses at order level (no folded global schedule, no
      observation equality — `mover_nonwriter_past` and `wache_aus_schuld`
      both take a `GemeinsamerLauf`, which the machine does not supply).
    * (discipline) No assumed context: the strong `hInv : InvariantenKontext`
      (the invariant at EVERY chain world) is DERIVED, not assumed, from
      entry (`hEntry`), return-restoration (`hReturn`), and the single watch
      premise per carrier (`hWatch`) via `invariantenKontext_aus_disziplin`
      (§21, read-only reuse) — the §8 discipline package
      (`ziel_nutzer_last_aus_disziplin` shape: `Wc`/`Gc` frame-locality
      `hAbD`, carrier-frame links `hFrameTD`/`hFrameGD`, guard existence
      `hGuardEx`). The r03 fix (2026-09-11): the first §9 cut kept the §5
      `hInv` premise beside the machine legs — a regression against the
      discipline package that rounds legs 1-2 closed.
    * (form) No per-run interference proof for the covered fragment: the
      general `hFree : InterferenceFree` is replaced by `hForm :
      InvariantForm` (OWN-LOGIC: exhibit, per thread, the carrier whose
      invariant the contract conjunction coincides with), consumed through
      the §7 variant `ziel_seqLogic_aus_spec_invariantForm` (read-only
      reuse). Assertions over shared carriers that are NOT in invariant
      form still owe `hFree` exactly as §6 books it — the non-invariant
      fragment stays open, honestly.

    Every premise below is load-bearing: each is passed whole to at least one
    lemma application in the proof term, so deleting any premise breaks
    elaboration. There is no `have _ :=` discard anywhere in the proof. The
    older variants (`ziel_nutzer_last`,
    `ziel_nutzer_last_aus_disziplin`) stand untouched as corollaries and
    steps.

    Remainder (booked, not hidden): the chain-to-machine wiring (`J.welten`
    versus `maschinenWelten M`); the `Verlauf` behind `M.hEin`
    (`Getragen`/`SpurLink` — no sentence reads a `Verlauf` off an `exec`
    outcome); the run-to-`Bau` wiring across the fold (cut C2); shared
    globals, more than two conflicting sections, restoring writers, and
    the non-invariant fragment — assertions over shared carriers NOT in
    invariant form still owe `hFree` exactly as §6 books it (inherited from
    the §22 remainder unchanged). -/

/-- The goal from the machine (m02, r03 rewired): the `ziel_nutzer_last`
    conclusion with the bare run-side links replaced — `hLink`/`hEin`/
    `hungeteilt` are gone, `M : MaschinenLauf D` travels instead, consumed
    by the machine theorems (`gesittet_aus_maschine`,
    `w1w2w4_aus_maschine`, `maschinenWelten_*`, `reduktion_maschine`). The
    sequential-logic leg runs through the §7 invariant variant
    (`ziel_seqLogic_aus_spec_invariantForm`) over the §8 discipline-derived
    context (`invariantenKontext_aus_disziplin`): `hFree` replaced by `hForm`,
    `hInv` derived from entry plus return-restoration plus watch. Probe,
    lowering, and outcome legs are unchanged from §5. Every premise is
    load-bearing. -/
theorem ziel_nutzer_last_aus_maschine (o : Ausgang V l Γ)
    (M : MaschinenLauf D)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.run[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.run[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂)))
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet M.run)
    ∧ ((∀ f j, Konsistent (M.run.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ M.run.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ ((maschinenWelten M).length = M.run.length + 1)
    ∧ (((maschinenWelten M).getLast?.map World.spur) =
      some ((M.run.map Schritt.ereignis).reverse ++ M.start.spur))
    ∧ (∀ W ∈ maschinenWelten M, ∀ e ∈ W.spur, e ∈ M.start.spur ∨ e.gut)
    ∧ (HB M.run j₁ j₂ ∨ HB M.run j₂ j₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gesittet_aus_maschine M
  · exact ⟨(w1w2w4_aus_maschine M).1, (w1w2w4_aus_maschine M).2.1⟩
  · intro σ hletzte f hf
    exact ziel_seqLogic_aus_spec_invariantForm Nb J I Pre Post
      (invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD hGuardEx
        hEntry hReturn hWatch)
      hDeck hAb hSpec hForm σ hletzte f hf
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o
  · exact maschinenWelten_laenge M
  · exact maschinenWelten_letzte_spur M
  · exact maschinenWelten_gut M
  · exact reduktion_maschine M t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_maschine

/-! ## 9b. The goal from PC runs: no deprecated fields, no bare shapes (t01, 2026-09-11)

    What `ziel_nutzer_last_aus_maschine` (§9 m02) still owes on the run side, and
    what this section stops owing. The m02 leg proves `Gesittet M.run` from
    `M : MaschinenLauf D` -- the DEPRECATED structure (`Maschine.lean` §§1-5,
    kept byte-identical for its consumer): reachability handed as premises, with
    `hEin` (W4) and `hungeteilt` (W5) as FIELDS. The §12 PC discharge
    (`pc_discharge_einfaedig`, `pc_discharge_unshared`, genuinely proved) is not
    wired in there: no `PCReach`-to-`MaschinenLauf` bridge exists, and §9 takes
    no `PCReach`. This section rewires the goal onto generated PC runs:

    * (run) `h : PCReach P O passes prog (GenStart sp) M pc` travels instead of
      `M : MaschinenLauf D` -- a GENERATED run (positions with footprints,
      `Maschine.lean` §12, read-only reuse): every `PCSchritt` is a generated
      step (`pcSchritt_gen`), every PC-reachable machine is generated
      (`pcReach_gen`). There is no other way to build one.
    * (W4) `hEin` is gone as a bare shape AND as a field: the projection premise
      discharges from program text (`pc_discharge_einfaedig`, consumed below as
      its own leg over `pcReach_markInv`), and the whole bundle closes to
      `Gesittet` (`pc_gesittet`, consumed below).
    * (W5) `hungeteilt` is gone as a bare shape AND as a field: the declaration
      side discharges from carrier separation (`pc_discharge_unshared`,
      consumed below as its own leg over `pcReach_carrierInv`, with the
      shared-side hypothesis before the access equations as §12 states it).
    * (order) `pc_reduktion` runs the serial order on the PC run (consumed
      below) -- the same two-access single-carrier fragment as
      `reduktion_maschine`, with `Gesittet` derived from positions, never
      assumed.
    * (worlds) The live-memory history `M.welten` travels instead of the
      constant-memory fold: `genWelten_laenge` (one world per step),
      `genWelten_gut` (good observations), `genWelten_letzte` (the last world
      is a thread world) -- each through the projection (`pcReach_gen`), never
      re-proved. This escapes the NEGATIVE shape
      `maschinenWelten_speicher_gleich` by construction (`gen_welt_speicher_bewegt`
      moves memory on a fireable write; §12 is read, not modified).
    * (discipline, form, probe, lowering, outcome) Unchanged from §§7-8 and §5:
      the sequential-logic leg runs through the §7 invariant variant
      (`ziel_seqLogic_aus_spec_invariantForm`) over the §8 discipline-derived
      context (`invariantenKontext_aus_disziplin`); `hFree` is replaced by
      `hForm` for the covered fragment only.

    The SINGLE residual footprint premise: `h` itself. Each `PCSchritt.leaf`
    inside `h` carries its footprint checks (`hΛa` tying the atom to the fired
    statement, `hmark` covering the step's mark namings, `hcar` covering the
    step's accessed carriers) -- they are owed per step by whoever exhibits the
    `PCReach` witness, not by this goal as separate hypotheses. No tree
    definition computes thread programs from bodies yet (there is no `progAus`:
    `Extraktion.lean` computes carrier/mark hulls (`fussAus`, `stmtOrte`)
    checker-side, but not per-thread atom sequences; the `HaengtAb` duty of §8
    covers contract footprints, not step atoms), so per program the annotation
    is owed as OWN-LOGIC: the user supplies, per thread, the atom footprint
    sequence (`prog`, with `Λa`/`cs` covering the step events); each step rule
    verifies it. The checker-side extraction of `prog` from bodies stays booked
    below. There is exactly one such premise (`h`), and it is load-bearing --
    it feeds every run-side leg.

    Every premise below is load-bearing: each is passed whole to at least one
    lemma application in the proof term, so deleting any premise breaks
    elaboration. There is no `have _ :=` discard anywhere in the proof, and no
    bare `Prop` slot that `False` could inhabit (every slot has a fixed shape:
    the run is owed as `PCReach ...`, not as `Prop`). The older variants
    (`ziel_nutzer_last`, `ziel_nutzer_last_aus_disziplin`,
    `ziel_nutzer_last_aus_maschine`) stand untouched as corollaries and steps.

    Remainder (booked, not hidden): the checker-side extraction of `prog` from
    bodies (a `progAus` in the style of `Extraktion.lean`, unwritten and
    unverified); the chain-to-machine wiring (`J.welten` versus `M.welten`);
    the run-to-`Bau` wiring across the fold (cut C2); shared globals, more than
    two conflicting sections, restoring writers; and the non-invariant fragment
    -- assertions over shared carriers NOT in invariant form still owe `hFree`
    exactly as §6 books it (inherited from the §8 remainder unchanged). -/

/-- The goal from PC runs (t01): the `ziel_nutzer_last` conclusion with the
    deprecated run-side bundle replaced -- no `MaschinenLauf`, no `hLink`,
    no `hEin`/`hungeteilt` as bare shapes or fields. `h : PCReach ...` travels
    instead (packaging the per-step `hmark`/`hcar` footprint checks), consumed
    by the PC theorems (`pc_gesittet`, `pc_discharge_einfaedig`,
    `pc_discharge_unshared`, `pc_reduktion`) and the generated-world lemmas
    through the projection (`pcReach_gen`). The sequential-logic leg runs
    through the §7 invariant variant
    (`ziel_seqLogic_aus_spec_invariantForm`) over the §8 discipline-derived
    context (`invariantenKontext_aus_disziplin`): `hFree` replaced by `hForm`,
    `hInv` derived from entry plus return-restoration plus watch. Probe,
    lowering, and outcome legs are unchanged from §5. Every premise is
    load-bearing. -/
theorem ziel_nutzer_last_aus_pc (o : Ausgang V l Γ)
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc)
    (code : D.Marke → Nat) (hMSep : PCMarkSep code prog)
    (hCSep : PCUnsharedSep prog)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (Wc : (c : D.Tab ⊕ D.Glob) → D.Tab → Bool)
    (Gc : (c : D.Tab ⊕ D.Glob) → D.Glob → Bool)
    (hAbD : ∀ c, HaengtAb (Wc c) (Gc c) (I.inv c))
    (hFrameTD : ∀ (c : D.Tab ⊕ D.Glob) (t : D.Tab), Wc c t = true → c = .inl t)
    (hFrameGD : ∀ (c : D.Tab ⊕ D.Glob) (x : D.Glob), Gc c x = true → c = .inr x)
    (hGuardEx : ∀ c : D.Tab ⊕ D.Glob, ∃ L : D.Lock, Bewacht (D := D) c L)
    (hEntry : ∀ (c : D.Tab ⊕ D.Glob) (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀)
    (hReturn : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g) → I.inv c nach)
    (hWatch : ∀ (c : D.Tab ⊕ D.Glob) (L : D.Lock) (k : Nat) (g : Faden)
      (vor nach : World D),
      Bewacht (D := D) c L → g ∈ J.faeden → J.schrittFaden[k]? = some g →
        J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
          TraegerSchreibt (J.code g) c = true → L ∈ D.haelt (J.code g))
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂)))
    (S : Nat) (c : TickClock S) (hstart : c.tick 0 ≤ S)
    (p : PruefPaar) (fr : Frist D) (d : Moment)
    (hpd : p.pruef < d) (hdl : d < p.lauf)
    (hspace : deadlineSpacing S p d)
    (hLowering : Absenkung) :
    (Gesittet M.lauf)
    ∧ ((∀ f j, Konsistent (M.lauf.spur f j)) ∧
      ∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut)
    ∧ (∀ (σ : World D), J.welten.getLast? = some σ →
      ∀ (f : Faden), f ∈ J.faeden → SpecQ Pre Post Nb J f σ)
    ∧ (∃ n, d ≤ c.tick n ∧ c.tick n ≤ p.lauf ∧
      fristErgebnis (fristlauf p fr (some d)) = some (.fortschritt fr.annahme))
    ∧ (hLowering.proPrimitiv ≤ 18)
    ∧ ((∃ σ ρ, o = .ok σ ρ) ∨ (∃ σ v, o = .zurueck σ v) ∨ (∃ σ r, o = .grund σ r) ∨
      (∃ h σ ρ, o = .leave h σ ρ) ∨ (∃ h σ ρ, o = .next h σ ρ) ∨
      (∃ e : Logik D, o = .logik e) ∨ (∃ e : Hardware D, o = .hardware e))
    ∧ (Marken.Einfaedig (laufProj code M.lauf))
    ∧ (∀ (i j : Nat) (f g : Faden) (carr : D.Tab ⊕ D.Glob) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      (match carr with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) →
      ei.traeger = some carr → ej.traeger = some carr → f = g)
    ∧ (M.welten.length = M.tiefe + 1)
    ∧ (∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut)
    ∧ (∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f)))
    ∧ (HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pc_gesittet P O passes hO prog sp M pc h code hMSep hCSep
  · exact ⟨pc_konsistent P O passes hO prog sp M pc h,
      pc_gut_obs P O passes hO prog sp M pc h⟩
  · intro σ hletzte f hf
    exact ziel_seqLogic_aus_spec_invariantForm Nb J I Pre Post
      (invariantenKontext_aus_disziplin Nb J I Wc Gc hAbD hFrameTD hFrameGD hGuardEx
        hEntry hReturn hWatch)
      hDeck hAb hSpec hForm σ hletzte f hf
  · exact sampling_closes_frist (S := S) c hstart p fr d hpd hdl hspace
  · exact hLowering.begrenzt
  · exact zwei_fehler o
  · exact pc_discharge_einfaedig code prog M
      (pcReach_markInv P O passes prog sp M pc h) hMSep
  · intro i j f g carr ei ej hi hj hsh hti htj
    exact pc_discharge_unshared prog M
      (pcReach_carrierInv P O passes prog sp M pc h) hCSep
      i j f g carr ei ej hi hj hsh hti htj
  · exact genWelten_laenge P O passes hO sp M
      (pcReach_gen P O passes prog (GenStart sp) M pc h)
  · exact genWelten_gut P O passes hO sp M
      (pcReach_gen P O passes prog (GenStart sp) M pc h)
  · exact genWelten_letzte P O passes hO sp M
      (pcReach_gen P O passes prog (GenStart sp) M pc h)
  · exact pc_reduktion P O passes hO prog sp M pc h code hMSep hCSep
      t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

#print axioms Gabbro.Grammatik.ziel_nutzer_last_aus_pc

end Gabbro.Grammatik
