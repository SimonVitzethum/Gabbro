/-
  Datei:      Passlogik/Kosten.lean
  Gegenstand: Die KOSTENRECHNUNG -- `Ĉ` ist eine OBERE Schranke jedes Durchlaufs.

  MODELLIERT WIRD
    Eine Ausdrucks- und Anweisungssprache mit den vier Primitiven aus `LANGUAGE.md` §7,
    die statisch gerechnete Zahl `Ĉ` und eine LAUFRELATION `laeuft s n` ("ein Durchlauf
    durch `s` fuehrt `n` Primitiven aus"). Bewiesen wird L1 aus `messung/K001.md`:
    `Ĉ(b) >= K(b, r)` fuer JEDEN Durchlauf `r`. Dazu L2 (Vergleich bei der kleinsten
    Belegung), die Schleifenmultiplikation und die Komposition von `held`.

  QUELLSAETZE
    dokumente/LANGUAGE.md:940  -- "`costs` counts operations, and the unit is defined:
                                 1 op = one Gabbro primitive (assignment, arithmetic
                                 operation, load, store; a call counts the declared `costs`
                                 of the callee; a traversal counts body costs x domain
                                 bound; branches count the maximum)."
    dokumente/LANGUAGE.md:949  -- "The four primitives are conclusive. An `if`, a `match`,
                                 a `return`, a `leave` cost NOTHING [...] And what is fixed
                                 at compile time costs nothing at run time."
    dokumente/LANGUAGE.md:953  -- "What stands after a branch that ALWAYS leaves lies on the
                                 other path."
    dokumente/LANGUAGE.md:1176 -- §9.3, Punkt 1/4: "Every lock declares `held <= K ops`. A
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


module

public import Passlogik.Kosten.Teil1
public import Passlogik.Kosten.Teil2
