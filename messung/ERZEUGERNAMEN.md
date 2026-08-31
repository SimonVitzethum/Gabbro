# Die Namen, die der Erzeuger selbst bildet — und wo zwei davon aufeinandertreffen

**Gemessen am 2026-08-31**, lokal (`free -g`: 31 GB gesamt, 18 verfügbar, 20 Kerne).
`cc` ist `gcc`, gefahren als `cc -std=c11 -O0 -Wall -Wextra -Werror -c`.

`beispiele/gift/413-format-feld-heisst-gueltig.gab` nennt **zwei** Formen. Der W24-Vorlauf
hat die Familie ausgemessen: es sind **neun**, und eine zehnte fällt ausdrücklich *nicht*.

*Eine Absage, die nur `gueltig` kennt, verschiebt den Fehler auf das nächste Wort.*

> **BERICHTIGT AM 2026-08-31 — `messung/STILLE-KOLLISIONEN.md` hat die Familie nachgezählt,
> und die Einteilung dieses Dokuments stimmt nicht.**
>
> * **Die zehnte ist nicht die einzige stille.** Ob `cc` spricht, hängt an drei Dingen, und
>   keines davon ist die Kollision: verträgliche Typen, höchstens eine Definition — und die
>   **Reihenfolge**. C11 6.2.2p4: eine nicht-statische Deklaration *nach* einer statischen
>   erbt die interne Bindung, andersherum ist es ein Fehler. *Dieselben zwei
>   Gabbro-Deklarationen, zwischen zwei Zeilen getauscht, geben `cc` exit 0 und exit 1.*
> * **§2 Fall 9 ist nur zufällig laut.** `format Eintrag { a … }` neben `extern fn
>   Eintrag_a` mit **passender** Signatur übersetzt sauber, und der erzeugte Leser
>   beantwortet den Ruf des Schreibers (gemessen: 42 statt der 999 aus seiner Bibliothek).
>   Die anderen acht sind *strukturell* laut.
> * **§7 letzter Punkt stimmt** — `N042` fängt die zehnte Form —, aber **die Aufzählung war
>   an sechs Stellen unvollständig und an drei zu weit**; beides ist am 2026-08-31 geheilt
>   und dort gemessen. `{Atomic}_ORDER`, `gabbro_eintritt_{e}_VEKTOR` und
>   `gabbro_boot_{b}_s{i}` stehen jetzt unter ihrer Bedingung.
> * **§6 nennt 426 Dateien.** Der Baum hält heute 446, und die Regel hat elf Treffer:
>   `gift/413`, die vier neuen Proben `417`–`420` und sechs Messdateien.
>
> *Die Tafel in §1 und die neun Formen in §2 bleiben, wie sie dastehen — sie sind gemessen.
> Was sich geändert hat, ist ihre Einteilung.*

---

## §1 Die Namensmuster, aus `emit.rs` gelesen

`N041` (`cnamen.rs`) hält die Namen, die **C** vergeben hat. Diese Tafel hält die, die
**Gabbro selbst** bildet — aus einem Nutzernamen und einem festen Anhang. Alle Zeilen sind
`grep`-Treffer in `crates/gabbro-check/src/emit.rs`.

| Träger | gebildeter C-Name | Stelle |
|---|---|---|
| `format F` | `F` (Verbund) | :3064 |
| `format F`, Feld `f` | `F_f` (Leser) | :3109, :3329 |
| `format F`, Feld `f` | `F_setz_f` (Schreiber, nur ohne `scale`) | :3117, :3344 |
| `format F` | `F_gueltig` (Prüfkörper) | :3406 |
| `tagged type T`, Variante `v` | `T_v` (Aufzählungswert) | :2185 |
| `tagged type T` | `T_marke` (Aufzählung), `T` (Verbund) | :2185, :2204 |
| `table T` | `T_slot`, `T` | :2232, :2236 |
| `table T` | `T_speicher` (nur wenn beim Namen genannt) | :2244 |
| `table T` | `T_NONE` (nur wenn `count < 2^32`) | :2263 |
| `table T`, `ops` | `T_insert`, `T_remove` | :2369, :2394 |
| `reason R`, Fall `c` | `R_c`, `R` | :1881 |
| `device D` | `D` (Griff) | :2597 |
| `device D`, `bank B`, Register `r` | `D_B_r`, `D_B_setz_r` | :2642, :2654 |
| `device D`, `transition x` | `D_x` | :2894 |
| `lock L` | `L_nimm`, `L_gib`, (`L_nimm_geteilt`, `L_gib_geteilt`) | :1846, :1851 |
| `rcu N` | `N_lese_start`, `N_lese_ende` | :1932 |
| `atomic A` | `A`, `A_ORDER` | :1812 |
| `walk W` | `W_EBENEN`, `W_WEITE`, `W_knoten`, `W_ist_blatt`, `W_steigt_ab`, `W_absteigen` | :8337 ff. |
| `entry e` | `gabbro_eintritt_e`, `gabbro_eintritt_e_VEKTOR`, `gabbro_eintritt_e_verteiler` | :8466 ff. |
| `boot b`, Schritt `s` | `gabbro_boot_b_s`, `gabbro_boot_b_s{i}` | :8624 |
| Blockmarke `m` | `m_wachhund` | :6191 |

> **Die Nummern sind die des Standes `26cd71f`** — nach den zwei Portraum-Absagen, die
> `emit.rs` um 83 Zeilen verlängert haben. *Eine Zeilennummer ist eine Jahreszahl; der `grep`
> daneben ist es nicht, und darum steht in jeder Zeile das Muster und nicht nur die Zahl.*

**Es gibt keine Umbenennung dazwischen.** `cnamen.rs` sagt es in seiner ersten Zeile: *„there
is no `fn c_name` in `emit.rs`"*. Was in Gabbro steht, steht in C — plus einem Anhang.

## §2 Neun gemessene Kollisionen

Je Klasse eine Probe, alle drei Werkzeuge gefahren. **Alle neun prüfen mit `0 Fehlern,
0 Hinweisen`, emittieren ohne `C001`, und `cc` weist sie ab.**

| # | die zwei Namen | wie geschrieben | `cc` sagt |
|---|---|---|---|
| 1 | `F_gueltig` × Leser | Feld heisst `gueltig` | *Redefinition von »Eintrag_gueltig«* |
| 2 | `F_setz_a` × Leser | Feld `setz_a` neben Feld `a` | *conflicting types for »Eintrag2_setz_a«* |
| 3 | `T_marke` × Aufzählungswert | Variante heisst `marke` | *»Nachricht_marke« als andere Symbolart redeklariert* |
| 4 | `T_slot` × Tabellenverbund | `table Kappe` neben `table Kappe_slot` | *abweichende Typen für »Kappe_slot«* |
| 5 | `R_c` × Konstante | `reason Fehler { Leer … }` neben `const Fehler_Leer` | *expected identifier before numeric constant* |
| 6 | `D_B_setz_r` × Bankleser | Register `setz_LO` neben Register `LO` | *abweichende Typen für »Vtd_FRR_setz_LO«* |
| 7 | `W_knoten` × Verbund | `walk Baum` neben `type Baum_knoten` | *abweichende Typen für »Baum_knoten«* |
| 8 | `T_NONE` × Konstante | `table Kappe` neben `const Kappe_NONE` | *»Kappe_NONE« redefiniert* |
| 9 | `F_f` × Funktion | `format Eintrag { a … }` neben `extern fn Eintrag_a` | *abweichende Typen für »Eintrag_a«* |

Die Proben stehen als `beispiele/gift/413…` (1, 2) und in `messung/proben/`.

## §3 Die zehnte fällt NICHT — und sie ist die unheimliche

```gabbro
static mut zaehler : u32 = 0;
lock TOR protects { zaehler } rank 0 held <= 8 ops;
extern fn TOR_nimm() effects { writes zaehler };
```

`cc` sagt **nichts**: `void TOR_nimm(void);` zweimal mit demselben Typ ist in C eine
zulässige Wiederholung. **Und genau darum ist es schlimmer als die neun darüber.** Zwei
Gabbro-Deklarationen werden zu *einem* Symbol; der Ruf der Sperre landet beim Binden in der
fremden Funktion, und kein Werkzeug in der Kette sagt ein Wort.

*Die neun fallen bei `cc`; diese neunte-plus-eins fällt nirgends.* Ein Prüfer, der nur
nachbaut, was `cc` schon findet, findet sie nicht.

## §4 Zwei Sorten, ein Satz

Die neun zerfallen in zwei Sorten:

* **Innerhalb eines Trägers** (1, 2, 3, 6): zwei *Anhänge* desselben Trägers treffen sich,
  weil ein Feld- oder Variantenname zufällig wie ein Anhang aussieht.
* **Über zwei Trägern** (4, 5, 7, 8, 9): ein *zweiter Gegenstand* heisst genau so, wie der
  Erzeuger den ersten benennt.

**Beide sind derselbe Satz:** *zwei verschiedene Gabbro-Deklarationen bekommen denselben
C-Namen.* Und daraus fällt die Bauform: nicht eine Liste verbotener Wörter, sondern die
**Aufzählung der gebildeten Namen und die Suche nach Doppelungen darin.**

Eine Wortliste wäre falsch in beide Richtungen zugleich. Sie verböte `gueltig` als Feldnamen
auch dort, wo kein `format` in der Nähe ist — und sie kennte `Kappe_NONE` nicht, weil das
Wort erst mit der Tabelle daneben entsteht.

## §5 Was `namen.rs` heute schon hält — und warum es nicht reicht

* **`geltungsbereich`** fängt *zwei gleiche* Gabbro-Namen. Keiner der neun Fälle ist einer:
  `Kappe` und `Kappe_NONE` sind verschieden, `a` und `setz_a` sind verschieden.
* **`N041`** fängt Namen, die *C* vergeben hat. `gueltig`, `marke`, `slot`, `NONE` sind
  keine — `messung/C-NAMEN.md` misst 558 Namen, und kein einziger davon steht oben.

*Der eine Pass misst die fremden Namen, der andere die doppelten. Die gebildeten misst
keiner.*

## §6 Was die Regel kostet, über den ganzen Korpus (Regel A)

`gabbro pruefe` über alle **426** `.gab`-Dateien, mit dem gebauten `N042`:

```
---- 426 Dateien, 1 mit N042 ----
== beispiele/gift/413-format-feld-heisst-gueltig.gab
error: [N042] …:61:5: `Eintrag2_setz_a` is the C name of two different declarations
error: [N042] …:54:5: `Eintrag_gueltig` is the C name of two different declarations
```

**Ein Treffer, und es ist die Probe, für die die Regel geschrieben wurde** — beide Formen,
beide an der Feldzeile, die sie verursacht.

### Der erste Lauf meldete ACHT, und die anderen sieben haben den Schnitt gezogen

| Datei | was gemeldet wurde | Urteil |
|---|---|---|
| `beispiele/29-undurchsichtig.gab` | `pa_aus_zahl` | **kein Mangel** — `pub impl fn` im einen Modul, `extern fn` im nächsten. Zwei Deklarationen, ein C-Symbol, *mit Absicht*: der Erzeuger schreibt den Prototyp genau einmal, und `cc` nimmt an (nachgemessen) |
| `messung/fragmente/F05.gab` | `invoke` | **kein Mangel** — zweimal `prim fn invoke`, getrennt durch `arch x86_64` / `arch aarch64`. Je Bau wird eine emittiert |
| `gift/06-doppelt`, `gift/31`, `gift/32`, `gift/140`, `gift/274` | `SEITE`, `eng`, `Eng`, `hilf`, `lesen` | **W7** — zwei *gleiche* Gabbro-Namen, und das sagt `geltungsbereich` schon. Ein zweites Register über einer Sache ist ein zweites Register |

Daraus die Verengung, und sie ist gemessen und nicht geraten: **mindestens eine Seite muss
ein Name sein, den der Erzeuger gebildet hat** (`Gebildet::angehaengt`). Zwei gleiche
*erklärte* Namen gehören dem Nachbarpass; wo sie kein Mangel sind, hat diese Regel gar nichts
zu sagen.

*Ohne diese Zeile hätte `N042` in sieben Fällen gesprochen, in denen entweder nichts kaputt
war oder ein anderer Pass schon sprach.* **Genau die Sorte Absage, die in dieser Nacht schon
einmal zurückgenommen werden musste.**

## §7 Was NICHT gebaut wurde, und je ein Grund

* **`{T}_speicher` steht nicht in der Aufzählung.** Der Erzeuger schreibt es nur, wo die
  Quelle die Tabelle beim NAMEN nennt (`emit.rs`:2244, `u.tabellenglobal`) — jene Menge lebt
  in den `Namen` des Erzeugers und nicht im Baum. Ein gelisteter Name, den der Erzeuger nie
  schreibt, wäre eine Absage ohne Mangel. **Der Preis steht als Probe da und nicht in einem
  Absatz:** `beispiele/gift/414-tabellenspeicher-heisst-so.gab`, Vertrag `-- erwartet: cc`.
* **Blockmarken (`{marke}_wachhund`).** Eine Marke ist kein Name des Dateibereichs; zwei
  Funktionen dürfen dieselbe tragen.
* **Rümpfe.** Ein `let` senkt zu einer lokalen Größe ab, und eine lokale, die einen Namen des
  Dateibereichs verdeckt, ist zulässiges C — dieselbe Grenze, die `N041` zieht, und aus
  demselben gemessenen Grund.
* **Eine Regel gegen die zehnte Form aus §3** wurde nicht *zusätzlich* gebaut — `N042` fängt
  sie mit. `lock TOR` neben `extern fn TOR_nimm()` ist `{Lock}_nimm` gegen `{fn}`, also eine
  Seite gebildet, also gemeldet. *Das ist der einzige der zehn Fälle, den `cc` nie gefunden
  hätte.*
