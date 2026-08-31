# Die Namen, die der Erzeuger selbst bildet — und wo zwei davon aufeinandertreffen

**Gemessen am 2026-08-31**, lokal (`free -g`: 31 GB gesamt, 18 verfügbar, 20 Kerne).
`cc` ist `gcc`, gefahren als `cc -std=c11 -O0 -Wall -Wextra -Werror -c`.

`beispiele/gift/413-format-feld-heisst-gueltig.gab` nennt **zwei** Formen. Der W24-Vorlauf
hat die Familie ausgemessen: es sind **neun**, und eine zehnte fällt ausdrücklich *nicht*.

*Eine Absage, die nur `gueltig` kennt, verschiebt den Fehler auf das nächste Wort.*

---

## §1 Die Namensmuster, aus `emit.rs` gelesen

`N041` (`cnamen.rs`) hält die Namen, die **C** vergeben hat. Diese Tafel hält die, die
**Gabbro selbst** bildet — aus einem Nutzernamen und einem festen Anhang. Alle Zeilen sind
`grep`-Treffer in `crates/gabbro-check/src/emit.rs`.

| Träger | gebildeter C-Name | Stelle |
|---|---|---|
| `format F` | `F` (Verbund) | :3032 |
| `format F`, Feld `f` | `F_f` (Leser) | :3077, :3297 |
| `format F`, Feld `f` | `F_setz_f` (Schreiber, nur ohne `scale`) | :3085, :3312 |
| `format F` | `F_gueltig` (Prüfkörper) | :3374 |
| `tagged type T`, Variante `v` | `T_v` (Aufzählungswert) | :2185 |
| `tagged type T` | `T_marke` (Aufzählung), `T` (Verbund) | :2185, :2204 |
| `table T` | `T_slot`, `T` | :2232, :2236 |
| `table T` | `T_speicher` (nur wenn beim Namen genannt) | :2244 |
| `table T` | `T_NONE` (nur wenn `count < 2^32`) | :2263 |
| `table T`, `ops` | `T_insert`, `T_remove` | :2369, :2395 |
| `reason R`, Fall `c` | `R_c`, `R` | :1881 |
| `device D` | `D` (Griff) | :2565 |
| `device D`, `bank B`, Register `r` | `D_B_r`, `D_B_setz_r` | :2610, :2622 |
| `device D`, `transition x` | `D_x` | :2862 |
| `lock L` | `L_nimm`, `L_gib`, (`L_nimm_geteilt`, `L_gib_geteilt`) | :1845, :1851 |
| `rcu N` | `N_lese_start`, `N_lese_ende` | :1932 |
| `atomic A` | `A`, `A_ORDER` | :1812 |
| `walk W` | `W_EBENEN`, `W_WEITE`, `W_knoten`, `W_ist_blatt`, `W_steigt_ab`, `W_absteigen` | :8253–:8266 |
| `entry e` | `gabbro_eintritt_e`, `gabbro_eintritt_e_VEKTOR`, `gabbro_eintritt_e_verteiler` | :8382–:8390 |
| `boot b`, Schritt `s` | `gabbro_boot_b_s`, `gabbro_boot_b_s{i}` | :8540 |
| Blockmarke `m` | `m_wachhund` | :6107 |

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
