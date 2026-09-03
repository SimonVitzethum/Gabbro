//! **Der Korpuslauf als Test** -- Tor P2, gemessen statt behauptet.
//!
//! Was hier festgehalten wird, ist nicht die *Zahl* der Fehler (die soll fallen), sondern
//! **ihre Art**: jeder Befund am Korpus muss ein Code sein, den dieser Uebersetzer benannt
//! hat. Ein neuer, unbenannter Code ist ein Befund ueber den Uebersetzer, kein Rauschen --
//! und genau so faellt der Test.
//!
//! Die gemessenen Zahlen stehen in `MESSUNGEN.md`, mit Datum. Sie hier zu wiederholen hiesse,
//! eine Zahl an zwei Stellen zu fuehren.

use gabbro_check::korpus;

fn lies(datei: &str) -> String {
    let pfad = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join(datei);
    std::fs::read_to_string(&pfad).unwrap_or_else(|e| panic!("{}: {e}", pfad.display()))
}

/// Jeder Code, den der Korpuslauf hervorbringen darf. Ein Eintrag hier ist eine Aussage:
/// *diese Absage ist gemeint und ihr Text ist geprueft.*
const BENANNT: &[&str] = &[
    "L001", "L002", "L003", "L004", "L005", "L006", // Lexik
    "P001", "P002", "P003", "P004", "P005", "P006", "P007", "P008", "P009", "P010", "P011",
    "P012", "P013", "P014", "P015", "P016", "P017", "P018", "P019", "P020", "P021", "P022",
    "P023", "P024", "P025", "P026", "P027", "P028", "P029", "P030", "P031", "P033", "P034", "P035",
    // `P041` -- split off from `P034` on 2026-08-30. `P034` kept the missing catch-all arm,
    // `P041` took the stray `pub`: two unrelated rules stood under one identifier, and each
    // of their two poison probes would have stayed green while the OTHER rule was out.
    "P032", "P035", "P041", // Grammatik
    "M101", "M102", "M103", "M104", "M105", // M1 + V1-V3
    "N001", "N002", "N003", // Namen
    "S001", "S002", // Schleifen und Kontrollfluss
    // **`progress` bekam am 2026-08-18 seinen ersten Leser** -- und `S003` faellt sofort im
    // Korpus (`FRAGMENTE.md`:887, die `virtq`-Wartestelle). Das ist KEINE Fehlmessung: ein
    // Fragment traegt keine Annahmenschicht, also nennt sein `progress` einen Zeugen, den
    // niemand erklaert. *In einem ganzen Programm waere genau das der Fehler.*
    "S003", "S004",
    // «F»: f32/f64. `F002` trifft das stillschweigend inexakte Literal -- die Regel kam aus
    // dem Korpus (FRAGMENTE.md, «F0»/FF4), nicht aus dem Entwurf.
    "F001", "F002", "F004", "F005", "F006",
    "K001", "K002", "K003", // Kosten
    "E001", "E002", "E003", "E004", "E005", "E006", "E007", "E008", "E009",
    "E010", // Wirkungen -- E010 ist die Lesehaelfte (Lesart A, 2026-08-16)
    "H001", "H002", "H003", "H004", "H005", "H006", // geteilter Halt, Rangordnung
    // K11.2.1: `protects` beisst (`H007`) und eine nie genommene Sperre faellt auf (`H008`).
    "H007", "H008",
    // «K2»: RCU ist keine Sperre -- H009 Leseseite benannt, H010 Schreiber braucht eine.
    "H009", "H010", "H011", "H012",
    // **«ABI», 2026-08-21: `H016` -- a lock name that no declaration explains.** Two sites
    // in the corpus -- `locks SCHEDS` at `FRAGMENTE.md`:652 and `locks CAPS` at
    // `SYNTAX.md`:764 -- and **neither is a mismeasurement**: a fragment is an EXCERPT, and
    // both name locks declared outside the cut. *The same class as `S003` eight lines above
    // -- and in a whole program it would be the error.*
    //
    // It was four until the rule was narrowed the same day: `requires Held(…)` is NOT
    // checked, because `Held(PHASE_ROH)` in F7 names a BOOT PHASE and not a lock. The
    // reasoning stands at the site, in `geteilt.rs`.
    //
    // > The build came from the other side: at a LIBRARY BOUNDARY a lock name from elsewhere
    // > is the normal case, and until this rule it was invisible. The rank rules in the
    // > checker looked the rank up, found nothing and stayed silent -- a ring across two
    // > libraries passed with zero errors (`messung/ABI.md`).
    "H016",
    // «B37» und K11.1: die Ordnung auf einer linearen Geistmarke. `O005` ist ZURUECKGEZOGEN --
    // der Hinweis „dieser Pass entscheidet das nicht" ist durch `O006` ersetzt, und der Code
    // bleibt frei: eine Absage, die heimlich ihre Bedeutung wechselt, ist schlimmer als eine
    // Nummer, die ungenutzt bleibt.
    "O001", "O002", "O003", "O004", "O006",
    // «C3a», 2026-08-20: der Fehlerkanal `-> T or R`. `N028` -- ein `let … else` ueber einer
    // Funktion, die nicht scheitern kann; `N029` -- ein Ruf auf eine, die es kann, ausserhalb
    // eines `let … else`. Die beiden sind einander die Gegenprobe.
    "N028", "N029",
    // 2026-08-20, gefunden beim SCHREIBEN von Caprocks Blockiergruenden: am Ruf wird der
    // Bereich gehalten und der NAME nicht. `N030` -- `opaque`, `linear`, `ghost` und
    // `tagged` sind nominal.
    "N030",
    // «V9», 2026-08-20: `observed by <assume>` -- die Gegenseite der Paarung steht in
    // Silizium. `N031` haelt die Klausel gegen die Annahmenschicht, damit sie kein
    // Schlupfloch mit einem Namen darauf wird.
    "N031",
    // 2026-08-20, gefunden von `pruefe-reichweite.py`: zwei Item-Arten mit einem RUMPF, den
    // genau ein Pass kannte. `N032` die `where`-Klausel eines `format`, `N033`/`O007` die
    // Schritte einer Bootstrecke -- das Konstrukt, das fuer die Reihenfolge da ist, prueft
    // seine eigene nicht.
    "N032", "N033", "O007",
    // «B41b», 2026-08-20: die Baumkante an der `table`. `D006` das Feld, `D007` sein Typ,
    // `D008` seine Tabelle.
    "D006", "D007", "D008",
    // 2026-08-31: the same three questions at the CHAIN edge, which `chain(a, b) in`
    // names at the walk instead of at the declaration. `messung/DOMAENENNAMEN.md`.
    "D014", "D015", "D016",
    // **2026-08-31: a probe yields a VERDICT, and on every path.** `N044` a `return` with
    // no value in a `can_fail` block, `N045` a path that reaches the closing brace. Six of
    // the twelve files in `messung/tor-proben/` emitted C that `cc` refused, and no stage
    // before `cc` said a word. `messung/TORREICHWEITE.md`.
    "N044", "N045",
    // 2026-08-31, one measurement later: the PLACE of a quantifier domain. `D017` its base
    // name -- `messung/DOMAENENSTELLUNGEN.md` falsified each of the 53 corpus sites outside
    // `ensures` one by one and 51 stayed silent -- and `D018` its KIND: `slots of` needs a
    // table, `queue` a record, `elems of` an array field, `mappings of` a `walk`.
    "D017", "D018",
    // 2026-08-31, the third question at the same place: `D017` reads its BASE name, `D018`
    // its KIND, and `D019` the FIELD names of its suffix. Measured at
    // `messung/proben/probe-elems-feldname.gab`: `elems of r.gibtsnichtfeld` falsified in
    // three positions gave `0 errors, 0 hints` -- `ensures` among them, so `M109` did not
    // read it either. The control in the same run: the same place with a falsified BASE
    // name does fall, at `M109`. *The base is read and the field is not.*
    "D019",
    // 2026-09-01, the fourth question at the same place and the first about the VARIABLE.
    // `D017`/`D018`/`D019` all stop at the PLACE; `mappings of` is the one domain that binds
    // a record, so it is the one where `m.field` means anything -- and `forall m in mappings
    // of Self : !m.gibtsnicht` passed with `0 errors, 0 hints`. The control in the same run
    // (a falsified BASE name) fell at `D017`. `dokumente/PLAN-HARDWARE.md` §5 rests on the
    // split this rule makes readable: entry fields travel with a grafted subtree, `va` does
    // not.
    "D020",
    // 2026-08-31, the other half of the `N044` sentence: `N044` sees THAT a verdict is
    // missing, `M135` sees whether the one that is there is a verdict at all. `passt` ends
    // in a comparison of RANGES and `bool` has none, so the whole boundary fell through a
    // silent `else` -- at every `return`, assignment and argument. Its first two finds were
    // in this checker: a compare-exchange bound to the atomic's type instead of to `bool`,
    // and an `exchange update` body read against the enclosing function's result.
    "M135",
    // 2026-09-02, the SAME silent `else`, two doors further out. `M135` closed the
    // `bool`/number crossing; `M140` closes every crossing where NEITHER side has a range --
    // a pointer, a record, an array, a function pointer. Measured: 18 parameter kinds x 18
    // argument kinds, the wrong thing passed at a call, and **283 of 306 off-diagonal cells
    // went through with `0 errors` and `100 % coverage`**. `cc` caught 165 of them and the
    // emitter refused 96 -- which is the `N041` shape, a trust base holding one stage too
    // late -- and 22 reached green C.
    "M140",
    // 2026-09-02, the residue `M140`'s own reservation named: `M128` holds arity, effects
    // and cost at a `fn(...)` slot and **nothing about the values that travel through it**.
    // `&eng` with `eng(b : u8) -> u8` went into a `fn(u32) -> u32` slot with `0 errors` and
    // `100 % coverage`; `cc` refused the emitted `.f = &eng` as an *incompatible pointer
    // type*. **A code of its own and not a fourth reading of `M128`**: `M128`'s sentence is
    // *promise no LESS than the slot*, and a signature is an EQUALITY -- nothing converts at
    // an indirect call, so `fn(u32)` at a `fn(u8)` slot is just as wrong as the reverse.
    "M142",
    // 2026-09-03, the third door in that same wall, and this one was never a range question
    // at all: the COUNT. `m1.rs` bound arguments to parameters with
    // `argtypen.iter().zip(sig.parameter.iter())` under a line that assigned the arity to
    // the NAME PASS -- and the name pass has no such rule. A `zip` stops at the
    // shorter list, so `zwei(x)` against `fn(u32, u32)` and `eins(x, x)` against `fn(u32)`
    // BOTH gave `0 errors` at `100 % coverage`, the emitter wrote the call out, and `cc`
    // answered *too few arguments to function 'zwei'*. **Arity was already held at a
    // function POINTER (`M128`), at `refines` (`M132`) and at a record constructor
    // (`M106`)** -- the commonest call in the language had the check the three rarer ones
    // carry.
    //
    // > **Its corpus site is F3, and it is a frozen excerpt line.** `FRAGMENTE.md`:692
    // > writes `owner_core(picked)` against `extern fn owner_core(d : ptr<normal, r>
    // > SchedOps, t : u32)` -- one argument, two parameters. Until today it surfaced as an
    // > `M140` about parameter `d`, a statement about the wrong thing: had both parameters
    // > been `u32`, the call would have been silent.
    "M143",
    // «B7»: der Verbundkonstruktor.
    "M106", "M107", "M108", "P036", "P037",
    // Punkt 3: `ensures` wird gelesen -- Wohlgeformtheit, nicht Beweis.
    "M109", "M110", "M111",
    // **P6, 2026-08-19: `maintains` wird gelesen.** `M112` steht hier als FOLGEFEHLER, und
    // der Grund gehoert dazu: der Ausschnitt in `SYNTAX.md`:533 erklaert `cdt_wellformed`
    // als `spec fn`, und die Zeile scheitert am Parser -- `c.parent_chain(s)` ist ein Ruf in
    // einem `place`, und «B8» verbietet das. *Die Deklaration wird nie erklaert, also nennt
    // `maintains` ins Leere.*
    //
    // > **Gabbro unterdrueckt Folgefehler nicht**, und das ist eine Entscheidung, die vor
    // > heute niemand aufgeschrieben hat: nach einem `P001` laufen die Paesse weiter. Was
    // > sie dann melden, kann Rauschen sein.
    "M112", "M113", "M114", "M115",
    // **`M119`, 2026-08-20: ein Name, den niemand deklariert.** Neu, weil ein Tippfehler die
    // Indexprüfung abschaltete: `t.slots[j].x` mit unbekanntem `j` gab **null Fehler**,
    // dieselbe Zeile mit `i` gibt `M103`. *M1 überspringt still, was es nicht typisieren
    // kann — und druckte dafür „100 % coverage".*
    //
    // Auf einem FRAGMENT ist die Absage richtig und trotzdem kein Befund über den Code: ein
    // Auszug deklariert seine Namen nicht. `FRAGMENTE.md`:269 nennt `obj`, gebunden in einer
    // Zeile, die nicht im Ausschnitt steht. **Deshalb steht `M119` hier — als benannte
    // Absage auf einer unvollständigen Hülle, dieselbe Klasse wie `E009` und `K003`.**
    "M117", "M118", "M119",
    // **Die dritte Rezension, zweite Haelfte** (2026-08-20). Vier neue Absagen, und jede
    // schliesst eine Umgehung, die einen SYNTAKTISCHEN SCHRITT neben einer bestehenden
    // Giftprobe lag:
    //
    // * `L108` -- ein linearer Wert wird in einem SCHLEIFENRUMPF verbraucht. Der Rumpf lief
    //   einmal als geradliniger Code; *genau einmal* ist aber eine Aussage ueber die
    //   Ausfuehrung, nicht ueber den Quelltext.
    // * `L109` -- ein linearer Wert wird in einem ZWEIG geboren und verlaesst ihn nicht.
    //   `abgleich` lief ueber den Stand VOR der Verzweigung, also fiel er heraus.
    // * `N027` -- ein `can_fail`-Block schreibt. Ein `check` traegt keinen Vertrag, und zehn
    //   der zwoelf Paesse laufen ueber `ItemArt::Funktion` und sahen ihn nie.
    "L108", "L109", "N027",
    // **`S006`, 2026-08-19: `on_exceeded` muss divergieren.** Die Fundstelle in
    // `FRAGMENTE.md`:902 schreibt `on_exceeded DeviceSilent` -- eine `reason`-VARIANTE, nicht
    // eine Funktion. *Der Erzeuger sagt seit jeher, warum das nicht geht:* „a `reason` value
    // would need an error-return convention, and that is not decided". **Das Fragment hat den
    // Bedarf vorweggenommen, und die Sprache hat ihn nicht.** Gebucht in `TODO.md`.
    "S006",
    // **`S007` -- der Wachhundname, den dieser Ausschnitt nicht deklariert.**
    // `FRAGMENTE.md`:902 nennt `on_exceeded DeviceSilent`, und `MESSUNGEN.md` fuehrte diese
    // Stelle bis 2026-08-19 als das, worueber `S006` SCHWEIGT. Sie schweigt nicht mehr:
    // weder abgesagt noch bestaetigt, aber sichtbar -- der dritte Zustand.
    "S007",
    // **`N016`-`N018`, 2026-08-19: die Axiomschicht und der Eintritt.** Ausgeloest von
    // `pruefe-konstrukte.py`, das sieben Konstrukte ohne Giftprobe meldete. `N018` faellt in
    // `SPRACHE.md`:1382 an einem AUSSCHNITT, dessen `dispatch`-Ziel er nicht deklariert --
    // *dieselbe Lage wie bei jedem Ausschnitt: der Name loest auf, nur nicht hier.*
    "N016", "N017", "N018",
    // **`N020` -- `gates` nennt niemanden**, und am Ausschnitt ist das dieselbe Lage wie oben:
    // `FRAGMENTE.md`:1184 gattert auf `all_done`, und der Name steht in diesem Ausschnitt
    // genau EINMAL, naemlich dort. *In der vollen Uebersetzungseinheit loest er auf; hier
    // nicht, und der Waechter sagt es statt es zu raten.*
    "N020",
    "K004", "K005", "D001", "D002", "D003", "D004", "M105", // Haltezeit geteilt, K-Bedingung, narrow-Zweig
    // **`K010`, 2026-08-20** -- eine `held`-Zusage, die keine Zahl ist. Sie fiel bis heute
    // aus der Karte, und mit der Karte fiel `K002`: die Sperre war unbewacht, und der Lauf
    // sagte 0 Fehler. *Die Kostenklasse vertraegt Symbole, die Sperrklasse nicht.*
    "K010",
    "V001", "V002", "V003", "V004", // Paarung
    "L101", "L102", "L103", "L104", "L105", // M2, echte Linearitaet
    "R001", "R002", "R003", "R004", // M3, Raeume, Rechte -- und zweimal `own` auf denselben Ort
    // 2026-09-02, beside `R008` and out of the same measurement: `R008` reads `z.raum` and
    // stops, `z.rechte` sits in the same struct and nothing read it. A `ptr<normal, r>`
    // reached a `ptr<normal, rw>` parameter with **0 errors**; the emitter wrote
    // `const Text *` into a `Text *` and `cc` said *discards `const` qualifier*.
    // **And unlike the space, rights are not symmetric** -- `rw` at an `r` slot is
    // narrowing and must stay silent, and `tests/gestalt.rs` already pinned that row.
    "R013",
    // **Die Versiegelung eines `asm`-Rumpfes** («OPT3»): `arch`, `effects`, `costs`, und ein
    // Operand, der ein Parameter sein muss. Geprueft wird die FORM, nicht der Befehlstext --
    // den liest Gabbro nicht, und das ist der Kern der Sache.
    "A001", "A002", "A003", "A004", "N026",
    "U001", "U002", "U003", "U004", "U005", "U006", "U007", // Traegergruppe: Sperrabdruck, Zug und Verbindungsaussage
    // --- Stufe 7 ---
    // **`M126` -- `FRAGMENTE.md`:269 schreibt `return Fehler::Buchfuehrung;`.**
    //
    // *Das ist der Bedarfsbeleg fuer den Grunderzeuger, und er stand die ganze Zeit im
    // Ordner.* Der Ausschnitt kommt aus echtem Code, er meldet einen Fehler an seinen Rufer
    // zurueck, und er schreibt dafuer genau die Form, die die Sprache bis zum 2026-08-21
    // nicht kannte. **Bis dahin fiel die Zeile mit `M119`** (*„`Fehler` is declared
    // nowhere"*) -- eine Absage, die den Namen nicht als GRUND las, sondern als Ort.
    //
    // Jetzt liest sie ihn als Grund und sagt, was fehlt: `reason Fehler` ist in diesem
    // Ausschnitt nicht deklariert. *Dieselbe Lage wie bei `N018` und `N020` -- in der vollen
    // Uebersetzungseinheit loest der Name auf, im Ausschnitt nicht.*
    "M126",
    // **`M124` -- `FRAGMENTE.md`:657 schreibt `set_reg(f, SYSNO_RESULT,
    // IpcResult::ErrQuiescing);`.**
    //
    // Ein Grundwert als ARGUMENT, und das ist eine der Stellungen, die `M124` absagt: ein
    // Grund geht durch `return`, durch den Gegenstand eines `match` und durch einen
    // Vergleich, und durch nichts sonst.
    //
    // **Die Absage ist richtig und der Bedarf ist echt.** Die Zeile schreibt das
    // Syscall-Ergebnis in das Nutzerregister -- das ist die **ABI**, nicht Gabbros
    // Fehlerkanal, und die Zahl an der `reason`-Zeile ist genau das, was dort reisen soll.
    // *Wie ein Grund die Syscall-Grenze ueberquert, ist nicht entschieden* -- gebucht in
    // `TODO.md`.
    //
    // > Dieselbe Lage wie bei `S006`: **das Fragment hat den Bedarf vorweggenommen, und die
    // > Sprache hat ihn nicht.** Ihn hier stillschweigend zuzulassen hiesse, die
    // > Stellungsregel fuer den einen Fall aufzugeben, fuer den sie am wenigsten gilt.
    "M124",
    // **`N035` -- `FRAGMENTE.md`:633-637 declares five function pointers and NO contract.**
    //
    // ```gabbro
    // type SchedOps = {
    //     current_id    : fn(u32) -> u32,
    //     block_current : fn(u32, u64) -> u64,
    //     …
    // };
    // ```
    //
    // **The refusal is exactly what the comment three lines above it asks for**, in the
    // fragment's own words: *"«B9» Der Ersatz fuer `&mut dyn SchedOps`: `fnptr` traegt
    // KEINEN Vertrag"*. `N035` was built on 2026-08-21 for this sentence.
    //
    // > **And until 2026-08-25 it never reached the fragment.** A parameter name was
    // > obligatory in a pointer type, so `fn(u32)` died at `P002`/`P003` -- a reader refusal
    // > at a token, before any pass could look. Measured on `messung/fragmente/F03.gab`, the
    // > same five lines as a `.gab` file: **23 items, 5 reader refusals** before, **24 items,
    // > 5 `N035`** after. *A rule cannot bite through a form the parser rejects, and the
    // > count looked the same from outside -- 11 errors either way.*
    "N035",
    // **`N040` -- and over the FROZEN excerpt it is the EXPECTED answer.**
    //
    // An excerpt names types it does not declare; that is its nature, and it has stood
    // counted out since 2026-08-20 in `messung/fragmente/README.md`: *"41 sites name 20
    // names nobody declares."* Until 2026-08-25 nothing but that tally SAID so -- the
    // checker walked over them with 0 errors and the emitter wrote C forward declarations.
    //
    // > *The number was known and the checker was silent* -- the same shape as a clause that
    // > parses and is dropped. **Now it speaks, and the tally has a reader.**
    "N040",
    // **`N041` -- the class refusal, and over the frozen corpus it no longer fires.**
    //
    // It stays in this list because it is the answer for a definING item: `pub fn exit`,
    // `const NAN`, `type switch`. The corpus holds none today, and an allow-list entry
    // nobody reaches is cheaper than one that is missing when somebody writes the line.
    "N041",
    // **`N046` -- and over the frozen excerpt it is the finding, not a side effect.**
    //
    // `FRAGMENTE.md`:1028 writes `extern fn exit() -> never effects { diverges };`, and the
    // body above it calls `exit()` at eight sites. **C owns that name, and here that is the
    // POINT** -- an `extern fn` exists to bind it. What is wrong is the SIGNATURE: the
    // generator writes `_Noreturn void exit(void);` and `cc` answers *conflicting types for
    // built-in function 'exit'; expected 'void(int)'*. The parameter is missing, not the
    // right to the name. Measured 2026-08-31 (`messung/C-NAMEN.md`), re-diagnosed 2026-09-01.
    //
    // > **The line was ADDED to the excerpt on 2026-08-15**, with the note above it saying
    // > `exit` and `signal` had been called and never declared -- and it thereby became part
    // > of the frozen text. Since then it has been the one line that keeps `F05` from
    // > lowering, and nothing said so: the
    // > checker was silent, the emitter wrote 199 lines of C, and the foreign compiler
    // > refused them. *A finding that only the third tool can see is not a finding, it is a
    // > surprise.*
    //
    // > **And from 2026-08-31 to 2026-09-01 it was named WRONGLY**, which is the cheaper of
    // > the two failures but not a free one: `N041` said the name was taken and told the
    // > writer to rename. *`exit` is exactly the name that line wants* -- the fix is
    // > `extern fn exit(a : i32)`, and only `N046` says so.
    "N046",
    // **`N043` -- the report line of `check kstack_eichung`, and it names a carrier that is
    // in no excerpt.**
    //
    // `FRAGMENTE.md`:1166 writes `measures eich.leer, eich.voll, eich.tiefe, eich.gelaufen`
    // and `floor eich.gelaufen == 1`. **There is no `eich` anywhere in the file** -- the
    // calibration reports four fields of something that was never brought over. Same shape
    // as `N040` above and found at the same place (`messung/fragmente/F06.gab`), one week
    // later.
    //
    // > **And the second subject weighs more than the first:** `N021` and `N022` find their
    // > quantity by matching a name against `measures`, so this excerpt's `floor` clause has
    // > been outside every rule that reads the list. *A quantity nobody declared is also a
    // > quantity nobody can check* -- and until 2026-08-31 nothing said so.
    "N043",
    // **The register layout, audited 2026-09-01 out of the emitted C.** `N047` an offset that
    // is not a multiple of its own width, `N048` a bank register that does not fit its cell,
    // `N049` a bank that covers bytes something else already names. All three judge LITERALS
    // only -- the same limit `N009` writes down for itself.
    "N047",
    "N048",
    "N049",
    // **`N050` -- the same audit method, one day later, one layer down.** `N047`-`N049` judge
    // the LAYOUT; `N050` judges whether the layout survives the LOWERING. The bank accessor
    // computes `i * stride` in `unsigned int`, so a bank wide enough wraps at 2^32 and the
    // last cells name addresses that are simply different. Found by handing the emitted C to
    // `clang-tidy`, which calls the site `bugprone-implicit-widening-of-multiplication-result`.
    "N050",
    // **`N051` -- the front end's `u128` literal meeting the back end's 64-bit pointer.**
    // `reg X : u64 @0x100000000000000000` was accepted with `0 errors` because `N047` only
    // asks about alignment and `2^68` is a multiple of 8. Found by
    // `instrumente/fuzze-grenzen.py` in the sweep that also found `N049`'s own overflow.
    "N051",
    // **`N052`, 2026-09-02: the end of the data is IN the data.** Split off from `N041` for
    // the same reason `P041` was split off from `P034`: two unrelated rules stood under one
    // identifier. `N041` refuses a SPELLING -- a `char *` Gabbro cannot write -- and would
    // go away the day Gabbro grew a `char`. `N052` refuses a REPRESENTATION: a terminator
    // scan has no bound anywhere in the signature, so no `requires` can hold it, and that
    // stands whatever types the language gains.
    "N052",    // **`M139` -- a literal wider than `i128`, which until 2026-09-02 answered
    // `Typ::Unbekannt`.** *That is not a refusal; it is an acquittal that reads like
    // caution.* Every rule downstream asks for the type first, so ONE lossy conversion in
    // `m1.rs` silenced `M101`, `M103`, `M104` and `M117` at once -- `T.slots[2^127]` on a
    // `count 8` table was accepted and emitted as an out-of-bounds C subscript. The
    // neighbouring value, `2^127 - 1`, fell at `M103` the whole time. Found by
    // `instrumente/fuzze-grenzen.py`, in the sweep over every rule with a literal slot.
    "M139",
    // **`M141`, 2026-09-02: the same index bound, in a PREDICATE.** `m1.rs` says in its own
    // head that it checks bodies and not predicates, *"they belong to the prover, not to
    // M1"* -- and the prover ASSUMES them: `gabbro lean` writes a `requires` as `<fn>_pre`,
    // "what the caller grants". `requires T.slots[9].x == 0` on a `table T count 8` gave
    // `0 errors` and left this compiler as a premise nothing can establish. It stands in
    // `domaene.rs` because the exhaustive walk over the predicate POSITIONS is already
    // there; only a LITERAL index is compared, so a quantifier variable stays silent.
    //
    // **It is `M141` and not `M140`, and that is the THIRD collision of one day.** The
    // shape-mismatch rule two lanes above already carries the note: two lanes picked the
    // same free number on 2026-09-02, and this one made three. *A free number is only
    // free against the tree one has, and three lanes each had a different tree.*
    "M141",
    // **`N053`, 2026-09-02: the ASSUMPTION TIER, which until today no pass read at all.**
    // `reg … requires` (4 sites) and `transition … requires` (13) were counted by
    // `gabbro pflichten` as device promises and by nothing else; eight hand-made
    // counter-forms all gave `0 errors, 0 hints` under `pruefe` AND under `emit`.
    //
    // It refuses the half that is decidable without knowing the machine: **a premise over
    // a place that does not exist.** Whether `GSTS.RTPS == 1` HOLDS stays an assumption and
    // is not touched -- the same line `M141` draws one construct over. The asymmetry that
    // made it worth building: the STEP of the same `transition` has been held to the
    // device's own registers by `C001` since it existed.
    //
    // > It found one in the tree it was written against: `messung/fragmente/F04.gab`:73
    // > wrote `requires QUEUE_SIZE <= QMAX` and `QMAX` stood nowhere -- booked as open in
    // > that file's own head since 2026-08-20, *"because no pass reads `RegDecl::requires`"*.
    "N053",
    // **`D021` -- the base name of a place in a PREDICATE resolves** (2026-09-02).
    //
    // `M109` asked this of an `ensures` and of nothing else, `N053` of a device promise,
    // `N032` of a `format ... where`. Measured position by position against the unchanged
    // checker (`messung/PREDICATE-NAMES.md`): a name nothing declares was accepted in **266
    // of 380** position x name-kind cells, and the sixteen positions without a reader
    // include every `requires`, every `invariant` and the body of every `spec fn`.
    //
    // The severity is not "a check is missing". `gabbro lean` writes a `requires` into
    // `<fn>_pre`, *"what the caller grants"*, so a conjunct over a phantom name is a premise
    // the prover CARRIES -- and unlike the call form, which the Lean channel names as
    // DROPPED, it is visible in no channel at all. **A wrong proof object, not a missing
    // finding.**
    //
    // > It found one in the tree it was written against: `messung/fragmente/F01.gab`:189
    // > wrote `c.slots[s] reaches WURZEL via parent` -- byte for byte the excerpt's own line
    // > -- and no unit of that file declared `WURZEL`.
    "D021",
    // **`N054` -- `Has(…)` names ONE machine feature, and a feature is a bare NAME**
    // (2026-09-02). The other direction of the same tier: `D021` holds a PREDICATE name
    // against the tree, this holds a FEATURE name against the only thing that can be held
    // without a declared list -- its shape.
    //
    // Measured first: eleven written forms x six positions, **64 of 66 accepted**.
    // `Has()`, `Has(7)`, `Has(GRENZE + 1)`, `Has(T.slots)` and `Has(RDTSCP, XSAVE)` all
    // gave `0 errors, 0 hints`. The last is the sharpest -- every reader of the form takes
    // `argumente.first()`, so it reads as a demand for two features and is one for the
    // first.
    //
    // > Whether the NAME is a feature of the machine stays undecided here and says so in
    // > its own second note: `SPRACHE.md` puts the only generator of `Has(F)` at the CPUID
    // > probe, that probe does not exist, and no list of feature names exists in the
    // > language.
    "N054",
];

#[test]
fn der_korpus_bringt_nur_benannte_absagen() {
    for datei in ["dokumente/FRAGMENTE.md", "dokumente/SYNTAX.md", "dokumente/SPRACHE.md", "README.md",
                  // Der Memo BEHAUPTET „heute schreibbar" -- dann wird sein Block auch gemessen.
                  "dokumente/MEMO-GLEITKOMMA.md"] {
        let md = lies(datei);
        for b in korpus::messe(datei, &md) {
            for (code, zeile) in b.fehler.iter().chain(b.hinweise.iter()) {
                assert!(
                    BENANNT.contains(code),
                    "{datei}:{zeile}: unbenannte Absage `{code}` -- \
                     jede Absage braucht ihren Eintrag, sonst zaehlt niemand sie"
                );
            }
        }
    }
}

#[test]
fn f2_das_geraetefragment_bleibt_sauber() {
    // F2 (VT-d als `device`) ist das eine Fragment, das gegen die heutige Grammatik
    // vollstaendig durchgeht. Faellt es, ist eine Regel zurueckgegangen.
    let md = lies("dokumente/FRAGMENTE.md");
    let befunde = korpus::messe("dokumente/FRAGMENTE.md", &md);
    // **Am INHALT verankert, nicht an der Zeilennummer.** Bis 2026-08-15 stand hier
    // `erste_zeile > 330 && < 350`; jede Aenderung weiter oben in der Datei brach den Test,
    // ohne dass an F2 etwas falsch war. Eine Probe, die an einer Zeilennummer haengt, ist
    // dieselbe Sorte Zahl wie eine, die ein Mensch parallel zur Wahrheit fuehrt.
    // `Befund.text` ist der gerenderte BERICHT, nicht die Quelle -- der Inhalt muss aus
    // den geschnittenen Bloecken kommen.
    let quelle = korpus::schneide(&md);
    let f2_zeile = quelle
        .iter()
        .find(|b| b.text.contains("device Vtd"))
        .map(|b| b.erste_zeile)
        .expect("F2 ist das VT-d-Fragment -- erkennbar an `device Vtd`");
    let f2 = befunde
        .iter()
        .find(|b| b.erste_zeile == f2_zeile)
        .expect("zu jedem geschnittenen Block gehoert ein Befund");
    assert!(
        f2.sauber(),
        "F2 war sauber und ist es nicht mehr:\n{}",
        f2.text
    );
}

#[test]
fn jeder_block_wird_gefunden() {
    let md = lies("dokumente/FRAGMENTE.md");
    let bloecke = korpus::schneide(&md);
    assert_eq!(
        bloecke.len(),
        md.matches("\n```gabbro").count(),
        "der Schneider verliert Bloecke"
    );
    // Die Zeilennummern muessen die der Markdown-Datei sein -- sonst zeigt eine Absage
    // auf eine Zeile, die es nicht gibt.
    for b in &bloecke {
        let vorspann = b.text.chars().take_while(|c| *c == '\n').count();
        assert_eq!(vorspann + 1, b.erste_zeile);
    }
}

#[test]
fn die_beispiele_der_grammatik_gehen_selbst_durch() {
    // **SYNTAX.md ist das Grammatikdokument -- seine eigenen Uebersetzungseinheiten muessen
    // uebersetzen.** Bis 2026-08-16 hat das niemand verlangt, und es standen drei echte
    // Fehler darin: `Duty(check)` (der Parameter ist der NAME einer Pruefung, nicht das
    // Wort), und zweimal eine Wortschatzkollision in einem Beispiel.
    //
    // *Ein Grammatikdokument, dessen Beispiele die Grammatik verletzen, ist die teuerste
    // Sorte Prosa: es sieht aus wie ein Beleg.*
    let md = lies("dokumente/SYNTAX.md");
    for b in korpus::messe("dokumente/SYNTAX.md", &md) {
        if b.vollstaendig {
            assert!(
                b.sauber(),
                "SYNTAX.md, Block ab Zeile {}: das Grammatikdokument bricht seine eigene \
                 Grammatik:\n{}",
                b.erste_zeile,
                b.text
            );
        }
    }
}

#[test]
fn jeder_gebaute_pass_ist_auch_angemeldet() {
    // **Gegen den entzogenen Halbcommit.** Am 2026-08-16 loeste ein `git stash` die
    // Registrierung des Paarungspasses aus dem Index; der Commit trug den Pass ohne seine
    // Anmeldung, und `gabbro paesse` haette ihn weiter als OFFEN gefuehrt. Niemand haette
    // es gemerkt -- die Proben liefen gruen, weil `pruefe()` ihn ja aufrief.
    //
    // Dieselbe mechanische Loesung wie fuer die Kennungen: der Abgleich steht in der
    // Waechterkette, nicht in der Aufmerksamkeit.
    let quelle = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/lib.rs"),
    )
    .expect("lib.rs");
    // Jedes `<name>::pass(` in `pruefe()` muss einen Eintrag in `passliste()` haben, der
    // NICHT `Zustand::Offen` ist -- ein aufgerufener Pass, der als offen gilt, ist eine
    // Zusage in die falsche Richtung: er prueft mehr, als er zugibt.
    let rumpf = quelle
        .split("pub fn pruefe(")
        .nth(1)
        .and_then(|s| s.split("\n}").next())
        .expect("pruefe()");
    for zeile in rumpf.lines() {
        let Some(modul) = zeile.trim().strip_suffix("::pass(baum, absagen);") else {
            continue;
        };
        let name = match modul {
            "m1" => "M1",
            "m2" => "M2",
            "m3" => "M3",
            "paarung" => "Paarung",
            "wirkungen" => "effects",
            "kosten" => "costs",
            "schleifen" => "M4",
            "namen" => "Namen",
            _ => continue, // Hilfspaesse ohne eigene Nummer (kbedingung, geteilt)
        };
        let eintrag = gabbro_check::passliste()
            .into_iter()
            .find(|p| p.name.starts_with(name))
            .unwrap_or_else(|| panic!("`{modul}::pass` laeuft, steht aber in keiner Passliste"));
        assert!(
            !matches!(eintrag.zustand, gabbro_check::Zustand::Offen(_)),
            "`{modul}::pass` wird gerufen, `gabbro paesse` fuehrt `{}` aber als OFFEN -- \
             ein Pass, der prueft und sich als ungebaut ausgibt, ist eine Zusage in die \
             falsche Richtung",
            eintrag.name
        );
    }
}

/// **Diese Probe kam aus einer Mutation, die ueberlebt hat (2026-08-17).**
///
/// `eine-einheit-faengt-mit-irgendwas-an` machte `ist_uebersetzungseinheit` blind fuer die
/// Frage, womit ein Block anfaengt — und **nichts fiel**. Die Regel *„eine
/// Uebersetzungseinheit faengt mit einem Item an"* war damit unbewacht, obwohl Tor P2 auf
/// ihr steht: sie entscheidet, was ueberhaupt gezaehlt wird.
///
/// > *Ein Nenner, den niemand prueft, ist die billigste Art, eine Quote zu verbessern.*
#[test]
fn eine_uebersetzungseinheit_faengt_mit_einem_item_an() {
    use gabbro_check::korpus::ist_uebersetzungseinheit;

    assert!(
        ist_uebersetzungseinheit("module t {\nconst A : u32 = 1;\n}"),
        "ein Modul ist eine Uebersetzungseinheit"
    );
    assert!(
        ist_uebersetzungseinheit("const A : u32 = 1;"),
        "ein Item auf oberster Ebene auch"
    );

    // **Ausschnitte, und genau sie sind der Grund fuer die Unterscheidung.** SPRACHE.md und
    // SYNTAX.md zeigen ueberwiegend einzelne Anweisungen; wer sie als Programm liest, meldet
    // Fehler, die es nicht gibt — und wer sie MITZAEHLT, rechnet die Quote von Tor P2 schoen.
    for ausschnitt in [
        "let x : u32 = 1;",
        "return 0;",
        "if a < b { return 0; }",
        "traverse s over slots of c by unvisited { }",
        "match a { Eins(x) => { } }",
    ] {
        assert!(
            !ist_uebersetzungseinheit(ausschnitt),
            "`{ausschnitt}` faengt mit einer ANWEISUNG an und ist kein Programm"
        );
    }

    // Und der Fall, der die erste Fassung dieser Regel aufgeflogen hat: `…` im KOMMENTAR
    // ist erlaubt (der Lexer trennt Code von Kommentar), `…` im CODE nicht.
    assert!(
        ist_uebersetzungseinheit("-- hier waere noch mehr …\nconst A : u32 = 1;"),
        "`…` im Kommentar macht aus einem Programm keine Skizze (W9, gemessene Richtung)"
    );
    assert!(
        !ist_uebersetzungseinheit("const A : u32 = …;"),
        "`…` im Code ist eine Auslassung, kein Programm"
    );
}

/// **Jede Korpusdatei steht in einem `module` — und das ist keine Formfrage** (2026-08-20).
///
/// Gefunden von aussen: `beispiele/gift/22-globaler-fakt-nach-aufruf.gab` trug die Notiz
/// *„damit das Loch nicht zurueckkehrt"* und war grün. **Dieselbe Datei in ein `module`
/// gewickelt gab drei Fehler statt einem** — `m1.rs::ist_lokal` fragte die
/// modulqualifizierte Karte der globalen Grössen mit einem *unqualifizierten* Schlüssel,
/// also galt in jeder Datei mit `module` jede globale Grösse als lokal.
///
/// > Alle 38 sauberen Beispiele hatten ein `module`, 40 von 177 Giftdateien nicht. **Der
/// > Korpus prüfte also die Regel in einer Umgebung, in der niemand programmiert.**
///
/// *Die Asymmetrie war das Loch, nicht die einzelne Datei.* Ein Gift ohne `module` misst
/// eine Namensauflösung, die im echten Gebrauch nie vorkommt — und deckt damit genau die
/// Fehlerklasse zu, gegen die es geschrieben wurde.
#[test]
fn jede_korpusdatei_steht_in_einem_modul() {
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("Wurzel")
        .join("beispiele");
    let mut ohne = Vec::new();
    let mut gesehen = 0;
    for ordner in [wurzel.clone(), wurzel.join("gift")] {
        for e in std::fs::read_dir(&ordner).expect("beispiele lesbar") {
            let p = e.expect("Eintrag").path();
            if p.extension().is_none_or(|x| x != "gab") {
                continue;
            }
            gesehen += 1;
            let t = std::fs::read_to_string(&p).expect("lesbar");
            if !t.lines().any(|z| z.starts_with("module ")) {
                ohne.push(p.file_name().unwrap().to_string_lossy().to_string());
            }
        }
    }
    assert!(gesehen > 200, "der Waechter hat den Korpus gefunden: {gesehen} Dateien");
    ohne.sort();
    assert!(
        ohne.is_empty(),
        "{} Datei(en) ohne `module` -- sie messen eine Namensaufloesung, die im echten \
         Gebrauch nie vorkommt:\n  {}",
        ohne.len(),
        ohne.join("\n  ")
    );
}

/// **Zwei Korpusdateien mit derselben Nummer -- und `git` meldet es nicht.**
///
/// Am 2026-08-20 zum ZWEITEN Mal aufgetreten: beim Zusammenfuehren zweier Arbeitsbaeume, und
/// wenige Stunden spaeter noch einmal, als ein Agent und ich beide `39-…` anlegten. **Git
/// sieht keinen Konflikt, weil die Dateinamen sich unterscheiden** -- die Kollision sitzt in
/// der Nummer, nicht im Namen, und die Nummer ist die Leseordnung des Korpus.
///
/// > *Beim zweiten Mal hoert es auf, eine Aufmerksamkeitssache zu sein.* Diese Probe findet
/// > es beim Zusammenfuehren statt danach -- und sie kostet zwoelf Zeilen.
///
/// **Die stabilere Fassung waere, die Wahl ganz wegzunehmen** (R19-Logik: die Nummern fallen
/// weg, die Reihenfolge kommt aus einer Indexdatei). Sie ist im TODO gebucht und nicht hier
/// gebaut, aus einem Grund, der zur Sache gehoert: die Umbenennung beruehrt jede
/// Dateireferenz in zehn Dokumenten, **und sie mitten in einem Lauf zu machen, in dem gerade
/// jemand numerierte Dateien schreibt, waere die dritte Instanz derselben Kollision.**
#[test]
fn keine_zwei_korpusdateien_teilen_eine_nummer() {
    let wurzel = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("Wurzel")
        .join("beispiele");
    for ordner in [wurzel.clone(), wurzel.join("gift")] {
        let mut nach_nummer: std::collections::BTreeMap<String, Vec<String>> = Default::default();
        for e in std::fs::read_dir(&ordner).expect("beispiele lesbar") {
            let p = e.expect("Eintrag").path();
            if p.extension().is_none_or(|x| x != "gab") {
                continue;
            }
            let name = p.file_name().and_then(|x| x.to_str()).unwrap_or("").to_string();
            // Das Praefix bis zum ersten `-`; ein Buchstabe dahinter gehoert dazu
            // (`11a-divergenz-endet.gab` ist die Gegenprobe zu `11-…` und mit Absicht so).
            let Some(nummer) = name.split('-').next() else { continue };
            if nummer.is_empty() || !nummer.chars().next().is_some_and(|c| c.is_ascii_digit()) {
                continue;
            }
            nach_nummer.entry(nummer.to_string()).or_default().push(name);
        }
        for (nummer, dateien) in &nach_nummer {
            assert!(
                dateien.len() == 1,
                "zwei Korpusdateien tragen die Nummer `{nummer}`: {dateien:?} -- \
                 git meldet das NICHT, weil die Namen sich unterscheiden. Die Nummer ist \
                 die Leseordnung des Korpus, und zwei Dateien koennen sie nicht teilen"
            );
        }
    }
}
