#!/usr/bin/env python3
"""**Die 15 benannten Luecken aus dem Generatorlauf, einzeln nachgefahren.**

Der zweite Generatorlauf war KEIN sauberer Vorher/Nachher: die Grundgesamtheit war von 377
auf 326 Stellen gefallen (Testkoerper und mehrzeilige Meldungen sind jetzt draussen), also
zog der feste Keim eine andere Stichprobe. **Zwei Quoten ueber verschiedenen Mengen sind
kein Vergleich.**

Diese Datei misst stattdessen die kontrollierte Frage: **sind GENAU DIE benannten Luecken
zu?** Gesucht wird ueber den Zeileninhalt, nicht ueber die Zeilennummer -- die hat sich
verschoben.

**Und sie unterscheidet Bauabbruch von gefangener Mutation.** Am 2026-08-15 haette ich
beinahe "15 von 15" berichtet, waehrend die Testdatei gar nicht uebersetzte: `cargo test`
liefert dann denselben Rueckgabewert wie bei einer gefangenen Mutation. Ein Beleg, der nicht
laeuft, ist keiner (WERKZEUGKASTEN.md W1).
"""
import hashlib
import pathlib, subprocess, re, sys
# **Die Wurzel kommt aus der DATEI, nicht aus einem absoluten Pfad** (2026-08-19).
#
# Hier stand `/home/simon/Dokumente/Gabbro` fest verdrahtet -- als einziger der dreizehn
# Waechter. In einem git-Arbeitsbaum baute und prueffte er damit **den fremden Baum**: er
# verdrehte Zeilen in Quellen, die gar nicht die gerade bearbeiteten waren, und meldete
# „13 von 13" ueber eine Messung, die mit dem Stand vor ihm nichts zu tun hatte.
#
# > *Ein Waechter, der etwas anderes misst, als er sagt, ist schlimmer als keiner* -- und
# > dieser hier SCHREIBT in die Quellen, die er misst.
W = pathlib.Path(__file__).resolve().parent.parent; C = W/"crates/gabbro-check/src"

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie
# ein Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe von
# `pruefe-emission.sh` nebeneinander, der aelteste seit dreieinhalb Stunden.
FRIST = 1800
# (Datei, alte Zeile aus Lauf 1, Verdrehung) -- ueber den INHALT gesucht, nicht ueber die Nummer.
LUECKEN = [
 # **NULLMUTATION, bewiesen** (2026-08-19) -- keine Luecke, sondern eine Verdrehung ohne
 # Wirkung. Zwei Zeilen darueber steht `if b.enthaelt_null() { return … }`, und
 # `enthaelt_null` ist `min <= 0 && max >= 0`. Wer hier ankommt und `b.min >= 0` hat, hat
 # `b.min > 0` -- waere `b.min == 0`, haette `enthaelt_null` schon zurueckgegeben.
 # *Sie kann nicht gefangen werden, weil sie nichts beschaedigt.*
 # **Und der Anker war MEHRDEUTIG**: dieselbe Zeile steht in `teile` und in `rest`.
 # `str.replace(alt, neu, 1)` traf stumm die erste -- gemerkt hat es niemand, weil die
 # Verdrehung ohnehin wirkungslos ist. *Zwei Fehler, die sich gegenseitig verdeckten.*
 (None, "typen.rs",
  "    if a.min >= 0 && b.min > 0 {\n        return ergebnis(breite, vz, a.min / b.max, a.max / b.min);",
  "    if a.min >= 0 && b.min >= 0 {\n        return ergebnis(breite, vz, a.min / b.max, a.max / b.min);"),
 ("typen.rs", "if a.min < 0 || b.min < 0 {", "if a.min < 0 && b.min < 0 {"),
 ("typen.rs", "if bits >= 127 {", "if bits > 127 {"),
 ("typen.rs", "(1i128 << bits) - 1", "(1i128 << bits) - 2"),
 ("typen.rs", "if b.min < 0 || b.max >= a.breite as i128 {", "if b.min < 0 || b.max > a.breite as i128 {"),
 # **NULLMUTATION, bewiesen.** `ecken` ist ein Feld FESTER Laenge (`[_; 4]`); `min()`
 # darueber ist nie `None`, also ist das `unwrap_or` toter Code. Verdrehen laesst sich nur
 # der Wert, den niemand nimmt.
 # Auch dieser Anker steht zweimal (`multipliziere` und `teile`) -- mit Umgebung eindeutig.
 (None, "typen.rs",
  "    let ecken = [a.min * b.min, a.min * b.max, a.max * b.min, a.max * b.max];\n    let min = ecken.iter().copied().min().unwrap_or(0);",
  "    let ecken = [a.min * b.min, a.min * b.max, a.max * b.min, a.max * b.max];\n    let min = ecken.iter().copied().min().unwrap_or(1);"),
 ("umgebung.rs", "if z.rsplit(\"::\").next() == Some(kurz) {", "if z.rsplit(\"::\").next() != Some(kurz) {"),
 ("umgebung.rs", "BinOp::Und => i128::from(x != 0 && y != 0),", "BinOp::Und => i128::from(x != 0 || y != 0),"),
 ("umgebung.rs", "BinOp::Oder => i128::from(x != 0 || y != 0),", "BinOp::Oder => i128::from(x != 0 && y != 0),"),
 ("umgebung.rs", "BinOp::Oder => i128::from(x != 0 || y != 0),", "BinOp::Oder => i128::from(x != 1 || y != 0),"),
 ("umgebung.rs", ".unwrap_or_else(|| IntBereich::voll(32, false));", ".unwrap_or_else(|| IntBereich::voll(33, false));"),
 ("kosten.rs", "XForm::Update { rumpf, .. } => Kosten::Zahl(1).plus(self.block(rumpf)),", "XForm::Update { rumpf, .. } => Kosten::Zahl(2).plus(self.block(rumpf)),"),
 # Der Anker wanderte, als `let … else` eine `place`-Quelle bekam (`als_ruf`): der Ruf
 # steht seitdem in einem `match`, nicht mehr in der Zeile. Nachgezogen 2026-08-19.
 ("kosten.rs", "Kosten::Zahl(1).plus(quelle).plus(self.block(&l.sonst))", "Kosten::Zahl(2).plus(quelle).plus(self.block(&l.sonst))"),
 ("kbedingung.rs", "let (mut haelt, mut faellt) = (0, 0);", "let (mut haelt, mut faellt) = (1, 0);"),
 ("schablonen.rs", "n + 1,", "n + 2,"),
]
def einheitlich(e):
    """Drei Felder oder vier -- das erste sagt `None`, wenn der Eintrag eine NULLMUTATION ist."""
    return e if len(e) == 4 else (True, *e)


def lauf(d, alt, neu):
    """Eine Verdrehung anwenden, bauen, pruefen, zuruecknehmen. Gibt den Zustand."""
    p = C / d
    t = p.read_text()
    if alt not in t:
        return "WEG", t
    p.write_text(t.replace(alt, neu, 1))
    b = subprocess.run(["cargo", "build", "--tests", "--quiet"], cwd=W, capture_output=True, timeout=FRIST)
    if b.returncode != 0:
        p.write_text(t)
        return "UNGUELTIG", t
    r = subprocess.run(["cargo", "test", "--quiet"], cwd=W, capture_output=True, timeout=FRIST)
    p.write_text(t)
    return ("GEFANGEN" if r.returncode != 0 else "ENTKOMMEN"), t


# **Die Sprechprobe, und sie hat hier einmal gefehlt.** Ohne sie zaehlt JEDE Verdrehung als
# gefangen, sobald der Baum aus einem ANDEREN Grund rot ist -- genau so kam am 2026-08-19
# ein "14 von 14" zustande, waehrend drei neue Giftdateien den Lauf rot faerbten und mit den
# Luecken nichts zu tun hatten. *Ein Nullauf, der schon faellt, misst nichts mehr.*
def hashes():
    """Der Zustand aller Quellen, die dieses Werkzeug anfassen darf."""
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(C.glob("*.rs"))}


# **Ein sauberer Baum ist die Vorbedingung, und der Nachweis der Wiederherstellung die
# Nachbedingung** (2026-08-19). Dieses Werkzeug SCHREIBT in Quellen. `mutiere-pruefer.py`
# traegt beide Riegel seit jeher; hier fehlten sie -- und am 2026-08-19 stand `typen.rs`
# hinterher veraendert da, ohne dass sich sagen liess, welcher Lauf es war.
#
# *Ein Werkzeug, das Quellen veraendert und die Rueckgabe nicht nachweist, verschiebt seine
# eigenen Fehler in die Arbeit des naechsten.*
_status = subprocess.run(["git", "status", "--porcelain", "crates/"], cwd=W,
                         capture_output=True, text=True, timeout=FRIST)
if _status.stdout.strip():
    print("  crates/ ist nicht sauber -- erst committen. Dieses Werkzeug schreibt in Quellen.")
    raise SystemExit(2)
VORHER = hashes()

print("== Sprechprobe ==")
_r = subprocess.run(["cargo", "test", "--quiet"], cwd=W, capture_output=True, timeout=FRIST)
if _r.returncode != 0:
    print("  GESCHEITERT: der Baum ist schon ohne Verdrehung rot -- dann faengt alles.")
    raise SystemExit(2)
print("  Nullauf gruen: eine gefangene Verdrehung ist danach EINE Aussage")

zu, offen, weg, null = 0, [], 0, []
for eintrag in LUECKEN:
    echt, d, alt, neu = einheitlich(eintrag)
    if not echt:
        z, _ = lauf(d, alt, neu)
        null.append((d, alt, z))
        print(f"  ~~ NULLMUTATION {d}: {alt[:52]}  ({z})")
        continue
    p = C/d; t = p.read_text()
    if alt not in t:
        weg += 1; print(f"  -- ANKER WEG  {d}: {alt[:56]}"); continue
    p.write_text(t.replace(alt, neu, 1))
    # **Uebersetzt der Mutant ueberhaupt?** Ein Bauabbruch sieht fuer `cargo test` genauso
    # aus wie eine gefangene Mutation -- und zaehlt in dieser Fassung als GEFANGEN, obwohl
    # nichts gemessen wurde. Genau so habe ich am 2026-08-15 beinahe "15 von 15" berichtet,
    # waehrend die Testdatei nicht kompilierte. W1: ein Beleg, der nicht laeuft, ist keiner.
    b = subprocess.run(["cargo","build","--tests","--quiet"], cwd=W, capture_output=True, timeout=FRIST)
    if b.returncode != 0:
        p.write_text(t); weg += 1
        print(f"  -- UNGUELTIG  {d}: uebersetzt nicht"); continue
    r = subprocess.run(["cargo","test","--quiet"], cwd=W, capture_output=True, timeout=FRIST)
    p.write_text(t)
    if r.returncode != 0: zu += 1; print(f"  GEFANGEN     {d}: {alt[:56]}")
    else: offen.append((d,alt)); print(f"  !! ENTKOMMEN {d}: {alt[:56]}")
print(f"\n== {zu} von {zu+len(offen)} der benannten Luecken sind ZU ({weg} Anker verschwunden) ==")
if null:
    print(f"   {len(null)} Eintraege sind NULLMUTATIONEN und zaehlen nicht mit:")
    for d, alt, z in null:
        print(f"     {d}: {alt[:60]}")
    print("   Eine Verdrehung ohne Wirkung kann nicht gefangen werden. Sie als Luecke zu")
    print("   zaehlen ist schlimmer als ein toter Anker: der sagt nichts, sie sagt Falsches.")
# **Der Rueckgabewert, seit 2026-08-19.** Bis dahin endete diese Datei mit einer ZAHL und
# `rc = 0` -- ein Bericht, den ein Waechterlauf als "gruen" las, ganz gleich was drinstand.
# *Dieselbe Klasse wie die vier Klauseln ohne Leser.*
# **Der Nachweis, byteweise.** Kein "war wohl in Ordnung": jede Datei, die dieses Werkzeug
# anfassen darf, muss hinterher dieselbe sein.
NACHHER = hashes()
_verschoben = [n for n in VORHER if VORHER[n] != NACHHER.get(n)]
if _verschoben:
    print(f"\n== WIEDERHERSTELLUNG FEHLGESCHLAGEN: {', '.join(_verschoben)} ==")
    print("   Diese Dateien stehen veraendert da. Ein Werkzeug, das Quellen anfasst und die")
    print("   Rueckgabe nicht nachweist, verschiebt seine Fehler in die Arbeit des naechsten.")
    raise SystemExit(2)
if offen or weg:
    print("\n== LUECKEN: FEHLER ==")
    raise SystemExit(1)
print("== LUECKEN: ALL PASS -- und alle Quellen byteidentisch zurueck ==")
