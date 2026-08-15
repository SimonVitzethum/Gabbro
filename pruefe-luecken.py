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
import pathlib, subprocess, re
W = pathlib.Path("/home/simon/Dokumente/Gabbro"); C = W/"crates/gabbro-check/src"
# (Datei, alte Zeile aus Lauf 1, Verdrehung) -- ueber den INHALT gesucht, nicht ueber die Nummer.
LUECKEN = [
 ("typen.rs", "if a.min >= 0 && b.min > 0 {", "if a.min >= 0 && b.min >= 0 {"),
 ("typen.rs", "if a.min < 0 || b.min < 0 {", "if a.min < 0 && b.min < 0 {"),
 ("typen.rs", "if bits >= 127 {", "if bits > 127 {"),
 ("typen.rs", "(1i128 << bits) - 1", "(1i128 << bits) - 2"),
 ("typen.rs", "if b.min < 0 || b.max >= a.breite as i128 {", "if b.min < 0 || b.max > a.breite as i128 {"),
 ("typen.rs", "let min = ecken.iter().copied().min().unwrap_or(0);", "let min = ecken.iter().copied().min().unwrap_or(1);"),
 ("umgebung.rs", "if z.rsplit(\"::\").next() == Some(kurz) {", "if z.rsplit(\"::\").next() != Some(kurz) {"),
 ("umgebung.rs", "BinOp::Und => i128::from(x != 0 && y != 0),", "BinOp::Und => i128::from(x != 0 || y != 0),"),
 ("umgebung.rs", "BinOp::Oder => i128::from(x != 0 || y != 0),", "BinOp::Oder => i128::from(x != 0 && y != 0),"),
 ("umgebung.rs", "BinOp::Oder => i128::from(x != 0 || y != 0),", "BinOp::Oder => i128::from(x != 1 || y != 0),"),
 ("umgebung.rs", ".unwrap_or_else(|| IntBereich::voll(32, false));", ".unwrap_or_else(|| IntBereich::voll(33, false));"),
 ("kosten.rs", "XForm::Update { rumpf, .. } => Kosten::Zahl(1).plus(self.block(rumpf)),", "XForm::Update { rumpf, .. } => Kosten::Zahl(2).plus(self.block(rumpf)),"),
 ("kosten.rs", "Kosten::Zahl(1).plus(self.ruf(&l.ruf)).plus(self.block(&l.sonst))", "Kosten::Zahl(2).plus(self.ruf(&l.ruf)).plus(self.block(&l.sonst))"),
 ("kbedingung.rs", "let (mut haelt, mut faellt) = (0, 0);", "let (mut haelt, mut faellt) = (1, 0);"),
 ("schablonen.rs", "n + 1,", "n + 2,"),
]
zu, offen, weg = 0, [], 0
for d, alt, neu in LUECKEN:
    p = C/d; t = p.read_text()
    if alt not in t:
        weg += 1; print(f"  -- ANKER WEG  {d}: {alt[:56]}"); continue
    p.write_text(t.replace(alt, neu, 1))
    # **Uebersetzt der Mutant ueberhaupt?** Ein Bauabbruch sieht fuer `cargo test` genauso
    # aus wie eine gefangene Mutation -- und zaehlt in dieser Fassung als GEFANGEN, obwohl
    # nichts gemessen wurde. Genau so habe ich am 2026-08-15 beinahe "15 von 15" berichtet,
    # waehrend die Testdatei nicht kompilierte. W1: ein Beleg, der nicht laeuft, ist keiner.
    b = subprocess.run(["cargo","build","--tests","--quiet"], cwd=W, capture_output=True)
    if b.returncode != 0:
        p.write_text(t); weg += 1
        print(f"  -- UNGUELTIG  {d}: uebersetzt nicht"); continue
    r = subprocess.run(["cargo","test","--quiet"], cwd=W, capture_output=True)
    p.write_text(t)
    if r.returncode != 0: zu += 1; print(f"  GEFANGEN     {d}: {alt[:56]}")
    else: offen.append((d,alt)); print(f"  !! ENTKOMMEN {d}: {alt[:56]}")
print(f"\n== {zu} von {zu+len(offen)} der benannten Luecken sind ZU ({weg} Anker verschwunden) ==")
