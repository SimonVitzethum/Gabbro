#!/usr/bin/env python3
"""**Der Netzwerkstack, gegen VEROEFFENTLICHTE Vektoren geprueft -- Stufe 4, Regel B.**

    ./instrumente/zaehle-netz.py [--zeige-c]

REGEL A UND REGEL B
-------------------
    A  kein neues Konstrukt ohne ein Programm, das es gebraucht hat
    B  und die VORLAGE kommt von aussen

Ohne B haelt A nicht: ein Stack, den derselbe Autor gegen seine eigenen Testpakete schreibt,
misst wieder, wie gut Gabbro zu Gabbro passt. Deshalb pruefen hier **zwei Vektoren, die
niemand fuer Gabbro ausgesucht hat**:

    45 00 00 73 00 00 40 00 40 11 [b8 61] c0 a8 00 01 c0 a8 00 c7
        der klassische IPv4-Kopf aus RFC 791; die Pruefsumme ist b861

    00 01 f2 03 f4 f5 f6 f7  ->  Summe dd f2        RFC 1071, Abschnitt 3

**Und die Gegenrechnung kommt aus einer ZWEITEN Implementierung** -- den paar Zeilen Python
unten. *Ein Vergleich gegen die eigene Zahl ist kein Vergleich* (W7): waeren beide Seiten aus
derselben Feder, ginge derselbe Denkfehler zweimal durch.

DIE DRITTE PROBE IST DIE WICHTIGSTE
-----------------------------------
`kopfsumme` ueber einem Kopf, in dem die Pruefsumme SCHON steht, muss **0** ergeben. Das ist
die Eigenschaft, auf der der ganze Empfangsweg ruht -- und die einzige der drei, die eine
falsche Faltung nicht ueberlebt.
"""
import os
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
BIN = W / "target" / "debug" / "gabbro"
QUELLE = W / "messung" / "netz" / "udp-echo.gab"
FRIST = 120

# **Die zweite Implementierung.** Absichtlich anders geschrieben als die Gabbro-Fassung:
# hier faltet jeder Schritt, dort faltet erst das Ende zweimal.
def rfc1071(b):
    s = 0
    for i in range(0, len(b), 2):
        s += (b[i] << 8) | (b[i + 1] if i + 1 < len(b) else 0)
        s = (s & 0xFFFF) + (s >> 16)
    return (~s) & 0xFFFF


KOPF_OHNE = "45000073000040004011" + "0000" + "c0a80001" + "c0a800c7"
KOPF_MIT  = "45000073000040004011" + "b861" + "c0a80001" + "c0a800c7"
RFC_BEISPIEL = "0001f203f4f5f6f7"

PRUEFSTAND = """
#include <stdio.h>

/* **Die fremden Ruempfe.** Sie stehen hier und nicht in Gabbro, und `gabbro zeugnis`
   zaehlt sie als das, was sie sind: Vertrauensflaeche. Der Pruefstand misst die
   Pruefsumme; die drei hier werden von ihr nicht beruehrt. */
static uint32_t gesendet_bytes = 0;
bool senden(const EthKopf *e, uint16_t laenge, uint32_t *_wert, Verwurf *_grund) {
    (void)e; (void)_grund; gesendet_bytes += laenge; *_wert = laenge; return true;
}
const Kopfworte * kopfworte_von(const IpKopf *r) { (void)r; return 0; }
UdpKopf * udpkopf_von(const IpKopf *k) { (void)k; return 0; }

/* Der Kopf kommt als BYTES an; die Worte werden in Netzreihenfolge zusammengesetzt.
   **Dass das hier steht und nicht in Gabbro, ist ein Befund** -- siehe README. */
static void worte_aus(Kopfworte *k, const unsigned char *b, int n) {
    for (int i = 0; i < 10; i++) k->wort[i] = 0;
    for (int i = 0; i * 2 < n; i++) k->wort[i] = (uint16_t)((b[2*i] << 8) | b[2*i+1]);
}

int main(void) {
    Kopfworte k;
    static const unsigned char ohne[20] = { %OHNE% };
    static const unsigned char mit[20]  = { %MIT% };
    static const unsigned char rfc[8]   = { %RFC% };
    worte_aus(&k, ohne, 20); printf("ohne=%04x\\n", kopfsumme(&k));
    worte_aus(&k, mit,  20); printf("mit=%04x\\n",  kopfsumme(&k));
    worte_aus(&k, rfc,   8); printf("summe=%04x\\n", (unsigned)(~kopfsumme(&k) & 0xffff));
    return 0;
}
"""


def bytes_c(h):
    return ", ".join(f"0x{h[i:i+2]}" for i in range(0, len(h), 2))


# **`LC_ALL=C` at EVERY call, not only at the `cc`.** A foreign tool reports in the user's
# locale: under a German locale the linker translates `multiple definition`, and a
# `grep` for the English words then misses it. Here the return code decides and not the text -- but the `stderr`
# output beside it is the reason a human reads, and a reason in a changing language is none.
# Fifth requirement in `pruefe-waechter.py`.
UMGEBUNG = {**os.environ, "LC_ALL": "C"}


def lauf(befehl, **kw):
    try:
        return subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST,
                              env=UMGEBUNG, **kw)
    except subprocess.TimeoutExpired:
        print(f"ABBRUCH: `{' '.join(map(str, befehl))}` ueberschritt {FRIST} s -- "
              "es wurde NICHTS gemessen.", file=sys.stderr)
        sys.exit(2)


def main():
    if not BIN.is_file():
        print(f"ABBRUCH: {BIN} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).",
              file=sys.stderr)
        return 2
    if not QUELLE.is_file():
        print(f"ABBRUCH: {QUELLE} fehlt -- es wird NICHT null gemessen.", file=sys.stderr)
        return 2

    # **Sprechprobe, in beide Richtungen.** Ein absichtlich falscher Vektor MUSS auffallen,
    # sonst vergleicht dieser Pruefstand zwei Zahlen, die er selbst erzeugt hat (W17).
    if rfc1071(bytes.fromhex(KOPF_OHNE)) != 0xB861:
        print("SPRECHPROBE GESCHEITERT: die zweite Implementierung trifft den "
              "veroeffentlichten Vektor nicht.", file=sys.stderr)
        return 1
    if rfc1071(bytes.fromhex(KOPF_OHNE[:-2] + "00")) == 0xB861:
        print("SPRECHPROBE GESCHEITERT: ein VERAENDERTER Kopf ergibt dieselbe Summe -- "
              "dieser Pruefstand unterscheidet nichts.", file=sys.stderr)
        return 1
    print("== Sprechprobe: ok (der veroeffentlichte Vektor trifft, ein veraenderter nicht) ==\n")

    r = lauf([str(BIN), "emit", str(QUELLE)])
    if r.returncode != 0 or "kopfsumme" not in r.stdout:
        print("ABBRUCH: `gabbro emit` lief nicht durch:\n" + r.stderr[:800], file=sys.stderr)
        return 1
    c = r.stdout + (PRUEFSTAND
                    .replace("%OHNE%", bytes_c(KOPF_OHNE))
                    .replace("%MIT%", bytes_c(KOPF_MIT))
                    .replace("%RFC%", bytes_c(RFC_BEISPIEL)))
    if "--zeige-c" in sys.argv:
        print(c)
    quelle = W / "target" / "netz-pruefstand.c"
    quelle.parent.mkdir(exist_ok=True)
    quelle.write_text(c, encoding="utf-8")
    binaer = W / "target" / "netz-pruefstand"
    u = lauf(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
              "-o", str(binaer), str(quelle)])
    if u.returncode != 0:
        print("ABBRUCH: `cc` lehnte das erzeugte C ab:\n" + u.stderr[:1200], file=sys.stderr)
        return 1
    e = lauf([str(binaer)])
    if e.returncode != 0:
        print(f"ABBRUCH: der Pruefstand endete mit {e.returncode}.", file=sys.stderr)
        return 1
    ist = dict(re.findall(r"(\w+)=([0-9a-f]+)", e.stdout))

    soll = {
        "ohne":  (f"{rfc1071(bytes.fromhex(KOPF_OHNE)):04x}", "IPv4-Kopf, Feld genullt (RFC 791)"),
        "mit":   ("0000", "derselbe Kopf MIT der Summe -- muss 0 sein"),
        "summe": (f"{(~rfc1071(bytes.fromhex(RFC_BEISPIEL))) & 0xFFFF:04x}",
                  "RFC 1071, Abschnitt 3: die Summe"),
    }
    print(f"== Der Stack gegen veroeffentlichte Vektoren: {len(soll)} Proben ==")
    schlecht = 0
    for k, (s, was) in soll.items():
        gut = ist.get(k) == s
        schlecht += not gut
        print(f"  {'ok ' if gut else 'ROT'}  {k:<6} Gabbro {ist.get(k, '--')}  "
              f"Gegenrechnung {s}   {was}")
    print()
    if schlecht:
        print(f"== {schlecht} von {len(soll)} Proben ROT ==")
        return 1
    print(f"== {len(soll)} von {len(soll)} Proben gruen ==")
    print("  Und was das NICHT heisst: der Stack ist an DREI Vektoren gemessen, nicht an")
    print("  einem Netz. Was er kann, steht in `messung/netz/README.md`; was Gabbro dabei")
    print("  NICHT konnte, steht daneben -- und das ist der eigentliche Ertrag.")
    print()
    zeilen = len(QUELLE.read_text(encoding="utf-8").splitlines())
    print(f"== Arbeitsmenge: {zeilen} Zeilen Gabbro, 1 Uebersetzung, 3 Vektoren, 1 Probe ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
