#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""zaehle-b3.py -- B3: welche Ruempfe lassen sich NICHT als Traversierung schreiben?

Erhebt gegen einen Rust-Kernelbaum die Ruempfe, die Gabbros drei Schleifenformen
(`traverse over <domaene> by`, `retry until bounded N ops`, `forever per_pass
bounded N ops`) ueber den acht Domaenen NICHT aufnehmen koennen.

    ./zaehle-b3.py ../caprock-messbasis
    ./zaehle-b3.py ../caprock-messbasis --json=b3.json

Marken (Protokoll in dokumente/MESSUNGEN.md, Abschnitt "VORAB -- B3 beziffern"):
  Na   Kettenlauf ohne Domaene (Zeiger-, Index- oder Kantenkette)
  Nb1  Zeigerchirurgie an einer Struktur OHNE Gabbro-Domaene
  Nb2  Zeigerchirurgie an einer Struktur MIT Gabbro-Domaene (Kippfall)

Berichtete Zahl = Na + Nb1 + Nb2 (Grenzfaelle in die teurere Spalte).
Ein nicht aufgehender Klammerabgleich ist ein ABBRUCH und wird gezaehlt (R14a);
steht dort eine Zahl > 0, ist das Ergebnis eine untere Schranke (R16).
"""
import os
import re
import sys
import json


# ---------------------------------------------------------------- Bereinigung

def bereinige(text):
    """Kommentare, String-, Roh-String- und Zeichenliterale durch Leerzeichen
    ersetzen; Zeilenumbrueche bleiben stehen.  Gibt (bereinigt, fehler) zurueck."""
    out = []
    i = 0
    n = len(text)
    fehler = []
    while i < n:
        c = text[i]
        # Zeilenkommentar
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            j = text.find('\n', i)
            if j < 0:
                j = n
            out.append(' ' * (j - i))
            i = j
            continue
        # Blockkommentar (schachtelbar in Rust)
        if c == '/' and i + 1 < n and text[i + 1] == '*':
            tiefe = 1
            j = i + 2
            while j < n and tiefe > 0:
                if text[j] == '/' and j + 1 < n and text[j + 1] == '*':
                    tiefe += 1
                    j += 2
                elif text[j] == '*' and j + 1 < n and text[j + 1] == '/':
                    tiefe -= 1
                    j += 2
                else:
                    j += 1
            if tiefe > 0:
                fehler.append('unbeendeter Blockkommentar')
            for k in range(i, min(j, n)):
                out.append('\n' if text[k] == '\n' else ' ')
            i = j
            continue
        # Roh-String  r"..."  r#"..."#  br#"..."#
        m = re.match(r'(b?r)(#*)"', text[i:i + 40])
        if m and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')):
            hashes = m.group(2)
            ende = '"' + hashes
            j = text.find(ende, i + m.end())
            if j < 0:
                fehler.append('unbeendeter Rohstring')
                j = n
            else:
                j += len(ende)
            for k in range(i, j):
                out.append('\n' if text[k] == '\n' else ' ')
            i = j
            continue
        # normaler String
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '\\':
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            else:
                fehler.append('unbeendeter String')
            for k in range(i, min(j, n)):
                out.append('\n' if text[k] == '\n' else ' ')
            i = j
            continue
        # Zeichenliteral vs. Lebenszeit:  'a  vs  'x'  vs  '\n'
        if c == "'":
            m = re.match(r"'(\\.|[^\\'])'", text[i:i + 8])
            if m:
                out.append(' ' * m.end())
                i += m.end()
                continue
            out.append(' ')   # Lebenszeit / Marke -> harmlos
            i += 1
            continue
        out.append(c)
        i += 1
    return ''.join(out), fehler


# ------------------------------------------------------------ Rumpfextraktion

FN_RE = re.compile(r'\bfn\s+([A-Za-z_][A-Za-z0-9_]*)')


def klammer_ende(s, start):
    """start zeigt auf '{'.  Liefert Index NACH dem passenden '}' oder None."""
    tiefe = 0
    i = start
    n = len(s)
    while i < n:
        if s[i] == '{':
            tiefe += 1
        elif s[i] == '}':
            tiefe -= 1
            if tiefe == 0:
                return i + 1
        i += 1
    return None


def finde_rumpf_start(s, pos):
    """Ab `pos` (nach dem fn-Namen) das '{' des Rumpfs suchen.
    Liefert (index, 'ok') / (None, 'deklaration') / (None, 'abbruch')."""
    i = pos
    n = len(s)
    runde = eckig = spitz = 0
    grenze = pos + 4000
    while i < n and i < grenze:
        c = s[i]
        if c == '(':
            runde += 1
        elif c == ')':
            runde -= 1
        elif c == '[':
            eckig += 1
        elif c == ']':
            eckig -= 1
        elif c == '<':
            spitz += 1
        elif c == '>':
            if spitz > 0:
                spitz -= 1
        elif c == ';' and runde <= 0 and eckig <= 0:
            return None, 'deklaration'      # Trait-/extern-Signatur ohne Rumpf
        elif c == '{' and runde <= 0 and eckig <= 0:
            return i, 'ok'
        i += 1
    return None, 'abbruch'


def sammle_ruempfe(pfad):
    roh = open(pfad, 'r', encoding='utf-8', errors='replace').read()
    rein, fehler = bereinige(roh)
    zeilenstart = [0]
    for i, c in enumerate(rein):
        if c == '\n':
            zeilenstart.append(i + 1)

    def zeile_von(idx):
        lo, hi = 0, len(zeilenstart) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if zeilenstart[mid] <= idx:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    ruempfe = []
    abbrueche = list(fehler)
    for m in FN_RE.finditer(rein):
        b, zustand = finde_rumpf_start(rein, m.end())
        if zustand == 'deklaration':
            continue
        if zustand == 'abbruch':
            abbrueche.append('%s:%d kein Rumpfanfang' % (pfad, zeile_von(m.start())))
            continue
        e = klammer_ende(rein, b)
        if e is None:
            abbrueche.append('%s:%d Klammer geht nicht auf' % (pfad, zeile_von(m.start())))
            continue
        ruempfe.append({
            'datei': pfad,
            'name': m.group(1),
            'zeile': zeile_von(m.start()),
            'zeile_ende': zeile_von(e - 1),
            'rein': rein[b:e],
            'roh': roh[b:e] if len(roh) == len(rein) else None,
            'von': b, 'bis': e,
        })
    # geschachtelte fn (Hilfsfunktionen in Ruempfen) entfernen: nur aeusserste
    ruempfe.sort(key=lambda r: (r['von'], -r['bis']))
    aeussere = []
    for r in ruempfe:
        if aeussere and r['bis'] <= aeussere[-1]['bis']:
            continue
        aeussere.append(r)
    return aeussere, abbrueche, rein, roh


# ------------------------------------------------------------- Schleifensuche

LOOP_RE = re.compile(r'\b(for|while|loop)\b')


def schleifen_von(rumpf_rein):
    """Liefert Liste (art, kopf, rumpf_der_schleife, offset)."""
    res = []
    for m in LOOP_RE.finditer(rumpf_rein):
        art = m.group(1)
        # '{' des Schleifenrumpfs suchen (bei for/while: nach dem Kopf)
        i = m.end()
        n = len(rumpf_rein)
        runde = eckig = 0
        b = None
        while i < n and i < m.end() + 2000:
            c = rumpf_rein[i]
            if c == '(':
                runde += 1
            elif c == ')':
                runde -= 1
            elif c == '[':
                eckig += 1
            elif c == ']':
                eckig -= 1
            elif c == '{' and runde <= 0 and eckig <= 0:
                b = i
                break
            elif c == ';' and runde <= 0 and eckig <= 0:
                break
            i += 1
        if b is None:
            continue
        e = klammer_ende(rumpf_rein, b)
        if e is None:
            continue
        res.append({
            'art': art,
            'kopf': ' '.join(rumpf_rein[m.end():b].split()),
            'rumpf': rumpf_rein[b:e],
            'offset': m.start(),
        })
    return res


# ----------------------------------------------------- Domaenen und Kippmarken

# for x in EXPR  ->  EXPR faellt in eine der acht Domaenen?
DOMAENE_RE = re.compile(
    r'('
    r'\.\s*iter\s*\(|\.\s*iter_mut\s*\(|\.\s*into_iter\s*\(|'
    r'\.\s*chars\s*\(|\.\s*bytes\s*\(|\.\s*lines\s*\(|'
    r'\.\s*chunks\w*\s*\(|\.\s*windows\s*\(|\.\s*split\w*\s*\(|'
    r'\.\s*enumerate\s*\(|\.\s*zip\s*\(|\.\s*rev\s*\(|\.\s*take\s*\(|'
    r'\.\s*skip\s*\(|\.\s*step_by\s*\(|\.\s*filter\w*\s*\(|\.\s*map\s*\(|'
    r'\.\s*keys\s*\(|\.\s*values\w*\s*\(|\.\s*entries\s*\(|\.\s*drain\s*\(|'
    r'\.\s*copied\s*\(|\.\s*cloned\s*\(|\.\s*flatten\s*\(|\.\s*by_ref\s*\(|'
    r'\.\s*peekable\s*\(|\.\s*as_slice\s*\(|\.\s*to_vec\s*\(|'
    r'\.\.=?|'                       # Bereich a..b / a..=b  -> slots of
    r'^\s*&\s*\w|'                   # &slice
    r'^\s*\[|'                       # Literalfeld
    r')'
)

# N2: Schreiben eines Verkettungsfelds  (Zeigerchirurgie)
LINKFELDER = (r'next|prev|previous|next_sibling|prev_sibling|first_child|last_child|'
              r'head|tail|link|nxt|sibling|child|front|back|next_free|free_list|'
              r'next_ptr|prev_ptr|queue_next|list_next')
LINKSCHREIB_RE = re.compile(
    r'(?:\.|->)\s*(?:' + LINKFELDER + r')\s*(?:\[[^\]]*\])?\s*=(?!=)'
)
# Ein-/Aushaengeroutinen
CHIRURGIE_RUF_RE = re.compile(
    r'\b(unlink\w*|relink\w*|splice\w*|detach\w*|dequeue\w*|enqueue\w*|'
    r'insert_after\w*|insert_before\w*|remove_from\w*|push_front|push_back|'
    r'pop_front|pop_back|list_del|list_add|requeue\w*)\s*\('
)

# N1: Fortschritt am Zeiger statt an einer Domaene:  x = x.next  /  x = f(x)
KETTENLAUF_RE = re.compile(
    r'\b([A-Za-z_]\w*)\s*=\s*(?:unsafe\s*\{\s*)?(?:\(\s*\*\s*)?\1\s*(?:\.|->)\s*'
    r'(?:' + LINKFELDER + r')\b'
)
KETTENLAUF2_RE = re.compile(
    r'\b([A-Za-z_]\w*)\s*=\s*(?:\w+\s*(?:::|\.))*\w*(?:next|parent|sibling|child|succ|follow)\w*\s*\(\s*\1\b',
    re.IGNORECASE
)
# Deklarierte Kettendomaenen: CDT (chain(first_child,next_sibling), descendants of)
# und Seitentabellen (mappings of).  Diese Kettenlaeufe zaehlen NICHT als N1.
CDT_FELDER_RE = re.compile(r'(?:\.|->)\s*(?:first_child|next_sibling|parent)\b')
WALK_RE = re.compile(r'\b(pte|pml4|pdpt|pd|pt|entry|level|table)\w*\b', re.IGNORECASE)


def klassifiziere(rumpf):
    """Liefert (klasse, marken, details).  klasse in {'T','N','-'}"""
    schleifen = schleifen_von(rumpf['rein'])
    if not schleifen:
        return '-', [], []
    marken = set()
    details = []
    for s in schleifen:
        kopf = s['kopf']
        koerper = s['rumpf']
        lokal = []
        # --- Kopfpruefung
        if s['art'] == 'for':
            iterteil = kopf.split(' in ', 1)[1] if ' in ' in kopf else kopf
            if not DOMAENE_RE.search(iterteil):
                # kein erkennbarer Domaenenausdruck -> Kippfall
                if re.search(r'^\s*[A-Za-z_][\w:.]*\s*$', iterteil) or \
                   re.search(r'\.\s*\w+\s*\(\s*\)\s*$', iterteil):
                    lokal.append('N0-Kopf-unklar')
                else:
                    lokal.append('N0-Kopf-unklar')
        # --- N1 Kettenlauf
        k1 = KETTENLAUF_RE.search(koerper) or KETTENLAUF2_RE.search(koerper)
        if k1:
            treffer = k1.group(0)
            if CDT_FELDER_RE.search(treffer):
                pass                      # chain(first_child,next_sibling) ist Domaene
            else:
                lokal.append('N1-Kettenlauf')
        # --- N2 Zeigerchirurgie
        if LINKSCHREIB_RE.search(koerper) or CHIRURGIE_RUF_RE.search(koerper):
            lokal.append('N2-Zeigerchirurgie')
        if lokal:
            details.append({'art': s['art'], 'kopf': kopf[:120], 'marken': lokal})
            marken.update(lokal)
    if marken:
        return 'N', sorted(marken), details
    return 'T', [], details


# ---------------------------------------------------------------------- Lauf

def nichtleere_zeilen(text):
    return sum(1 for z in text.split('\n') if z.strip())


def lauf(wurzel, unterbaeume):
    dateien = []
    for ub in unterbaeume:
        p = os.path.join(wurzel, ub)
        for dp, _, fn in os.walk(p):
            if '/.git' in dp:
                continue
            for f in fn:
                if f.endswith('.rs'):
                    dateien.append(os.path.join(dp, f))
    dateien.sort()

    alle = []
    abbrueche = []
    gesamt_nichtleer = 0
    for d in dateien:
        roh = open(d, 'r', encoding='utf-8', errors='replace').read()
        gesamt_nichtleer += nichtleere_zeilen(roh)
        ruempfe, ab, _, _ = sammle_ruempfe(d)
        abbrueche.extend(ab)
        for r in ruempfe:
            kl, marken, det = klassifiziere(r)
            rel = os.path.relpath(d, wurzel)
            alle.append({
                'datei': rel,
                'name': r['name'],
                'zeile': r['zeile'],
                'zeile_ende': r['zeile_ende'],
                'zeilen': nichtleere_zeilen(r['rein']),
                'klasse': kl,
                'marken': marken,
                'schleifen': det,
            })
    return alle, abbrueche, gesamt_nichtleer, len(dateien)




# ----------------------------------------------------------------- Wortlisten

# Verkettungsfelder: ein Feld eines ELEMENTS, das ein anderes Element benennt.
LINK = (r'next|prev|previous|nxt|next_sibling|prev_sibling|first_child|last_child|'
        r'sibling|child|children|parent|link|qnext|qprev|next_free|free_next|'
        r'list_next|list_prev|queue_next|succ|pred|left|right|down|up')

# Felder, die zur CDT-Domaene gehoeren -> deklarierte Domaene
# chain(first_child, next_sibling) in slots  +  descendants of  (SPRACHE.md:381,400)
CDT_LINK = r'first_child|next_sibling|parent'

# Schreibziel = Elementauswahl UND Verkettungsfeld
#   a)  X[i]. … .link =        b)  X.link[i] =        c)  (*p).link =
CHIR_A = re.compile(r'([A-Za-z_][\w.]*)\s*\[[^\]]{0,80}\]\s*(?:\.\s*[A-Za-z_]\w*\s*)*'
                    r'\.\s*(' + LINK + r')\s*=(?!=)')
CHIR_B = re.compile(r'([A-Za-z_][\w.]*)\s*\.\s*(' + LINK + r')\s*\[[^\]]{0,80}\]\s*=(?!=)')
CHIR_C = re.compile(r'\(\s*\*\s*[A-Za-z_]\w*\s*\)\s*\.\s*(' + LINK + r')\s*=(?!=)')
CHIR_D = re.compile(r'[A-Za-z_]\w*\s*->\s*(' + LINK + r')\s*=(?!=)')

# Domaenenausdruecke im for-Kopf  ->  slots of / elems of / fields of / threads / …
DOM = re.compile(
    r'\.\s*(?:iter|iter_mut|into_iter|chars|bytes|lines|chunks\w*|windows|split\w*|'
    r'enumerate|zip|rev|take|take_while|skip|skip_while|step_by|filter\w*|map|flat_map|'
    r'keys|values|values_mut|entries|drain|copied|cloned|flatten|by_ref|peekable|'
    r'as_slice|as_bytes|to_vec|as_mut_slice|windows|repeat|once|chain)\s*\('
    r'|\.\.=?'                       # Bereich -> slots of
    r'|^\s*&\s*(?:mut\s+)?[\w.]'     # &slice / &mut slice -> elems of
    r'|^\s*\['                       # Feldliteral
)

LOOP_RE = re.compile(r'\b(for|while|loop)\b')

# Fortschritt am Zeiger:  x = x.link   /   x = f(x)
CHAIN_STEP = re.compile(r'\b([A-Za-z_]\w*)\s*=\s*(?:unsafe\s*\{)?\s*(?:Some\s*\()?\s*'
                        r'\1\s*\.\s*(' + LINK + r')\b')


def schleifen(rein):
    res = []
    for m in LOOP_RE.finditer(rein):
        i, n = m.end(), len(rein)
        runde = eckig = 0
        b = None
        while i < n and i < m.end() + 3000:
            c = rein[i]
            if c == '(':
                runde += 1
            elif c == ')':
                runde -= 1
            elif c == '[':
                eckig += 1
            elif c == ']':
                eckig -= 1
            elif c == '{' and runde <= 0 and eckig <= 0:
                b = i
                break
            elif c == ';' and runde <= 0 and eckig <= 0:
                break
            i += 1
        if b is None:
            continue
        e = klammer_ende(rein, b)
        if e is None:
            continue
        res.append({'art': m.group(1), 'kopf': ' '.join(rein[m.end():b].split()),
                    'rumpf': rein[b:e]})
    return res


def marken_von(rein):
    """Liefert (marken, belege)."""
    marken = set()
    belege = []
    # --- N2 / N2d : Zeigerchirurgie
    for rx, name in ((CHIR_A, 'A'), (CHIR_B, 'B'), (CHIR_C, 'C'), (CHIR_D, 'D')):
        for m in rx.finditer(rein):
            treffer = ' '.join(m.group(0).split())
            feld = m.group(2) if rx in (CHIR_A, CHIR_B) else m.group(1)
            if re.fullmatch(CDT_LINK, feld):
                marken.add('N2d')
                belege.append('N2d ' + treffer)
            else:
                marken.add('N2')
                belege.append('N2 ' + treffer)
    # --- N1 : Schleife ueber eine Nicht-Domaene
    for s in schleifen(rein):
        if s['art'] == 'for':
            it = s['kopf'].split(' in ', 1)[1] if ' in ' in s['kopf'] else s['kopf']
            if not DOM.search(it):
                marken.add('N1')
                belege.append('N1 for … in ' + it[:70])
        else:
            m = CHAIN_STEP.search(s['rumpf'])
            if m:
                if re.fullmatch(CDT_LINK, m.group(2)):
                    pass                      # chain(…)/descendants of ist Domaene
                else:
                    marken.add('N1')
                    belege.append('N1 Kettenschritt ' + ' '.join(m.group(0).split()))
    return sorted(marken), belege


def ruempfe_von(pfad):
    roh = open(pfad, 'r', encoding='utf-8', errors='replace').read()
    rein, fehler = bereinige(roh)
    zs = [0] + [i + 1 for i, c in enumerate(rein) if c == '\n']

    def zeile(idx):
        lo, hi = 0, len(zs) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if zs[mid] <= idx:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    roh_liste = roh.split('\n')
    treffer, abbruch = [], list(fehler)
    for m in FN_RE.finditer(rein):
        b, z = finde_rumpf_start(rein, m.end())
        if z == 'deklaration':
            continue
        if z == 'abbruch':
            abbruch.append('%s:%d kein Rumpfanfang' % (pfad, zeile(m.start())))
            continue
        e = klammer_ende(rein, b)
        if e is None:
            abbruch.append('%s:%d Klammer geht nicht auf' % (pfad, zeile(m.start())))
            continue
        treffer.append({'name': m.group(1), 'z0': zeile(m.start()), 'z1': zeile(e - 1),
                        'rein': rein[b:e], 'von': b, 'bis': e})
    treffer.sort(key=lambda r: (r['von'], -r['bis']))
    aussen = []
    for r in treffer:
        if aussen and r['bis'] <= aussen[-1]['bis']:
            continue
        aussen.append(r)
    return aussen, abbruch, roh_liste


TESTMOD = re.compile(r'#\[cfg\(test\)\]|#\[test\]|#\[cfg\(all\(test')


def testbereiche(pfad):
    """Zeilenbereiche von #[cfg(test)] mod … { … } — grob, ueber Klammerabgleich."""
    roh = open(pfad, 'r', encoding='utf-8', errors='replace').read()
    rein, _ = bereinige(roh)
    zs = [0] + [i + 1 for i, c in enumerate(rein) if c == '\n']

    def zeile(idx):
        lo, hi = 0, len(zs) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if zs[mid] <= idx:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1
    ber = []
    for m in re.finditer(r'#\[cfg\(test\)\]\s*(?:pub\s+)?mod\s+\w+\s*\{', rein):
        b = rein.index('{', m.start())
        e = klammer_ende(rein, b)
        if e:
            ber.append((zeile(m.start()), zeile(e - 1)))
    return ber


def lauf(wurzel, unterbaeume):
    dateien = []
    for ub in unterbaeume:
        for dp, _, fn in os.walk(os.path.join(wurzel, ub)):
            if '/.git' in dp:
                continue
            for f in sorted(fn):
                if f.endswith('.rs'):
                    dateien.append(os.path.join(dp, f))
    dateien.sort()
    ergebnis, abbrueche = [], []
    zeilen_gesamt = zeilen_nichtleer = zeilen_test = 0
    for d in dateien:
        rel = os.path.relpath(d, wurzel)
        roh = open(d, 'r', encoding='utf-8', errors='replace').read()
        rl = roh.split('\n')
        zeilen_gesamt += len(rl) - (1 if rl and rl[-1] == '' else 0)
        zeilen_nichtleer += nichtleere_zeilen(roh)
        tb = testbereiche(d)
        for (a, b) in tb:
            zeilen_test += sum(1 for i in range(a - 1, min(b, len(rl))) if rl[i].strip())
        rp, ab, _ = ruempfe_von(d)
        abbrueche.extend(ab)
        for r in rp:
            mk, bl = marken_von(r['rein'])
            im_test = any(a <= r['z0'] <= b for (a, b) in tb)
            ergebnis.append({'datei': rel, 'name': r['name'], 'z0': r['z0'], 'z1': r['z1'],
                             'zeilen': nichtleere_zeilen(r['rein']),
                             'marken': mk, 'belege': bl[:6], 'test': im_test,
                             'hat_schleife': bool(schleifen(r['rein']))})
    return ergebnis, abbrueche, zeilen_gesamt, zeilen_nichtleer, zeilen_test, len(dateien)


def bericht(erg, ab, zg, znl, zt, nd, nur_prod=False):
    if nur_prod:
        erg = [r for r in erg if not r['test']]
        basis = znl - zt
        etikett = 'ohne Testmodule'
    else:
        basis = znl
        etikett = 'ganzer Baum'
    kern = [r for r in erg if 'N1' in r['marken'] or 'N2' in r['marken']]
    kipp = [r for r in erg if r['marken']]
    zk = sum(r['zeilen'] for r in kern)
    zi = sum(r['zeilen'] for r in kipp)
    print('--- %s ---' % etikett)
    print('Dateien %d | Zeilen roh %d | nicht leer %d | Testmodule (nicht leer) %d'
          % (nd, zg, znl, zt))
    print('Bezugsgroesse (nicht leer): %d' % basis)
    print('Funktionsruempfe: %d   davon mit Schleife: %d'
          % (len(erg), sum(1 for r in erg if r['hat_schleife'])))
    print('N-KERN  (N1|N2):        %3d Ruempfe  %5d Zeilen  %.3f %%'
          % (len(kern), zk, 100.0 * zk / basis))
    print('N-KIPP  (+N2d):         %3d Ruempfe  %5d Zeilen  %.3f %%'
          % (len(kipp), zi, 100.0 * zi / basis))
    print('ABBRUECHE: %d' % len(ab))
    return kern, kipp, basis



# Vollstaendig aus der Feldnamen-Erhebung (siehe Befehlszeile im Protokoll):
# Felder, die ein ANDERES Element derselben Sammlung benennen.
LINK = LINK + r'|sc_donor|sc_donee|queued|handler_pd'

# --- Verkettungsfelder, die eine der ACHT Domaenen deckt -------------------
# chain(first_child, next_sibling) in slots / descendants of  -> CDT
# queue <place>                                               -> Bereitliste
# mappings of <place>                                         -> Seitentabelle
DOM_LINK_ABSTIEG = r'first_child|next_sibling|qnext|qprev'
# `parent` deckt KEINE Domaene: Gabbro hat `descendants of`, kein `ancestors of`.

# --- Strukturen mit deklarierbarer Domaene (fuer die Nb1/Nb2-Trennung) -----
DOM_STRUKT = re.compile(r'\bmdb\b|\bslots\s*\[|\bqueues\s*\[|\btcbs\s*\[|self\.next\s*\[')

# --- Zeigerchirurgie: Elementauswahl UND Verkettungsfeld -------------------
CHIR = [
    re.compile(r'([A-Za-z_][\w.]*)\s*\[[^\]]{0,80}\]\s*(?:\.\s*[A-Za-z_]\w*\s*)*'
               r'\.\s*(' + LINK + r')\s*=(?!=)'),                     # X[i]….link =
    re.compile(r'([A-Za-z_][\w.]*)\s*\.\s*(' + LINK + r')\s*\[[^\]]{0,80}\]\s*=(?!=)'),  # X.link[i] =
    re.compile(r'\(\s*\*\s*([A-Za-z_]\w*)\s*\)\s*\.\s*(' + LINK + r')\s*=(?!=)'),        # (*p).link =
    re.compile(r'([A-Za-z_]\w*)\s*->\s*(' + LINK + r')\s*=(?!=)'),                       # p->link =
]
# Schreiben ueber eine &mut-gebundene Elementvariable
CHIR_REF = re.compile(r'\b([a-z_]\w*)\s*\.\s*(' + LINK + r')\s*=(?!=)')
REF_BIND = re.compile(r'let\s+(?:mut\s+)?([a-z_]\w*)\s*(?::[^=]{0,60})?=\s*&\s*mut\s+[^;]*\[')

# --- Kettenschritt in while/loop ------------------------------------------
KETTE = re.compile(r'\b([A-Za-z_]\w*)\s*(?<![=!<>])=(?!=)\s*[^;{}=]{0,70}?\.\s*(' + LINK + r')\s*(?:;|\)|,|\.)')
# Indexkette:  x = A[x]  -- ein Feld, dessen Elemente Indizes IN DASSELBE Feld halten.
# `slots of A` liefert die Elemente, nicht die Kette; keine der acht Domaenen deckt das.
IDXKETTE = re.compile(r'\b([A-Za-z_]\w*)\s*(?<![=!<>])=(?!=)\s*([A-Za-z_][\w.]*)\s*\[\s*\1\b[^\]]{0,20}\]')
IDXSCHREIB = None
# Kettenlauf ueber eine KANTENFUNKTION:  let Some(n) = f(x) … ; x = n
# Keine der acht Domaenen deckt eine Kette, die erst durch einen Aufruf entsteht.
KANTENKETTE = re.compile(r'Some\s*\(\s*([A-Za-z_]\w*)\s*\)\s*(?<![=!<>])=(?!=)\s*([A-Za-z_]\w*)\s*'
                         r'\(\s*([A-Za-z_]\w*)\s*\)')


def marken(rein, idxfelder=()):
    mk, bel = set(), []
    # ---- Zeigerchirurgie
    ziele = []
    for rx in CHIR:
        for m in rx.finditer(rein):
            ziele.append((' '.join(m.group(0).split()), m.group(2)))
    refs = set(REF_BIND.findall(rein))
    for m in CHIR_REF.finditer(rein):
        if m.group(1) in refs:
            ziele.append((' '.join(m.group(0).split()), m.group(2)))
    for treffer, feld in ziele:
        if DOM_STRUKT.search(treffer):
            mk.add('Nb2')
            bel.append('Nb2 ' + treffer)
        else:
            mk.add('Nb1')
            bel.append('Nb1 ' + treffer)
    # ---- Kettenlauf ohne Domaene
    for s in schleifen(rein):
        if s['art'] == 'for':
            continue
        for m in KETTE.finditer(s['rumpf']):
            feld = m.group(2)
            if re.fullmatch(DOM_LINK_ABSTIEG, feld):
                continue
            mk.add('Na')
            bel.append('Na ' + ' '.join(m.group(0).split()))
            break
        m = IDXKETTE.search(s['rumpf'])
        if m:
            mk.add('Na')
            bel.append('Na Indexkette ' + ' '.join(m.group(0).split()))
        for m in KANTENKETTE.finditer(s['kopf'] + ' ; ' + s['rumpf']):
            neu, fn_, alt = m.group(1), m.group(2), m.group(3)
            # Nur wenn der Rumpf die Laufvariable WIRKLICH auf das Ergebnis setzt.
            # Ein blosser Aufruf im Rumpf ist ein Nachschlagen, kein Kettenschritt.
            if re.search(r'\b' + re.escape(alt) + r'\s*(?<![=!<>])=(?!=)\s*'
                         + re.escape(neu) + r'\b', s['rumpf']):
                mk.add('Na')
                bel.append('Na Kantenkette ' + ' '.join(m.group(0).split()))
                break
    # ---- Chirurgie an einem indexverketteten Feld
    for feld in idxfelder:
        rx = re.compile(r'\b' + re.escape(feld) + r'\s*\[[^\]]{0,40}\]\s*=(?!=)')
        m = rx.search(rein)
        if m:
            mk.add('Nb1')
            bel.append('Nb1 Indexkette-Schreiben ' + ' '.join(m.group(0).split()))
    return sorted(mk), bel


def lauf(wurzel, unterbaeume=('kernel', 'crates')):
    dat = []
    for ub in unterbaeume:
        for dp, _, fn in os.walk(os.path.join(wurzel, ub)):
            if '/.git' in dp:
                continue
            for f in sorted(fn):
                if f.endswith('.rs'):
                    dat.append(os.path.join(dp, f))
    dat.sort()
    erg, ab = [], []
    z_roh = z_nl = z_test = 0
    for d in dat:
        rel = os.path.relpath(d, wurzel)
        roh = open(d, 'r', encoding='utf-8', errors='replace').read()
        rl = roh.split('\n')
        z_roh += len(rl) - (1 if rl and rl[-1] == '' else 0)
        z_nl += nichtleere_zeilen(roh)
        tb = testbereiche(d)
        for (a, b) in tb:
            z_test += sum(1 for i in range(a - 1, min(b, len(rl))) if rl[i].strip())
        rp, abb, _ = ruempfe_von(d)
        ab.extend(abb)
        idxf = set()
        for r in rp:
            for m in IDXKETTE.finditer(r['rein']):
                idxf.add(m.group(2).split('.')[-1])
        for r in rp:
            mk, bl = marken(r['rein'], idxf)
            erg.append({'datei': rel, 'name': r['name'], 'z0': r['z0'], 'z1': r['z1'],
                        'zeilen': nichtleere_zeilen(r['rein']), 'marken': mk,
                        'belege': bl[:8],
                        'test': any(a <= r['z0'] <= b for (a, b) in tb),
                        'schleifen': len(schleifen(r['rein']))})
    return erg, ab, z_roh, z_nl, z_test, len(dat)


def zeige(erg, ab, z_roh, z_nl, z_test, nd, prod=False):
    e = [r for r in erg if not r['test']] if prod else erg
    basis = (z_nl - z_test) if prod else z_nl
    N = [r for r in e if r['marken']]
    buch = [r for r in e if 'Na' in r['marken'] or 'Nb1' in r['marken']]
    zn, zb = sum(r['zeilen'] for r in N), sum(r['zeilen'] for r in buch)
    print('%-16s Ruempfe %4d | mit Schleife %3d | Bezug %6d nicht-leere Zeilen'
          % ('OHNE TESTS' if prod else 'GANZER BAUM', len(e),
             sum(1 for r in e if r['schleifen']), basis))
    print('   BUCHSTABE (Na+Nb1): %2d Ruempfe %5d Z  %.3f %%'
          % (len(buch), zb, 100.0 * zb / basis))
    print('   BERICHTET (+Nb2)  : %2d Ruempfe %5d Z  %.3f %%'
          % (len(N), zn, 100.0 * zn / basis))
    print('   Abbrueche: %d' % len(ab))
    return N, buch, basis




if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        raise SystemExit(2)
    w = sys.argv[1]
    erg, ab, zr, zn, zt, nd = lauf(w)
    print('Dateien %d | roh %d | nicht leer %d | Testmodule %d\n' % (nd, zr, zn, zt))
    N, B, basis = zeige(erg, ab, zr, zn, zt, nd, prod=False)
    print()
    zeige(erg, ab, zr, zn, zt, nd, prod=True)
    print('\n--- Liste (berichtet), nach Datei:Zeile ---')
    for r in sorted(N, key=lambda x: (x['datei'], x['z0'])):
        print('%s:%d  %s  [%s]  %d Zeilen%s'
              % (r['datei'], r['z0'], r['name'], ','.join(r['marken']),
                 r['zeilen'], '  (Testmodul)' if r['test'] else ''))
        for x in r['belege'][:3]:
            print('        ' + x[:100])
    for a in ab:
        print('  ! ABBRUCH ' + a)
    for arg in sys.argv:
        if arg.startswith('--json='):
            json.dump({'r': erg, 'ab': ab, 'z_roh': zr, 'z_nl': zn, 'z_test': zt},
                      open(arg[7:], 'w'), ensure_ascii=False, indent=1)
