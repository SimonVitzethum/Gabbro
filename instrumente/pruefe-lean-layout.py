#!/usr/bin/env python3
"""Guardian: every folder holding Lean files holds at most 20 entries and every module is placed (Simon, 2026-10-05).

Reads the rules in `lean-layout-rules.py`; the verdict is the exit code of `lean-layout.py --check`.
`--selbsttest` proves the instrument can fall: a synthetic folder of 21 entries must be refused.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def selbsttest():
    src = (HERE / 'lean-layout.py').read_text().split('def main')[0]
    g = {'__file__': str(HERE / 'lean-layout.py')}
    exec(compile(src, 'lean-layout', 'exec'), g)
    files = [f'grammatik/Probe/F{i:02d}.lean' for i in range(21)]
    zu_voll = g['overfull'](files)
    ok = [f'grammatik/Probe/F{i:02d}.lean' for i in range(20)]
    if not zu_voll or g['overfull'](ok):
        print('SELBSTTEST ROT: der Waechter erkennt einen vollen Ordner nicht (oder meldet einen leeren)')
        return 1
    print('SELBSTTEST GRUEN: 21 Eintraege werden abgelehnt, 20 nicht')
    return 0


if __name__ == '__main__':
    if '--selbsttest' in sys.argv:
        sys.exit(selbsttest())
    sys.exit(subprocess.call([sys.executable, str(HERE / 'lean-layout.py'), '--check']))
