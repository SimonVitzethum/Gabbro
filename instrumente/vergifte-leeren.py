#!/usr/bin/env python3
"""Poison twin of the emitted `gabbro_region_leeren`: puts the FIRST version's arithmetic back
(`bis` formed in uint64_t before the test, wraps for a range inside one page).
usage: vergifte-leeren.py IN.c OUT.c  -- refuses if the corrected shape is not in IN.c."""
import sys

neu = ("lo = (a + seite - 1u) / seite * seite;\nhi = (a + bytes) / seite * seite;\n"
       "if (lo < hi) {\nvon = lo - a;\nbis = hi - a;")
alt = ("von = (a + seite - 1u) / seite * seite - a;\nbis = (a + bytes) / seite * seite - a;\n"
       "if (von < bis) {")
s = open(sys.argv[1]).read()
if neu not in s:
    sys.exit("the emitted helper no longer has the corrected shape this probe poisons")
open(sys.argv[2], "w").write(s.replace(neu, alt))
