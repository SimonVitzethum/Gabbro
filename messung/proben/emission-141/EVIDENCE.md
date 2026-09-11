# Emission-141 evidence: direct byte operations with the run bound

Two units under `messung/proben/emission-141/`, one per direction. Each checks
clean, emits with exit 0, and the emitted C compiles under GCC 16.2.1
`-std=c11 -Wall -Wextra -Werror` at `-O0` and `-O2` and runs to exit 0.

| unit | pruefe | emit | cc -O0 | cc -O2 | run -O0 | run -O2 |
|---|---|---|---|---|---|---|
| `emission-141-lesen.gab` | 0 errors, 0 hints | exit 0 | clean | clean | exit 0 | exit 0 |
| `emission-141-schreiben.gab` | 0 errors, 0 hints | exit 0 | clean | clean | exit 0 | exit 0 |

Emitted-C shapes (inspected, not only compiled):

- Constant index stays plain: `PUFFER[3]`, `PUFFER[3] = v;`, `t.bytes[2] = 66;`.
- Dynamic read carries the run bound:
  `((uint64_t)(i) < 16u ? PUFFER[(uint64_t)(i)] : (__builtin_trap(), (uint8_t)0))`.
- Dynamic write binds the index once and traps past the bound:
  `{ uint64_t _gabbro_i = (uint64_t)(s->len); if (!(_gabbro_i < 16u)) __builtin_trap(); s->bytes[_gabbro_i] = b; }`.
- `narrow`, `requires`, compound ops and the `format` readers are untouched.

Byte identity: old vs new `gabbro emit` over all 647 `.gab` files under
`beispiele/` and `messung/proben/` -- zero exit-code diffs, and exactly one C
diff: `beispiele/32-zeichenkette.gab`, whose two dynamic accesses
(`s.bytes[i]`, `s.bytes[s.len] = b`) take the new arms. Its new C still
passes `cc -fsyntax-only` at `-O0`/`-O2`. No exchange arm, no refusal site
and no other lowering changed.
