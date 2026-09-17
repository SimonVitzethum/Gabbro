# Ruling record: admission batch of lane-143 (2026-09-11)

Status: ruled. Seven forms admitted with price, no emitter change (all
existing emission byte-identical by construction). Per-form rulings with
folds live in their own notes; this file records the batch decision and
the two unruled admissions.

## Admitted with priced rulings (see per-form notes)

- `cInline`: `messung/CFORM-REGEL-INLINE.md` (non-binding inline request).
- `cConst`: `messung/CFORM-REGEL-CONST.md` (read-only qualifier).
- `deref`: `messung/CFORM-REGEL-DEREF.md` (plain dereference).
- `adressVon`: `messung/CFORM-REGEL-ADRESSE.md` (provenance-carrying address).
- `bitNicht`: `messung/CFORM-REGEL-TILDE.md` (double-cast width rule).

## Admitted unruled (step-4 batch)

- `schrittStmt`: no user spelling exists to refuse; `+= 1` rewrite would
  churn every loop for zero semantic difference.
- `cSizeof`: checker already refuses layout-less `sizeof` by name;
  remaining sites carry declared layout.

Units proving each admission emit and compile in
`messung/proben/emission-143/` with `EVIDENCE.md`.
