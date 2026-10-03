# Task-brief audit batch B20 (lanes 1031-1045)

Auditor: lane 1073. Scope: the 15 embedded brief bodies (HARD RULES preamble
excluded; preamble passed a central mechanical check over all 300 files).
Each brief was checked against: (1) distinct proof obligation, (2) OWN ONLY
scope and file collisions, (3) author/reviewer shape, (4) lane/clone/branch
match, (5) HARD RULES compliance. No brief was modified.

## Top list of BLOCKING items

None. No brief in this batch would fail gates or collide. There is no
BLOCKING item to list.

## General notes (apply to all 15 briefs)

- N1 — Reviewer-shaped briefs. All 15 briefs are report-only exact reviews
  ("OWN ONLY MUSE-REPORT-NNN.md", "no source or live controls"). The
  author-side sub-criteria (new-module OWN ONLY, ZEUGE target, reuse lists,
  diagnostic/gift/example numbers) are not applicable to them: a reviewer
  mints no numbers and adds no module, so there is nothing to collide and
  nothing invented. Verified: no brief names a diagnostic, gift, or example
  number, and none names a Lean module file.
- N2 — Template uniformity is not duplication. The 15 bodies are
  word-identical except lane number, clone/branch, author ID, and rule name.
  The proof obligation differs in each case (a different optimiser rule under
  review, quoted per brief below), so criterion (1) passes for every brief.
  Overlapping background checklist text (byte forms, REX, flags, TSO) means
  some duplicated reviewer reading effort across the batch, but that is an
  efficiency observation, not a gate defect.
- N3 — Reserved optimiser paths. AGENTS.md reserves
  `grammatik/Grammatik/X86/OptimizationRules.lean` and
  `OptimizationWitnesses.lean` for the friend handoff. Neither file exists in
  this tree (checked: no `Optimization*.lean` under `grammatik/Grammatik/X86/`,
  which holds 143 other modules). The review briefs pin no author file list,
  so each reviewer must confirm as part of "inspect the exact pinned
  snapshot" that its author candidate (881-895) touches no reserved path.
  This is covered by the briefs' existing inspection duty; no brief change
  is needed.
- N4 — Reviewer/author pairing is a uniform intra-batch offset
  (reviewer = author + 150: 1031->881 through 1045->895). This differs from
  the older wave convention (author + 18) but is self-consistent across all
  15 briefs and matches each brief's own CANDIDATE line, so it is not a
  defect. Allocation authority remains the live coordinator registry.

## Per-brief verdicts

- 1031 (rematerialisation rule; reviews author 881): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1031.md"; "FIRST verify clone
  /home/simon/Dokumente/gabbro-muse/a1031, branch muse/1031" matches header
  1031; "CANDIDATE: 881 <full pinned HEAD>, exactly one VERDICT: ACCEPT or
  REPAIR"; architecture checklist present ("byte forms,
  REX/register/width/flag semantics ... interaction with canonical
  execution"); "No network, provider, other clones or keys", queued wrappers
  for reproduction, commit through commit.sh.
- 1032 (chain scheduling rule; reviews author 882): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1032.md"; clone a1032 / branch muse/1032 match
  header 1032; "CANDIDATE: 882 <full pinned HEAD>", one VERDICT
  ACCEPT-or-REPAIR; full architecture checklist; no-network / queued-wrapper
  / commit.sh clauses present.
- 1033 (loop alignment rule; reviews author 883): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1033.md"; clone a1033 / branch muse/1033 match
  header 1033; "CANDIDATE: 883 <full pinned HEAD>", one VERDICT; architecture
  checklist; HARD RULES compliant clauses present.
- 1034 (branch bias rule; reviews author 884): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1034.md"; clone a1034 / branch muse/1034 match
  header 1034; "CANDIDATE: 884 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1035 (zero-idiom selection rule; reviews author 885): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1035.md"; clone a1035 / branch muse/1035 match
  header 1035; "CANDIDATE: 885 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1036 (LEA selection rule; reviews author 886): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1036.md"; clone a1036 / branch muse/1036 match
  header 1036; "CANDIDATE: 886 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1037 (shift selection rule; reviews author 887): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1037.md"; clone a1037 / branch muse/1037 match
  header 1037; "CANDIDATE: 887 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1038 (multiply selection rule; reviews author 888): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1038.md"; clone a1038 / branch muse/1038 match
  header 1038; "CANDIDATE: 888 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1039 (division guard rule; reviews author 889): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1039.md"; clone a1039 / branch muse/1039 match
  header 1039; "CANDIDATE: 889 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1040 (SETcc selection rule; reviews author 890): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1040.md"; clone a1040 / branch muse/1040 match
  header 1040; "CANDIDATE: 890 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1041 (CMOV selection rule; reviews author 891): SHIPPABLE. Evidence:
  "OWN ONLY MUSE-REPORT-1041.md"; clone a1041 / branch muse/1041 match
  header 1041; "CANDIDATE: 891 <full pinned HEAD>", one VERDICT; architecture
  checklist; compliant clauses present.
- 1042 (MOV-immediate selection rule; reviews author 892): SHIPPABLE.
  Evidence: "OWN ONLY MUSE-REPORT-1042.md"; clone a1042 / branch muse/1042
  match header 1042; "CANDIDATE: 892 <full pinned HEAD>", one VERDICT;
  architecture checklist; compliant clauses present.
- 1043 (address-mode selection rule; reviews author 893): SHIPPABLE.
  Evidence: "OWN ONLY MUSE-REPORT-1043.md"; clone a1043 / branch muse/1043
  match header 1043; "CANDIDATE: 893 <full pinned HEAD>", one VERDICT;
  architecture checklist; compliant clauses present.
- 1044 (call-argument selection rule; reviews author 894): SHIPPABLE.
  Evidence: "OWN ONLY MUSE-REPORT-1044.md"; clone a1044 / branch muse/1044
  match header 1044; "CANDIDATE: 894 <full pinned HEAD>", one VERDICT;
  architecture checklist; compliant clauses present.
- 1045 (return-path selection rule; reviews author 895): SHIPPABLE.
  Evidence: "OWN ONLY MUSE-REPORT-1045.md"; clone a1045 / branch muse/1045
  match header 1045; "CANDIDATE: 895 <full pinned HEAD>", one VERDICT;
  architecture checklist; compliant clauses present.

## Summary

15 of 15 briefs SHIPPABLE, 0 SHIPPABLE-WITH-NOTES, 0 BLOCKING. No brief was
modified. Nothing in any brief violates the HARD RULES (isolation,
no-network, queued wrappers, report-only ownership, commit.sh, English).
