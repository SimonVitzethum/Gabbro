# OPUS lane `rahmen` — the last piece of part 4's condition, and it was about locks

*2026-09-15. Task: decide with a MEASUREMENT whether the one named frame hypothesis of
`rufAt_nurAbstieg` can go — (a) `HeldB` for reachable worlds, (b) the frame without
`rufAt_gut`, or (c) a world where it is FALSE — take the honest route, say what it costs,
and witness it on a LOCKED program.*

## 0. The answer in one line

**Route (b), and the hypothesis is gone.** The frame half of the handler discipline holds at
EVERY world, for every program, with no lock discipline anywhere in the premise — because
the lock discipline is spent entirely on the trace QUALITY half of `Gut`, and never on the
frame or on the held set. `schlusssatz` clause 4e(ii) is now unconditional, and what is left
of part 4's condition is the DEPTH residue of 4e(i) alone.

## 1. THE MEASUREMENT that picked the route

Before writing a line of proof I counted where the premise `HeldB bo Λ σ.haelt` is actually
USED in `Satz.lean`'s grammar-wide induction. `Gut W G σ σ'` is three facts:

| fact | what `HeldB` buys it | where |
|---|---|---|
| `Rahmen W G σ σ'` — no write outside the contract | **nothing** | every write case passes its own `hw : V.schreibt t = true`; `rahmen_storeSlot`/`rahmen_storeGlob` take no lock argument |
| `σ'.haelt = σ.haelt` — every lock given back | **nothing** | `gut_nimmt_gibt`'s second component never touches its `hn` argument |
| every new event `Ereignis.gut`, `Konsistent` preserved | **everything** | `Ereignis.gut (.zugriff t _ Λ h)` is `darf D t Λ ∧ HeldIn Λ h`; `Ereignis.gut (.nimmt L h)` is the strict rank order and `L ∉ h` |

That is the whole finding. `RufRahmenTreu` asks for the first two facts and `rufAt_gut`
delivers all three, so it asks for a premise it does not need. **Route (c) is therefore
false** and route (a) — a reachability argument for `HeldB` — would have been both harder
and weaker (it would prove the clause only for worlds a certified program reaches, where the
theorem quantifies over all of them).

**The sharpest single line of the measurement**, and it decides the `locks` case:

```
offen (gibt L :: nimmt L h :: s) = (L :: offen s).erase L = offen s
```

`List.erase` removes the FIRST occurrence, and that is the one `nimmt` just put there. So a
world that **already holds `L`** — a world no disciplined program reaches, and one `Gut`
rightly refuses, because its `nimmt` event is not good — still gets its held set back
unchanged. The frame and the held set survive a world the lock discipline does not accept.
*That asymmetry is the entire reason the premise was removable, and it is a fact about
`offen`, not about programs.*

## 2. What was built

| file | what |
|---|---|
| `grammatik/Grammatik/RahmenTreu.lean` | **new**, 668 lines — `Treu`, the leaf lemmas, `TreuAusgang`/`TreuEnd`, the three loop combinators, the mutual induction `stmt_treu`/`block_treu`/`end_treu`/`arms_treu`/`grund_treu`, and `rufAt_treu` |
| `grammatik/Grammatik/RufLogik.lean` | `rufAt_rahmenTreu` and `rufAt_respektiertRahmen` added; `rufAt_nurAbstieg` lost the hypothesis `hRT` and took `TreuO O` in place of `RahmenO O`; `rufRahmenTreu_ohneSperren` **deleted** with the gap it measured |
| `grammatik/Grammatik/RufLogikZeuge.lean` | `heldB_faellt_104`, `nurAbstieg_zeuge_104` (the LOCKED witness) added; `stufen8`/`rahmenTreu_108` deleted; `nurAbstieg_zeuge_108` keeps its statement as the lock-free control |
| `grammatik/Grammatik/Schlusssatz.lean` | clause 4e(ii) lost its hypothesis; docstring and CUTS rewritten |
| `grammatik/Grammatik/CParser/Bruecke.lean` | `schlusssatz_text` restates the conclusion — the same change |
| `grammatik/Grammatik.lean` | one import |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §6.9 table corrected, new §6.10 |
| `dokumente/SATZKARTE.md` | new §37, §36 marked superseded in part |

**Not touched:** `Satz.lean` (see §6), `Semantik.lean`, `HandlerKongruenz.lean`,
`RufTiefe.lean`, `Zielsatz/`, `Schlusssatz104.lean`, `Schlusssatz124.lean`,
`KorrespondenzAllg.lean`, `CFormen*` (the aggregates lane), `Parser/` (the Muse lanes),
`instrumente/pruefe-cformen.py`, any corpus file, any diagnostic code, any emission counter,
any Rust source.

### The theorem

```lean
def Treu (W : D.Tab → Bool) (G : D.Glob → Bool) (σ σ' : World D) : Prop :=
  Rahmen W G σ σ' ∧ σ'.haelt = σ.haelt

def TreuO (O : Orakel D) : Prop :=        -- the first two conjuncts of `GutO`, i.e. H1
  ∀ a σ ρ, Rahmen (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 ∧
    (O.wirkt a σ ρ).1.haelt = σ.haelt

def TreuR (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ σ', (R f σ ρ).welt = some σ' → Treu (D.schreibt f) (D.gschreibt f) σ σ'

theorem stmt_treu : ∀ (s : Stmt D V l Γ Λ Λ') (σ : World D) (ρ : Env D Γ),
    TreuAusgang V.schreibt V.gschreibt σ (execStmt O passes R s σ ρ)     -- + block/end/arms/grund

theorem rufAt_treu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O) :
    ∀ fuel, TreuR (rufAt P O passes fuel)

theorem rufAt_rahmenTreu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O) :
    ∀ n : Nat, RufRahmenTreu P (rufAt P O passes n)
```

**No premise on the program, the user's logic, the world, the floors or the depth.** Not
`StufenOk`, not `GutO`'s trace shape, not `HeldB`. The ONE premise is the hardware's, and it
is `GutO`'s own first two conjuncts, so at every call site `gutO_treuO hH.1` supplies it out
of the goal theorem's named hardware assumptions.

`stmt_treu`'s statement is `stmt_gutB`'s with **four** binders deleted (`bo`, `hbV`, `hbo`,
`hh`) — the floor bookkeeping goes with the lock discipline, because floors exist only to
order lock ranks.

## 3. Clause by clause: what disappeared from `schlusssatz`, and what remains

The premise list of `schlusssatz` is **unchanged character for character**. One implication
vanished from the conclusion, so the theorem is strictly stronger:

```diff
-      ((∀ passes n : Nat, RufRahmenTreu K.E.P (rufAt K.E.P O passes n)) →
-        ∀ (passes n : Nat) (f …) (σ …) (ρG …) (e : Logik …),
-          ReqAmEintritt K.E.P f σ ρG → rufAt K.E.P O passes n f σ ρG = .logik e →
-            ∃ h, e = .abstieg h)) ∧
+      (∀ (passes n : Nat) (f …) (σ …) (ρG …) (e : Logik …),
+          ReqAmEintritt K.E.P f σ ρG → rufAt K.E.P O passes n f σ ρG = .logik e →
+            ∃ h, e = .abstieg h)) ∧
```

Part 4's condition `(rufAt … n f σ ρG).istFehler = false`, kind by kind, across the three
lanes that worked on it:

| outcome kind | 2026-09-15 morning (§6.8) | after lane `kongruenz` (§6.9) | after THIS lane (§6.10) |
|---|---|---|---|
| `hardware` — all five forms | **discharged** (4b) | discharged | discharged |
| `Logik.vorbedingung` of a CALLEE | open | discharged (`KoerperGutS` cl. 1, caller duty) | discharged |
| `Logik.nachbedingung` | open | discharged (`KoerperGutS` cl. 1, body triple) | discharged |
| `Logik.invariante` | open | discharged (`InvGutS`) | discharged |
| `Logik.schleife` / `.vorzustand` / `.bereich` | open | discharged (`KoerperGutS` cl. 2) | discharged |
| `Logik.vorbedingung` of the CALL ITSELF | open | it IS `ReqAmEintritt` (4d) | unchanged |
| `Logik.abstieg` | open | **stays**, stable upwards (4e(i)) | **stays** — the only residue |
| *the frame hypothesis carrying the four rows above* | — | `RufRahmenTreu`, NAMED | **proved, gone** |

So: **of the seven `Logik` constructors, six are discharged onto the clause of the user's
own duty that owns them, the seventh is the depth, and the side condition that carried the
six is no longer a side condition.** What a chain author owes for part 4 is now one
computation at one depth — `rufAt_stabil_ab` carries it upward from there.

Statements held at or above their old strength:

| theorem | statement |
|---|---|
| `gabbro_ziel` | **not edited**; `#print axioms` `[propext, Classical.choice, Quot.sound]` |
| `schlusssatz_104` | **not edited** |
| `schlusssatz_124` | **not edited** |
| `schlusssatz` | premises identical, one implication removed from the conclusion — **strictly stronger** |
| `schlusssatz_text` | the same, and its proof is still the one-liner |

## 4. The witness, on a LOCKED program

`Kette104.nurAbstieg_zeuge_104`. 104 declares `lock M protects { stand } rank 0`, and BOTH
its functions carry `requires Held(M)`, so `Signatur.anfang D4 (D4.signatur ein4)` names
`Res.held m4`. The world the chain's own headline witness runs from (`sp4.welt []`, the
declared zero memory with an empty trace) holds **nothing**:

```lean
theorem heldB_faellt_104 :
    ¬ HeldB (D4.signatur ein4).boden (Signatur.anfang D4 (D4.signatur ein4))
        (sp4.welt []).haelt
```

That is PROVED, not assumed. At that world `rufAt_gut` says nothing at all — and 104's own
chain witness (`kette_104_zeuge`, which moves the slot `0 → 100` and constrains every C run)
starts exactly there. **The gap was not hypothetical; it sat under the corpus's reference
program.**

Non-degeneracy, three ways, all in the one theorem:

1. the entry world **fails** `HeldB` (above);
2. the run RETURNS and moves memory: `rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok wEin ()`
   with `(wEin.slots t4 0 f4).n = 100`;
3. the frame is read on the function that may **not** write: `D4.schreibt lies4 t4 = false`,
   and `lies(k, 0)` from `wEin` returns with
   `Rahmen (D4.schreibt lies4) (D4.gschreibt lies4) wEin σ''`,
   `offen σ''.spur = offen wEin.spur` and the slot still at `100`. The frame clause there
   forbids something that could have happened — the one table of the declaration, at a
   nonzero value.

`nurAbstieg_zeuge_108` keeps its statement as the **lock-free control**: it was already
unconditional yesterday, and it still is, now for a different reason.

## 5. What the route needs from the checker Bool — NOTHING NEW

The task asked for this to be named precisely if it came up. **It did not.** `rufAt_treu`
and `rufAt_rahmenTreu` are theorems about the semantics and take no checker fact at all;
`rufAt_nurAbstieg` still needs `(P.rumpf f).ohneLocks = true`, and that is the SAME
`korrOk_ohneLocks` reading of the SAME certificate check that lane `kongruenz` introduced —
no new decision, no new diagnostic code, no change to `Akzeptiert`, so
`instrumente/pruefe-akzeptiert-diff.py` has nothing new to hold together. The Rust side is
untouched by this lane.

*If a later lane wants clause 4e(ii) for programs that DO carry `locks` statements in a
body, that is where a checker question would appear — `korrOk_ohneLocks` is the reason the
obligation's `execEndH` and the model's `execEnd` agree, and it would have to be replaced by
a lock-aware agreement, not by a checker flag. That is the next name on the list, and it is
not this lane's.*

## 6. What did NOT have to move, and why that is a result

**`Satz.lean` was not edited.** The tempting alternative was to generalise `stmt_gutB` in
place — to conclude `Treu ∧ (HeldB → Gut)` — and it would have touched the one file every
adequacy, non-interference and machine-G proof reads. A parallel induction in a new file
costs 668 lines once; a changed central statement costs a re-verification of everything
downstream and a merge conflict with every lane in flight. The two inductions are not a
duplication that can drift: `Gut.treu` (one line) says the old theorem implies the new one
at every world where both apply, so a future change to `Satz.lean` that breaks the frame
would break `Gut.treu` too.

**`Semantik.lean` was not edited.** As with the congruence: the theorem went through because
the semantics already has the property. No error had to be caught, no outcome added.

## 7. Build cost, measured on `ki-pc-fisch-101` (`gabbro-opus-rahm`, 6-slot queue)

| what | jobs | wall | peak RSS |
|---|---|---|---|
| whole library BEFORE the lane, cold (`.lake` seeded from `stage/lake3`; master had moved, so this is a real rebuild) | 262 | 3 min 30 s | — |
| whole library AFTER the lane, warm no-op | 263 | 20 s | 3,04 GB |
| whole library AFTER the lane, **COLD** (`.lake` deleted and re-seeded from `stage/lake3`) | 263 | **162 s** | **6,60 GB** |
| `RahmenTreu.lean` alone, warm `LEAN_PATH` | — | **2,13 s** | 0,63 GB |

**The lane costs one job and two seconds.** The cold figures sit inside the band the lane
before it measured (262 jobs, 153 s, 6,67 GB, same machine, different neighbours under the
6-slot queue) and inside OFFEN O13's booked ~5 min at 6,5 GB. `cargo build` was run only to
give `zaehle-kette.py` a binary; no Rust source was touched.

## 8. The guardian numbers

- **Chain count: 2 of 113**, `instrumente/zaehle-kette.py --lean` on fisch (sieve totals
  (a) 2, (b) 15, (c) 15, (d) 60, (e) 2) — unchanged, as expected: neither a chain instance
  nor the parser was touched.
- `grep -c sorry` over the whole cold build log: **0**.
- `#print axioms` over the cold build log: `gabbro_ziel`, `schlusssatz`, `schlusssatz_104`,
  `schlusssatz_124`, `schlusssatz_text` and every new theorem of this lane at the standard
  three (`heldB_faellt_104`, purely computational, at `[propext, Quot.sound]`).

## 9. Standards

- No `sorry`, no `admit`, no `native_decide`, no new `axiom` (grep over the whole diff).
- `#print axioms` on every new theorem: `[propext, Classical.choice, Quot.sound]`
  (`heldB_faellt_104`, purely computational: `[propext, Quot.sound]`).
- `#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel`, `… .schlusssatz`,
  `… .schlusssatz_104`, `… K124.schlusssatz_124`, `… CParser.schlusssatz_text`: the standard
  three, **unchanged**.
- Every new ∀-over-syntax theorem has a witness: `rufAt_treu`/`rufAt_rahmenTreu` through
  `nurAbstieg_zeuge_104` (locked) and `nurAbstieg_zeuge_108` (lock-free).
- Chain count: **2 of 113**, re-measured with `--lean` on fisch (the instances and the
  parser were not touched).
- Guardians re-run against a stashed baseline of the same worktree, so the comparison is a
  measurement and not a hope: `pruefe-zahlen.py` **27 findings before and after**,
  `pruefe-todo.py` **14 before and after**, `pruefe-englisch.py`'s three broken ratchets
  break identically on the baseline. `pruefe-gestalt.py` goes **198 → 199**: the new file is
  "neu, nicht gebucht" in the shape ratchet -- and so are `HandlerKongruenz.lean`,
  `RufLogik.lean`, `RufTiefe.lean`, `KorrOkOhneLocks.lean` and `RufLogikZeuge.lean` from
  yesterday's lane. That ledger is stale wholesale, not by this lane; it is named here
  rather than quietly stepped over.

## 10. What a reviewer should check

- `git diff master -- grammatik/Grammatik/Schlusssatz.lean` — the premise list is untouched;
  the only change to the conclusion is the removal of ONE implication inside clause 4e(ii).
  The conjunct INDICES do not move, so `Kette108.lean`, `CText108.lean` and
  `Kette104Satz.lean` needed no edit and got none.
- `RahmenTreu.lean` against `Satz.lean` §3: every case is the `Gut` case with the `HeldB`
  arguments deleted. If a reader suspects a case was WEAKENED rather than freed, the test is
  `Gut.treu`: the new conclusion is implied by the old one, so the new induction cannot be
  proving something the old one did not.
- `treu_nimmt_gibt` versus `gut_nimmt_gibt` — the one place where the two proofs genuinely
  differ, and the docstring says why.
- `heldB_faellt_104` — the witness's claim that `rufAt_gut` is silent at the chain's entry
  world is a theorem, not a remark.
- No emission counter, no diagnostic code, no corpus file, no gift number was touched.
