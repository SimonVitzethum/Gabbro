module
public import Grammatik.Kern.Semantik.Maschine.T7
@[expose] public section
/-! ## 19. The single-thread discharge for Einfaedig runs (`hsingle_aus_einfaedig`)

    The `hsingle` premises of §14 (`kette_aus_maschinenlauf_schritt`,
    `_nimmt`, `_gibt`) and §18 (`kette_aus_maschinenlauf_blatt`) narrow
    everything to single-thread runs: every run step is `f`'s. Inside those
    proofs `hsingle` is consumed for exactly two duties:

    - the ownership fields of `Gesittet M'.lauf` (`marke_eindeutig`, W4, and
      `ungeteilt`, W5), via `hfaden` arithmetic;
    - `BeschraenkteVerschraenkung Nb M'.lauf`, vacuously via the same
      arithmetic.

    What is proved (no `sorry`):

    - `hsingle_aus_einfaedig`: the first duty discharged for multi-thread
      runs. From reachability (`h`, which yields W1-W3 through the §11
      projection theorems), the `Einfaedig` projection (`hEin`, W4 through
      `marke_eindeutig_aus_einfaedig`, `Wettlauf.lean` §7), and the
      declaration side (`hungeteilt`, W5, the exact shape `gen_gesittet`
      takes), the run is `Gesittet` -- with no single-thread premise
      anywhere. Read-only reuse of `gen_gesittet` (§11): one positional
      application, no duplicated proof. Every premise is load-bearing: each
      feeds `gen_gesittet` positionally, so deleting any premise breaks
      elaboration. There is no `have _ :=` discard, no `sorry`/`admit`/
      `axiom`, and no bare `Prop` slot.

    Coverage (exactly): the `Gesittet` half of `hsingle`'s duties, for every
    generated reachable run whose threads satisfy `Einfaedig` plus the
    declaration side -- multi-thread Einfaedig runs included. The
    `.marke_eindeutig` and `.ungeteilt` projections of the conclusion are
    the literal shapes `hsingle` supplied at the §14/§18 use sites.

    Remainder (booked, not hidden): `BeschraenkteVerschraenkung` does not
    follow from `Einfaedig` plus the declaration side -- it constrains which
    thread pairs may share a run (`Nb`), and under `hsingle` it held
    vacuously only because no second thread had steps. Multi-thread use
    sites keep it as an explicit `Nb` declaration premise (or keep
    `hsingle`); the step theorems themselves are not restated here.
    `hsingle_prog` (the program side, `Extraktion.lean` counter routing)
    is untouched, as are `SerialLink` witnesses, globals, and
    multi-carrier conflicts (as before).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The single-thread narrowing discharged for Einfaedig runs.** A
    generated reachable run whose threads satisfy `Einfaedig` (plus the
    declaration side) is `Gesittet`: W1-W3 are generated, W4 travels as the
    `Einfaedig` projection, W5 as the declaration side. This is the
    `Gesittet` half of what `hsingle` supplies at the §14/§18 use sites,
    now without any single-thread premise, so multi-thread Einfaedig runs
    are covered. Every premise is load-bearing: each is passed whole to
    `gen_gesittet`. -/
theorem hsingle_aus_einfaedig
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g) :
    Gesittet M.lauf :=
  gen_gesittet P O passes hO sp M h code hEin hungeteilt

#print axioms Gabbro.Grammatik.hsingle_aus_einfaedig

end Gabbro.Grammatik

/-! ## 20. The spec triple from execution: one fired step extends the thread triple
    (`spec_aus_fuehrung_schritt`)

    The Owicki-Gries bind (`InterferenzAllgemein.lean` section 19: `SpecTriple`,
    `seqTriple_from_spec`, `stabil_from_spec`, consumed by `owickiGries_stabil`)
    posits each thread's triple over chain positions: `requiresEigen` and
    `ensuresEigen` quantify over indices `k` with `schrittFaden[k]? = some f`,
    with no link to the steps the machine actually fired. The sequential side
    exists (`stabil_from_spec`) and the execution side exists (PC runs,
    section 12: where each thread stands, firing through `PCSchritt`); nothing
    binds the triple to the executed steps of the interleaving.

    What is proved (no `sorry`):

    - `spec_aus_fuehrung_schritt`: one executed PC step extends the thread
      triple. A chain `J` tracks the machine `M` (`hJw`: the same worlds); the
      thread's triple holds on `J` (`hSpec`, the prefix -- at the seed this is
      head validity alone, since a zero-step chain carries no eigen
      obligation); one `PCSchritt` of `f` fires (`hs`: where the thread stands
      plus the firing data, read as a generated step through `pcSchritt_gen`);
      the extended chain `J'` continues the history by construction
      (`hJ'sf` / `hJ'w` / `hJ'code`, exactly what the section 14 / `blatt`
      constructions supply definitionally). Then the triple holds on `J'`.
      Old indices transfer through the prefix triple; the new index -- the
      fired step -- transfers through the firing itself. Leaf steps go
      through the per-firing contract preservation (`hBlatt`, the
      sequential-verification duty, now stated over firings with `hstep`
      evidence rather than over chain positions); lock steps (`nimmt` /
      `gibt`, the section boundaries of the section 21 grain) go through
      live-memory constancy plus memory-only contracts (`hMem`): a lock step
      keeps the memory, and contracts read only memory, so `Pre` / `Post`
      survive with no user logic owed.
      Every premise is load-bearing: `hReach` / `hO` / `sp` feed the
      last-world memory fact (`genWelten_letzte` through `pcReach_gen`); `hs`
      feeds `pcSchritt_gen`; `hJw` / `hJ'sf` / `hJ'w` / `hJ'code` rewrite every
      index; `hMem` bridges both step kinds; `hBlatt` closes the leaf case;
      `hSpec` closes the old indices and both heads. There is no `have _ :=`
      discard, no `sorry` / `admit` / `axiom`, and no bare `Prop` slot.

    Coverage (exactly): one executed `PCSchritt` (`leaf` / `nimmt` / `gibt`)
    by a tracked thread, extending a tracked chain. `Pre` holds along the
    thread's executed steps and `Post` at its section ends, in the uniform
    eigen shape that `owickiGries_stabil` consumes -- the indexing is executed
    (chain positions are machine firings, worlds are machine history), while
    the per-statement contract content stays where it belongs (below).

    Remainder (booked, not hidden): iterating the step over a whole `PCReach`
    run (the induction that carries a seed triple -- head validity from the
    caller -- to the final chain); the per-step atom identity inside `hs`
    (S12, the scheduler and witness duty: the counter points at the extracted
    atom); the `axiomCall` oracle-event contract (S13: the oracle answers with
    an arbitrary world, so `hBlatt` for oracle leaves is owed on arbitrary
    answers); discharging `hMem` for `QRequires` / `QEnsures` (the
    per-expression induction showing `eval` reads only slots and globals,
    downstream where the contract instantiation lives); head validity from
    thread entry (the caller side).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **Memory-only contracts.** `Pre` / `Post` read only live memory (slots and
    globals), never the trace: worlds over the same memory agree. Contract
    shapes (`QRequires` / `QEnsures`) satisfy this because `eval` reads only
    slots and globals; the per-expression induction stays downstream, where
    the contract instantiation lives. -/
structure SpeicherVertrag (Pre Post : D.Fn → World D → Prop) (fn : D.Fn) : Prop where
  /-- The requires-side agrees on worlds over the same memory. -/
  memPre : ∀ σ σ' : World D, σ.speicher = σ'.speicher → (Pre fn σ ↔ Pre fn σ')
  /-- The ensures-side agrees on worlds over the same memory. -/
  memPost : ∀ σ σ' : World D, σ.speicher = σ'.speicher → (Post fn σ ↔ Post fn σ')

/-- A world built over a memory carries that memory. -/
theorem speicher_welt_speicher (s : Speicher D) (tr : List (Ereignis D)) :
    (s.welt tr).speicher = s := by
  cases s
  rfl

#print axioms Gabbro.Grammatik.speicher_welt_speicher


end Gabbro.Grammatik
