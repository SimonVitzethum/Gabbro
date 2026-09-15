/-
  File:      Grammatik/Schlusssatz.lean
  Subject:   THE CLOSING THEOREM, STAGE (a), GENERIC (plan
             `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2, §6):
             `schlusssatz`, for EVERY source text whose chain data check.

  `schlusssatz_104` (Schlusssatz104.lean) is about one program: its parser
  is keyed to 104's declaration (`lowerProg`), its correspondence check
  fixes 104's rows (`certOkG`), its model judgement and its machine are
  104's by hand. Here every piece is the generic one:

  * THE PARSER: `uebersetzeAllg` -- lex, parse, the lane-162
    preprocessing (`pre108`: `concurrent` stripped, bare `u32` as its
    range), elaborate, and the GENERIC lowering `lowerAllg` onto the
    declaration built from the source itself (`declOf u`). One function
    for every source text; its output is the program everything below is
    about.
  * THE CHECKER: the goal theorem's form -- the program is an `Einheit`
    (code, lock invariants, axiom ensures, declared starts, initial
    memory, Zielsatz/Spec.lean) and the checker's Bool is
    `akzeptiert_pruefer.akzeptiert` (Zielsatz/Akzeptiert.lean), decided.
  * THE USER'S LOGIC: `NutzerPflicht` -- the goal theorem's premise (b).
  * THE CORRESPONDENCE CERTIFICATE: `korrOk` (KorrespondenzAllg.lean), T2
    proper: one Bool for every program over the covered forms, sound at
    every call depth (`korrOk_fnCorr`).
  * THE MACHINE: `P.mitRuhe`, the goal theorem's generic idle root
    (MitRuhe.lean) -- no hand-written `gPB`: `rufAt_mitRuhe` is the generic
    form of `gPB_wie_gP`, `ziel_ort_einfaden_ende` the single-thread
    machine statement, `gabbro_ziel` the concurrent one for the declared
    starts.

  A CLOSED CHAIN for a source text is a value `Kette src`: the parse
  result, the `Einheit` built on it, the checker's Bool, the user's proof,
  the emitter's layout and the correspondence certificate with its check.
  Every field is a Lean proposition about the program or data, decided or
  proved; nothing about the world outside Lean. `schlusssatz` turns every
  `Kette src` into the six parts of §6, under the NAMED hypotheses that
  are about the world outside: A1 (with A2, A3) on the binary's behaviour,
  A4 as the single-threaded start (`EinFadenStart`), and the hardware
  assumptions of the goal theorem (c) on the oracle.
-/
import Grammatik.KorrespondenzAllg
import Grammatik.Parser.UebersetzeAllg2
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik

open Parser Parser.Uebersetze Parser.UebersetzeAllg Parser.UebersetzeAllg2 Zielsatz

/-! ## 1. The Lean pipeline, for every source text -/

/-- **THE LEAN TRANSLATION PIPELINE**: lex, parse, preprocess (`pre108`:
    `concurrent` items stripped -- they carry the declared starts, which the
    `Einheit` holds --, bare `u32` as its full range), elaborate, lower
    GENERICALLY onto the declaration built from the source. Every stage a
    Lean function; nothing Rust. -/
def uebersetzeAllg (s : String) :
    Except String (Σ u : UProg, Programm (declOf u) × List (declOf u).Fn) :=
  match lex s with
  | .error _ => .error "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => .error e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => .error e
      | .ok u =>
        match lowerAllg u with
        | .error e => .error e
        | .ok (P, fs) => .ok ⟨u, P, fs⟩

/-- **PARSE FIDELITY FROM A SOURCE PINNED AS CHARACTERS**, stage by stage.
    The four premises are the four stages of `uebersetzeAllg`; the
    conclusion is the pipeline on the `String` the chain is indexed by.

    WHY IT EXISTS, and it is a MEMORY statement, not a proof one (O13):
    unfolding `uebersetzeAllg` at a CONCRETE source makes `simp` look at
    the discriminant `lex src`, and whnf of that runs Lean 4.33's UTF-8
    decoder over the whole text in the kernel -- measured 2026-09-15 on
    `ki-pc-fisch-101` at **70 GB for `Kette104`** (the cold full build
    died with `code 137` on a 16 GB machine). Here `l` is a VARIABLE, so
    there is nothing to decode: `lex_ofList` carries the pin across by
    the core lemmas `String.toList_ofList`/`String.length_ofList`, and
    every stage arrives as a hypothesis. A chain instance applies this
    lemma and the decoder is never run at all.

    Nothing is weakened. The conclusion is the SAME proposition the
    hand-written `unfold`/`rw` script proved -- `uebersetzeAllg src`
    for the chain's own `src` --, and `src = String.ofList l` holds by
    definition, so a guardian comparing the pieces `l` against the file
    still decides whether the chain is about this program. -/
theorem uebersetzeAllg_von_zeichen {l : List Char} {toks : List Token}
    {items : List SItemTief} {u : UProg} {P : Programm (declOf u)}
    {fs : List (declOf u).Fn}
    (hl : lexL l = .ok toks)
    (hp : parseTopTief toks = .ok items)
    (he : elabU (pre108 items) = .ok u)
    (hw : lowerAllg u = .ok (P, fs)) :
    uebersetzeAllg (String.ofList l) = .ok ⟨u, P, fs⟩ := by
  unfold uebersetzeAllg
  rw [lex_ofList, hl]
  dsimp only
  rw [hp]
  dsimp only
  rw [he]
  dsimp only
  rw [hw]

/-- A successful computation is `.ok` of its extracted value (how a chain
    instance names the parser's output without retyping it). -/
theorem except_ok_get {ε α : Type} {x : Except ε α} (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.get h) := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok a => rfl

/-- The functions of a generically lowered program are numbered. -/
instance instDecEqDeclOfFn (u : UProg) : DecidableEq (declOf u).Fn :=
  inferInstanceAs (DecidableEq (Fin u.fns.length))

/-- The C function number of a generically lowered function: its position
    among the source's `impl fn`s (the printer numbers them the same way). -/
def fnNr {u : UProg} (f : (declOf u).Fn) : Nat := Fin.val (n := u.fns.length) f

/-! ## 2. Stage (a): one active thread -/

/-- **A4, SINGLE-THREADED** (stage (a)). The machine runs `E.P.mitRuhe` from
    * `lader` -- the loader's memory: the program's declared initial memory;
    * `ruhe` -- every thread but `0` runs the runtime's idle root;
    * `treiber` -- thread `0` runs what the driver (not emitted) calls:
      nothing, or one source function whose `requires` holds at the initial
      memory with the driver's arguments and which has no reason exits.
    Unlike `Laufzeit` (the goal theorem's (d)), the one active thread may
    run a function that holds locks by signature -- no other thread can
    contend for them. -/
structure EinFadenStart {D : Deklaration} (E : Einheit D) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) : Prop where
  lader : sp = speicherR E.sp0
  ruhe : ∀ u, u ≠ 0 → init u = ⟨none, .nil⟩
  treiber : init 0 = ⟨none, .nil⟩ ∨ ∃ (f : D.Fn) (ρ : Env D (D.params f)),
    init 0 = ⟨some f, envR ρ⟩ ∧ ReqAmEintritt E.P f (E.sp0.welt []) ρ ∧ D.gruende f = 0

/-- The runtime's idle root is idle (`ruhig`, the Bool `ziel_ort_einfaden` reads). -/
theorem ruhig_ruhe {D : Deklaration} (P : Programm D) : ruhig P.mitRuhe none = true := by
  unfold ruhig
  rw [fussOrteG_mitRuhe_ruhe]
  rfl

section Einfaden

variable {D : Deklaration} [DecidableEq D.Fn]

/-- **THE MACHINE WITH ONE ACTIVE THREAD, from the goal theorem's premises**:
    the checker's facts (`AkzeptiertSpec`), the user's logic
    (`NutzerPflicht`), the hardware assumptions and the single-threaded
    start give, on every machine of `E.P.mitRuhe` reachable at every
    budget: memory safety (`SpurInv`), the contracts at every logged event,
    the lock invariants, no thread stuck at a `logik` check, progress at a
    check, the owed invariants at returns, the root function's `ensures` at
    its completion and no reason exit of it (`ziel_ort_einfaden_ende`). -/
theorem einfaden_ziel (E : Einheit D) (fs : Aufzaehlung D.Fn)
    (hA : AkzeptiertSpec E.P E.S fs.1 E.ws) (hN : NutzerPflicht E) (O : Orakel D)
    (hH : HardwareAnnahmen O E.Q) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hA4 : EinFadenStart E sp init) :
    ∀ (passes : Nat) (M : RufMaschineG D.mitRuhe),
      RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M →
        SpurInv M ∧
        ((VertragAmOrtG E.P.mitRuhe M ∧ SperrInvG E.S.mitRuhe M ∧ KeinLogikHaltG O.mitRuhe passes M ∧
          ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
            AnPruefungG M t → ∃ M', RufSchrittG E.P.mitRuhe O.mitRuhe passes M t M') ∧
          InvAmOrtG E.P.mitRuhe M) ∧ StartEndeG E.P.mitRuhe M ∧ KeinStartGrundG M := by
  intro passes M hr
  have hA' := akzeptiertSpec_mitRuhe E.P fs.2 hA
  have hL := logikPflicht_mitRuhe hN.logik
  have hH' := hardware_mitRuhe hH
  have hRuhe : ∀ u, u ≠ 0 → ruhig E.P.mitRuhe (init u).1 = true := by
    intro u hu
    rw [hA4.ruhe u hu]
    exact ruhig_ruhe E.P
  have hStart : StartGut E.P.mitRuhe sp init := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rcases hA4.treiber with h | ⟨f, ρ, h, hreq, -⟩
      · rw [h]; rfl
      · rw [h, hA4.lader]
        exact (req_mitRuhe_iff E.P f (E.sp0.welt []) ρ).mpr hreq
    · rw [hA4.ruhe t ht]; rfl
  have hSstart : ∀ L, E.S.mitRuhe.inv L sp = true := by
    intro L
    show E.S.inv L (speicherZ sp) = true
    rw [hA4.lader, speicherZ_speicherR]
    exact hN.start.sperren L
  have hGrund : StartOhneGrund init := by
    intro t
    by_cases ht : t = 0
    · subst ht
      rcases hA4.treiber with h | ⟨f, ρ, h, -, hg⟩
      · rw [h]; rfl
      · rw [h]; exact hg
    · rw [hA4.ruhe t ht]; rfl
  exact ⟨spurInv_erreichbar hH'.1 sp init hr,
    ziel_ort_einfaden_ende E.P.mitRuhe O.mitRuhe (axEnsRuhe E.Q) E.S.mitRuhe (fsRuhe fs.1) sp init
      hH'.1 hH'.2.1 hH'.2.2 hL.2.2 ⟨hA'.sperrOrte, hL.2.1⟩ (fsRuhe_voll fs.2) hA'.frag hRuhe
      (fun pa f => (hL.1 pa f).1) hStart hSstart (fun pa f => (hL.1 pa f).2.1) hGrund passes M hr⟩

end Einfaden

/-! ## 2b. What part 4's condition is, and what it can no longer be

    Part 4 (and part 6 through it) is conditional on the Gabbro call ending
    in NO MODEL ERROR (`istFehler = false`). The model knows two error
    outcomes: the writer's logic and an assumption about the machine
    (`Semantik.lean`). The second one is discharged for every chain, and
    syntactically: the five forms whose outcome is `hardware` -- an axiom
    call, an axiom bind, a register read in either shape, an `awaits`, a
    `forever` budget -- are all outside the certificate check's covered set,
    so a program with a certificate carries none of them, so `rufAt` never
    ends in one, at any depth, against any oracle
    (`korrOk_rufAt_ohneHardware`, KorrespondenzAllg.lean §5, over
    `rufAt_ohneHardware`).

    What is LEFT of the condition is the writer's logic, and the two lemmas
    here say what its first case is: at any depth above `0` the very first
    thing `rufAt` does is test the callee's `requires` at the entry world,
    so the condition IMPLIES the caller's duty `ReqAmEintritt` -- the
    theorem hands the C side ANY Gabbro world and ANY arguments, and a
    callee with a non-trivial `requires` fails at most of them. That is not
    a defect of the model; it is the condition being stated on the
    COMPUTATION where the contract would do. -/

/-- **`rufAt`'s gate IS the entry contract.** The requires test stands at
    the world after the entry read, and a read only appends trace events;
    an expression reads carriers, so the two tests are the same Bool. -/
theorem rufAt_tor {D : Deklaration} (P : Programm D) (f : D.Fn) (σ : World D)
    (ρ : Env D (D.params f)) :
    wahr? (eval (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) (P.requires f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ) =
      wahr? (eval σ (P.requires f) σ ρ) := by
  rw [eval_gleichAuf (S := (P.requires f).orte) (P.requires f) (fun _ h => h)
    (GleichAuf.lese_links (GleichAuf.refl _ σ) _ _) ρ]

/-- **A call at a depth above `0` whose entry contract fails IS a model
    error** -- so part 4's condition implies the caller's duty. -/
theorem rufAt_vorbedingung {D : Deklaration} (P : Programm D) (O : Orakel D) (passes n : Nat)
    (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (h : ¬ ReqAmEintritt P f σ ρ) :
    rufAt P O passes (n + 1) f σ ρ = .logik (.vorbedingung f) := by
  simp only [rufAt]
  rw [if_pos]
  rw [rufAt_tor]
  simpa [ReqAmEintritt] using h

/-! ## 3. A closed chain -/

/-- **A CLOSED CHAIN for the source text `src`**: everything the closing
    theorem needs that is a Lean proposition about the program -- the parse
    result, the program as an `Einheit`, the checker's Bool, the user's
    proof, the correspondence certificate and its check. The fields of the
    `Einheit` other than the code (`S`, `Q`, `starts`, `sp0`) are data a
    reviewer reads next to the source: the exporter does not fill them
    (Zielsatz/Spec.lean, NOT CLAIMED), so the chain names them. -/
structure Kette (src : String) where
  /-- The elaborated program (the parser's output). -/
  u : UProg
  /-- The program as the goal theorem's unit: its code IS the parser's. -/
  E : Einheit (declOf u)
  fs0 : List (declOf u).Fn
  /-- PARSE FIDELITY: the source text translates, in Lean, to `E.P`. -/
  uebersetzt : uebersetzeAllg src = .ok ⟨u, E.P, fs0⟩
  fs : Aufzaehlung (declOf u).Fn
  ls : Aufzaehlung (declOf u).Lock
  cs : Aufzaehlung ((declOf u).Tab ⊕ (declOf u).Glob)
  /-- The checker's Bool, on `E` (the goal theorem's (a)). -/
  akzeptiert : akzeptiert_pruefer.akzeptiert E fs.1 ls.1 cs.1 = true
  /-- The user's logic (the goal theorem's (b)). -/
  nutzer : NutzerPflicht E
  /-- The emitter's layout of the declaration (table blocks, records). -/
  EL : EmitLay (declOf u)
  /-- The correspondence certificate (`gabbro corr-lean`, generic section). -/
  zert : KCert (declOf u)
  /-- The certificate checks against the parsed program (T2). -/
  zertOk : korrOk EL fnNr zert E.P fs.1 = true

/-! ## 4. THE CLOSING THEOREM, STAGE (a) -/

/-- **`schlusssatz` -- THE CLOSING THEOREM, STAGE (a), for every source text
    with a closed chain.** PREMISES: a closed chain `K : Kette src` (all Lean
    propositions about the program, see `Kette`), and the NAMED hypotheses
    about the world outside Lean:

    * `hH` -- the hardware assumptions of the goal theorem (c) on the oracle
      `O` (foreign code keeps its frame, registers read their carriers,
      axiom answers meet their declared `ensures`);
    * `hXR` -- foreign calls of the C side are functional (the emitted unit
      of a chain in the covered forms makes none; the premise keeps the
      statement honest for units that would);
    * `hA1` -- A1 with A2 and A3, as a hypothesis: every run of the binary's
      function `f` (`bin f`, the behaviour of the compiled code, a parameter)
      is a run of the C semantics of the unit the certificate elaborates to
      (`kProg K.zert`), at the emitter's layout (`K.EL.lay`), at the call
      depth `tief f` its call tree needs;
    * `hA4` -- A4, single-threaded: the loader's memory is the declared
      initial memory, every thread but `0` idles, thread `0` runs what the
      driver calls.

    CONCLUSIONS -- the six parts of §6, for the program `K.E.P` the parser
    produced:
    1. PARSE FIDELITY: `src` translates to `K.E.P`;
    2. THE CERTIFICATES: the checker's Bool holds and means `AkzeptiertSpec`;
       the correspondence certificate checks against `K.E.P`;
    3. THE MODEL JUDGEMENT: the user's logic at every budget and the start
       obligation (`NutzerPflicht`);
    4. EVERY C RUN: for every function, depth and budget, from a C state and
       C arguments related to ANY Gabbro world and arguments: when the Gabbro
       call ends in no model error, the C call has a run and EVERY run of it
       ends related to the Gabbro outcome;
    4b. NO HARDWARE ERROR: part 4's condition can never fail for a machine
       reason. A certified program carries none of the five forms whose
       outcome is `hardware` (`korrOk_rufAt_ohneHardware`), so `rufAt` never
       ends in one -- at any depth, any budget, any world, any arguments,
       against any oracle. This is NOT the goal theorem's premise (c) doing
       the work: `HardwareAnnahmen` is conditional on the raw answer fitting
       the declared type and leaves the error standing
       (`befund_hardware_bleibt`, RufOhneHardwareZeuge.lean);
    4c. WHAT IS LEFT of part 4's condition is the WRITER'S LOGIC alone --
       `vorbedingung`, `nachbedingung`, `invariante`, `abstieg`, and the two
       body-own kinds `schleife`/`vorzustand`/`bereich`;
    4d. AND ABOVE DEPTH `0` the condition IMPLIES the caller's duty: the
       entry contract of the called function at the given world and
       arguments. Parts 4 and 6 quantify over ANY Gabbro world and ANY
       arguments, and `rufAt`'s first act is the `requires` test, so a
       callee with a non-trivial `requires` fails at most of them. That is
       the condition being stated on the COMPUTATION where the contract
       would do;
    5. THE MACHINE: `K.E.P.mitRuhe` behaves as `K.E.P` at every depth; on
       every machine reachable from the single-threaded start, at every
       budget, memory safety and the goal theorem's contract legs hold,
       including the root function's `ensures` at its completion; and for
       every start of the goal theorem's runtime shape (the DECLARED starts,
       concurrently), every leg of `Ziel` holds (`gabbro_ziel`);
    6. EVERY RUN OF THE BINARY: under `hA1`, from related starts, when the
       Gabbro call at the depth `tief f` ends in no model error, every run of
       the binary ends related to it. -/
theorem schlusssatz {src : String} (K : Kette src)
    (O : Orakel (declOf K.u)) (hH : HardwareAnnahmen O K.E.Q)
    (orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional)
    (bin : (declOf K.u).Fn → CSt → List CVal → CSt → Option CVal → Prop)
    (tief : (declOf K.u).Fn → Nat)
    (hA1 : ∀ f st vs st' rv, bin f st vs st' rv →
      CallAt K.EL.lay orc XR (kProg K.zert) (tief f) (fnNr f) st vs st' rv)
    (sp : Speicher (declOf K.u).mitRuhe)
    (init : Faden → Σ f : (declOf K.u).mitRuhe.Fn,
      Env (declOf K.u).mitRuhe ((declOf K.u).mitRuhe.params f))
    (hA4 : EinFadenStart K.E sp init) :
    -- 1. parse fidelity
    uebersetzeAllg src = .ok ⟨K.u, K.E.P, K.fs0⟩ ∧
    -- 2. the certificates
    (akzeptiert_pruefer.akzeptiert K.E K.fs.1 K.ls.1 K.cs.1 = true ∧
      AkzeptiertSpec K.E.P K.E.S K.fs.1 K.E.ws ∧
      korrOk K.EL fnNr K.zert K.E.P K.fs.1 = true) ∧
    -- 3. the model judgement
    NutzerPflicht K.E ∧
    -- 4. every C run
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (k : KFun (declOf K.u)), K.zert[fnNr f]? = some k →
      ∀ (σ : World (declOf K.u)) (st : CSt) (ρG : Env (declOf K.u) ((declOf K.u).params f))
        (vs : List CVal) (ρ0 : CLok), corrW K.EL σ st → bindParams k.params vs = some ρ0 →
        EnvRel K.EL k.lay ρG ρ0 → (rufAt K.E.P O passes n f σ ρG).istFehler = false →
        (∃ st' rv, CallAt K.EL.lay orc XR (kProg K.zert) n (fnNr f) st vs st' rv) ∧
        ∀ st' rv, CallAt K.EL.lay orc XR (kProg K.zert) n (fnNr f) st vs st' rv →
          RufOut K.EL (rufAt K.E.P O passes n f σ ρG) st' rv) ∧
    -- 4b. NO HARDWARE ERROR: the condition of parts 4 and 6 can never fail
    --     for a machine reason -- a certified program carries no oracle form
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
        (ρG : Env (declOf K.u) ((declOf K.u).params f)) (e : Hardware (declOf K.u)),
      rufAt K.E.P O passes n f σ ρG ≠ .hardware e) ∧
    -- 4c. so what is left of that condition is the WRITER'S LOGIC, alone
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
        (ρG : Env (declOf K.u) ((declOf K.u).params f)),
      (rufAt K.E.P O passes n f σ ρG).istFehler = true →
        ∃ e : Logik (declOf K.u), rufAt K.E.P O passes n f σ ρG = .logik e) ∧
    -- 4d. and above depth `0` the condition IMPLIES the caller's duty: the
    --     entry contract of the called function at the given world and
    --     arguments (the theorem quantifies over ANY of both)
    (∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
        (ρG : Env (declOf K.u) ((declOf K.u).params f)),
      (rufAt K.E.P O passes (n + 1) f σ ρG).istFehler = false →
        ReqAmEintritt K.E.P f σ ρG) ∧
    -- 5. the machine
    ((∀ passes n : Nat, RufRu (rufAt K.E.P O passes n) (rufAt K.E.P.mitRuhe O.mitRuhe passes n)) ∧
      (∀ (passes : Nat) (M : RufMaschineG (declOf K.u).mitRuhe),
        RufErreichbarG K.E.P.mitRuhe O.mitRuhe passes (RufStartG K.E.P.mitRuhe sp init) M →
          SpurInv M ∧
          ((VertragAmOrtG K.E.P.mitRuhe M ∧ SperrInvG K.E.S.mitRuhe M ∧
            KeinLogikHaltG O.mitRuhe passes M ∧
            ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
              AnPruefungG M t → ∃ M', RufSchrittG K.E.P.mitRuhe O.mitRuhe passes M t M') ∧
            InvAmOrtG K.E.P.mitRuhe M) ∧ StartEndeG K.E.P.mitRuhe M ∧ KeinStartGrundG M) ∧
      (∀ (passes : Nat) (sp' : Speicher (declOf K.u).mitRuhe)
        (init' : Faden → Σ f : (declOf K.u).mitRuhe.Fn,
          Env (declOf K.u).mitRuhe ((declOf K.u).mitRuhe.params f)),
        Laufzeit K.E sp' init' → ∀ M : RufMaschineG (declOf K.u).mitRuhe,
          RufErreichbarG K.E.P.mitRuhe O.mitRuhe passes (RufStartG K.E.P.mitRuhe sp' init') M →
            Ziel K.E.P.mitRuhe K.E.S.mitRuhe O.mitRuhe passes
              (RufStartG K.E.P.mitRuhe sp' init') M)) ∧
    -- 6. every run of the binary
    (∀ (passes : Nat) (f : (declOf K.u).Fn) (k : KFun (declOf K.u)), K.zert[fnNr f]? = some k →
      ∀ (σ : World (declOf K.u)) (st : CSt) (ρG : Env (declOf K.u) ((declOf K.u).params f))
        (vs : List CVal) (ρ0 : CLok), corrW K.EL σ st → bindParams k.params vs = some ρ0 →
        EnvRel K.EL k.lay ρG ρ0 → (rufAt K.E.P O passes (tief f) f σ ρG).istFehler = false →
        ∀ st' rv, bin f st vs st' rv → RufOut K.EL (rufAt K.E.P O passes (tief f) f σ ρG) st' rv) := by
  have hA : AkzeptiertSpec K.E.P K.E.S K.fs.1 K.E.ws :=
    akzeptiert_pruefer.korrekt K.E K.fs K.ls K.cs K.akzeptiert
  have hlauf := fun passes n f k hk σ st ρG vs ρ0 hw hb hr hnf =>
    korrOk_jeder_lauf K.fs.2 K.zertOk orc XR hXR O passes n f k hk σ st ρG vs ρ0 hw hb hr hnf
  have hhw : ∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
      (ρG : Env (declOf K.u) ((declOf K.u).params f)) (e : Hardware (declOf K.u)),
      rufAt K.E.P O passes n f σ ρG ≠ .hardware e :=
    fun passes n => korrOk_rufAt_ohneHardware K.EL fnNr K.zert K.fs.2 K.zertOk O passes n
  have hlog : ∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
      (ρG : Env (declOf K.u) ((declOf K.u).params f)),
      (rufAt K.E.P O passes n f σ ρG).istFehler = true →
        ∃ e : Logik (declOf K.u), rufAt K.E.P O passes n f σ ρG = .logik e := by
    intro passes n f σ ρG hf
    cases hr : rufAt K.E.P O passes n f σ ρG with
    | ok σ' v => rw [hr] at hf; exact absurd hf (by simp [RufAusgang.istFehler])
    | grund σ' r => rw [hr] at hf; exact absurd hf (by simp [RufAusgang.istFehler])
    | logik e => exact ⟨e, rfl⟩
    | hardware e => exact absurd hr (hhw passes n f σ ρG e)
  have hreq : ∀ (passes n : Nat) (f : (declOf K.u).Fn) (σ : World (declOf K.u))
      (ρG : Env (declOf K.u) ((declOf K.u).params f)),
      (rufAt K.E.P O passes (n + 1) f σ ρG).istFehler = false →
        ReqAmEintritt K.E.P f σ ρG := by
    intro passes n f σ ρG hf
    rcases Classical.em (ReqAmEintritt K.E.P f σ ρG) with hq | hq
    · exact hq
    · rw [rufAt_vorbedingung K.E.P O passes n f σ ρG hq] at hf
      exact absurd hf (by simp [RufAusgang.istFehler])
  refine ⟨K.uebersetzt, ⟨K.akzeptiert, hA, K.zertOk⟩, K.nutzer, hlauf, hhw, hlog, hreq,
    ⟨fun passes => rufAt_mitRuhe K.E.P O passes,
      einfaden_ziel K.E K.fs hA K.nutzer O hH sp init hA4,
      fun passes sp' init' hL M hr => gabbro_ziel akzeptiert_pruefer (declOf K.u) K.E K.fs K.ls K.cs
        K.akzeptiert K.nutzer O hH passes sp' init' hL M hr⟩, ?_⟩
  intro passes f k hk σ st ρG vs ρ0 hw hb hr hnf st' rv hbin
  exact (hlauf passes (tief f) f k hk σ st ρG vs ρ0 hw hb hr hnf).2 st' rv (hA1 f st vs st' rv hbin)

/-
CUTS -- what the closing theorem does NOT say, by name (plan §6 keeps the
list for the whole chain):
- It speaks about the programs the Lean pipeline admits: sieve (a) is
  `uebersetzeAllg` (the lane-160 parser and elaborator, the lane-162
  generic lowering: slot writes through a pointer or at a table, direct
  calls, a trailing return of a literal, a parameter or a slot read). On
  2026-09-15 that is `beispiele/104` and `beispiele/108` of the corpus.
- `Kette.E`'s fields other than the code are the chain's data, not the
  exporter's: `S`, `Q`, `starts`, `sp0` are read next to the source.
- Part 4 relates C runs to `rufAt` (the sequential semantics) and is
  conditional on the Gabbro call ending in no model error. The HARDWARE half
  of that condition is discharged (4b); the WRITER'S LOGIC half is not, and
  the reason is nameable: the user's obligation `KoerperGutS`
  (Zielsatz/Spec.lean (b)) is quantified over handlers in the classes
  `RespektiertRahmen ∧ OhneVorbedingung` and `RespektiertRahmen ∧ OhneLogik`,
  and `rufAt` -- the very handler part 4 speaks about -- is in NEITHER: it
  answers `logik (vorbedingung g)` at every key whose `requires` fails,
  `logik (abstieg g)` at depth `0`, and its frame theorem `rufAt_gut`
  (Satz.lean) is CONDITIONAL on `HeldB` of the entry world where
  `RespektiertRahmen` promises the frame at EVERY world. Applying the
  obligation to `rufAt` needs a congruence lemma over `execEnd` in its
  handler (two handlers that differ only where both answer an error give
  outcomes that differ only where both are errors), which the tree does not
  have. Booked in `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5.
- Part 5 states the machine. That the one active thread of G agrees with
  `rufAt` is the adequacy chain (`rufG_adaequat_ruf`), not re-instantiated
  here -- the same cut as `schlusssatz_104`'s. Of the four things in the way,
  the covered FRAGMENT is not one (`korrOk_endR`, KorrOkAdaequat.lean: every
  certified body is in `EndR`); the other three are that the chain realises
  `rufRumpf` and not `rufAt` (contracts checked, and their carriers READ, so
  the two differ on the TRACE), that `Tief` carries the same depth residue,
  and that the adequacy is existential over machines of a given frame shape.
- A2 (the emitted TEXT means `kProg K.zert`) and the parts of A1/A3/A4 that
  are no Lean proposition stay outside, exactly as for `schlusssatz_104`.
- Stage (b), concurrency on the C side, is not addressed: the concurrent
  conclusion of part 5 is the MODEL's (`gabbro_ziel`), not the C's.
-/

#print axioms Gabbro.Grammatik.einfaden_ziel
#print axioms Gabbro.Grammatik.schlusssatz

end Gabbro.Grammatik
