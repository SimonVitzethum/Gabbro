/- Part 3 of 9 of `Maschine` (split by instrumente/teile/lean-teilen.py; the umbrella `Maschine.lean` imports all parts). -/
import Grammatik.Kern.Semantik.Maschine.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

/-- A `gibt` step preserves the invariant. -/
theorem genInv_gibt (_P : Programm D) (_O : Orakel D) (_passes : Nat)
    (M : GenMaschine D) (f : Faden) (L : D.Lock)
    (_hhaelt : L ∈ offen (M.spuren f))
    (hM : GenInv M) :
    GenInv ⟨M.speicher,
      genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f),
      M.lauf ++ genEigen f [Ereignis.gibt L],
      M.start,
      M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)],
      M.tiefe + 1⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f'
    by_cases hf : f' = f
    · subst f'
      show Konsistent (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f)
      rw [genUpdate_self]
      exact konsistent_cons trivial (hM.konsistent f)
    · show Konsistent (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f')
      rw [genUpdate_noteq _ _ _ hf]
      exact hM.konsistent f'
  · intro f' e he
    by_cases hf : f' = f
    · subst f'
      change e ∈ genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f at he
      rw [genUpdate_self, List.mem_cons] at he
      rcases he with rfl | he
      · trivial
      · exact hM.spur_gut f e he
    · change e ∈ genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f' at he
      rw [genUpdate_noteq _ _ _ hf] at he
      exact hM.spur_gut f' e he
  · intro W hW e he
    have hW' : W ∈ M.welten ∨ W = M.speicher.welt (Ereignis.gibt L :: M.spuren f) := by
      change W ∈ M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)] at hW
      rwa [List.mem_append, List.mem_singleton] at hW
    rcases hW' with hW' | hW'
    · exact hM.welt_gut W hW' e he
    · subst hW'
      have he' : e ∈ Ereignis.gibt L :: M.spuren f := he
      rw [List.mem_cons] at he'
      rcases he' with rfl | he'
      · trivial
      · exact hM.spur_gut f e he'
  · show ∀ f', (M.lauf ++ genEigen f [Ereignis.gibt L]).spur f' (M.lauf ++ genEigen f [Ereignis.gibt L]).length =
      genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f'
    exact genProj_blatt M.lauf M.spuren f [Ereignis.gibt L] (Ereignis.gibt L :: M.spuren f) hM.proj rfl
  · refine ⟨f, ?_⟩
    show (M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)]).getLast? =
      some (M.speicher.welt (genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f) f))
    rw [gen_getLast_append_singleton, genUpdate_self]
  · show ForeignExclusion (M.lauf ++ genEigen f [Ereignis.gibt L])
    exact genAuss_gibt M.lauf f L hM.auss
  · show (M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)]).length = (M.tiefe + 1) + 1
    simp only [List.length_append, hM.tiefe_len, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.add_left_cancel_iff]

/-- Every step preserves the invariant. -/
theorem genSchritt_inv (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M M' : GenMaschine D) (f : Faden)
    (hM : GenInv M) (hs : GenSchritt P O passes M f M') : GenInv M' := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn⟩ |
    ⟨L, hself, hrang, hfrei⟩ | ⟨L, hhaelt⟩
  · exact genInv_blatt P O passes hO M f V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn hM
  · exact genInv_nimmt P O passes M f L hself hrang hfrei hM
  · exact genInv_gibt P O passes M f L hhaelt hM

/-- Every generated machine maintains the invariant. -/
theorem genErreichbar_inv (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M0 M : GenMaschine D)
    (h0 : GenInv M0) (h : GenErreichbar P O passes M0 M) : GenInv M := by
  induction h with
  | start => exact h0
  | schritt M M' f _ hs ih => exact genSchritt_inv P O passes hO M M' f ih hs

/-! ## 11. What generated runs yield: W1/W2, the scheduler rule, worlds, order

   Every run generated from a start machine is consistent (W1) with good
   observations (W2) and obeys the scheduler rule (W3, `gen_ausschluss`): the
   lock is taken only while nobody else holds it, by construction of the
   `nimmt` step. W4 comes from the explicit `Einfaedig` projection
   (`gen_w1w2w4`, same triple shape as `w1w2w4_aus_maschine`); with the
   declaration side it closes to `Gesittet` (`gen_gesittet`) and to the serial
   order (`gen_reduktion`), through the read-only bridge and reduction. The
   world history carries live memory (`genWelten_*`, same shapes as the
   `maschinenWelten_*` family); a fireable write moves it
   (`gen_welt_speicher_bewegt`). -/

/-- W1 for generated runs: every projection of the run is consistent. -/
theorem gen_konsistent (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) (f : Faden) (j : Nat) :
    Konsistent (M.lauf.spur f j) := by
  have hM := genErreichbar_inv P O passes hO _ M (genStart_inv sp) h
  have hk : Konsistent (M.lauf.spur f M.lauf.length) := by
    rw [hM.proj]
    exact hM.konsistent f
  by_cases hj : M.lauf.length ≤ j
  · rw [gen_spur_ueber _ _ _ hj]
    exact hk
  · have hj' : j ≤ M.lauf.length := by omega
    obtain ⟨pre, hpre⟩ := gen_spur_suffix M.lauf f j M.lauf.length hj'
    rw [hpre] at hk
    exact gen_konsistent_suffix pre _ hk

/-- W2 for generated runs: every observed event is good. -/
theorem gen_gut_obs (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) (f : Faden) (j : Nat)
    (e : Ereignis D) (he : e ∈ M.lauf.spur f j) : e.gut := by
  have hM := genErreichbar_inv P O passes hO _ M (genStart_inv sp) h
  have hg : ∀ e ∈ M.lauf.spur f M.lauf.length, e.gut := by
    rw [hM.proj]
    exact hM.spur_gut f
  by_cases hj : M.lauf.length ≤ j
  · rw [gen_spur_ueber _ _ _ hj] at he
    exact hg e he
  · have hj' : j ≤ M.lauf.length := by omega
    obtain ⟨pre, hpre⟩ := gen_spur_suffix M.lauf f j M.lauf.length hj'
    exact hg e (by rw [hpre]; exact List.mem_append_right _ he)

/-- W3 for generated runs: the scheduler rule holds over the whole run. -/
theorem gen_ausschluss (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    ForeignExclusion M.lauf :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).auss

/-- **W1, W2, W4 for generated runs.** W1+W2 are generated (grammar side,
    through `execStmt`); W4 comes from the explicit `Einfaedig` projection --
    thread programs are over-approximated (any leaf any time, no counters),
    so ownership is still a construction premise, exactly as the bridge books
    it. Same triple shape as `w1w2w4_aus_maschine`. -/
theorem gen_w1w2w4 (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf)) :
    (∀ f j, Konsistent (M.lauf.spur f j)) ∧
    (∀ f j (e : Ereignis D), e ∈ M.lauf.spur f j → e.gut) ∧
    (∀ (i j : Nat) (f g : Faden) (m : D.Marke) (s s' : Nat) (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      Res.marke m s ∈ ei.lambda → Res.marke m s' ∈ ej.lambda → f = g) :=
  ⟨gen_konsistent P O passes hO sp M h, gen_gut_obs P O passes hO sp M h,
   marke_eindeutig_aus_einfaedig code M.lauf hEin⟩

/-- **A generated run is `Gesittet`.** W1-W3 are generated; W4 travels as the
    `Einfaedig` projection, W5 as the declaration side -- both explicit
    premises, exactly as the bridge books the construction and the declaration
    side. -/
theorem gen_gesittet (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
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
  gesittet_aus_einfaedig M.lauf (gen_konsistent P O passes hO sp M h)
    (gen_gut_obs P O passes hO sp M h) (gen_ausschluss P O passes hO sp M h)
    code hEin hungeteilt

/-- **Reduction, serial order, from a generated run (two-access single-carrier
    fragment).** Same interface as `reduktion_maschine`: two conflicting
    accesses in a generated run are happens-before ordered, in one direction
    or the other. Closes via `reduktion_seriell` with machine-derived
    `Gesittet`; the narrowing (single shared table carrier, two accesses at
    order level) is carried unchanged. -/
theorem gen_reduktion (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (code : D.Marke → Nat) (hEin : Marken.Einfaedig (laufProj code M.lauf))
    (hungeteilt : ∀ (i j : Nat) (f g : Faden) (o : D.Tab ⊕ D.Glob)
      (ei ej : Ereignis D),
      M.lauf[i]? = some (Schritt.mk f ei) → M.lauf[j]? = some (Schritt.mk g ej) →
      ei.traeger = some o → ej.traeger = some o →
      (match o with
        | .inl t => D.geteilt t = false
        | .inr x => D.ggeteilt x = false) → f = g)
    (t₀ : D.Tab) (g₁ g₂ : Faden) (hne : g₁ ≠ g₂)
    (j₁ j₂ : Nat) (w₁ w₂ : Bool) (Λ₁ Λ₂ : List (Res D)) (h₁ h₂ : List D.Lock)
    (hw₁ : M.lauf[j₁]? = some (Schritt.mk g₁ (.zugriff t₀ w₁ Λ₁ h₁)))
    (hw₂ : M.lauf[j₂]? = some (Schritt.mk g₂ (.zugriff t₀ w₂ Λ₂ h₂))) :
    HB M.lauf j₁ j₂ ∨ HB M.lauf j₂ j₁ :=
  reduktion_seriell M.lauf
    (gen_gesittet P O passes hO sp M h code hEin hungeteilt)
    t₀ g₁ g₂ hne j₁ j₂ w₁ w₂ Λ₁ Λ₂ h₁ h₂ hw₁ hw₂

/-- One world per step, plus the start world: the history counts steps. -/
theorem genWelten_laenge (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    M.welten.length = M.tiefe + 1 :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).tiefe_len

/-- The observations of every generated run are good. -/
theorem genWelten_gut (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    ∀ W ∈ M.welten, ∀ e ∈ W.spur, e.gut :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).welt_gut

/-- The last recorded world is a thread world with live memory. -/
theorem genWelten_letzte (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M) :
    ∃ f, M.welten.getLast? = some (M.speicher.welt (M.spuren f)) :=
  (genErreichbar_inv P O passes hO _ M (genStart_inv sp) h).letzte

/-- **Generated worlds move memory.** A fireable write reaches, in one step, a
    machine whose memory differs -- the auditor's constant-memory shape
    (`maschinenWelten_speicher_gleich`) does not characterize generated runs. -/
theorem gen_welt_speicher_bewegt (P : Programm D) (O : Orakel D) (passes : Nat)
    (sp : Speicher D) (f : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D))
    (g : D.Glob) (e : Expr D Γ Λ (D.gtyp g)) (ρ : Env D Γ)
    (hw : V.gschreibt g = true) (hL : gdarf D g Λ)
    (hΛ : HeldGenau Λ (offen ((GenStart sp).spuren f)))
    (hv : eval (((GenStart sp).weltVon f).lese Λ e.orte) e
      (((GenStart sp).weltVon f).lese Λ e.orte) ρ ≠
      (((GenStart sp).weltVon f).lese Λ e.orte).globs g) :
    ∃ M', GenErreichbar P O passes (GenStart sp) M' ∧
      M'.speicher.globs g ≠ sp.globs g := by
  obtain ⟨M', hs, hdiff⟩ :=
    gen_write_glob_moves P O passes (GenStart sp) f V l Γ Λ g e ρ hw hL hΛ hv
  exact ⟨M', GenErreichbar.schritt _ _ f GenErreichbar.start hs, hdiff⟩

#print axioms Gabbro.Grammatik.keinRuf_gut
#print axioms Gabbro.Grammatik.Speicher.welt_speicher
#print axioms Gabbro.Grammatik.weltenFalte_speicher_gleich
#print axioms Gabbro.Grammatik.maschinenWelten_speicher_gleich
#print axioms Gabbro.Grammatik.storeSlot_hit
#print axioms Gabbro.Grammatik.storeGlob_hit
#print axioms Gabbro.Grammatik.schreibt_wirkt_slot
#print axioms Gabbro.Grammatik.schreibt_wirkt_slot_ne
#print axioms Gabbro.Grammatik.schreibt_wirkt_glob
#print axioms Gabbro.Grammatik.schreibt_wirkt_glob_ne
#print axioms Gabbro.Grammatik.gen_write_glob_moves
#print axioms Gabbro.Grammatik.gen_konsistent
#print axioms Gabbro.Grammatik.gen_gut_obs
#print axioms Gabbro.Grammatik.gen_ausschluss
#print axioms Gabbro.Grammatik.gen_w1w2w4
#print axioms Gabbro.Grammatik.gen_gesittet
#print axioms Gabbro.Grammatik.gen_reduktion
#print axioms Gabbro.Grammatik.genWelten_laenge
#print axioms Gabbro.Grammatik.genWelten_gut
#print axioms Gabbro.Grammatik.genWelten_letzte
#print axioms Gabbro.Grammatik.gen_welt_speicher_bewegt

/-! ## 12. Program counters -- every thread carries its position

   Section 11 books the remainder honestly: thread programs are over-approximated
   (any leaf any time), so W4 needs the `Einfaedig` projection as premise and W5
   the declaration side. This section removes the over-approximation at the
   position level.

   A thread program (`PCProg`) is the schedule of one thread: one atom per step.
   A `leaf` atom carries the static footprint of the leaf `Stmt` it points at --
   its `Λ` (every `zugriff`/`gzugriff` event of a leaf step names exactly that
   `Λ`: `World.lese`, `World.schreibSlot`, `World.schreibGlob`) and the carrier
   set the step may touch -- reusing the `Stmt`/`Block` body shapes at leaf
   grain. A `take`/`rel` atom is one side of a `locks L` section. Sections are
   take-to-release intervals, the grain of `InterferenzAllgemein.lean` §21
   (`AbschnittGedeckt`): at event grain the invariant breaks mid-step, at section
   grain each step re-establishes what it owes.

   Every thread carries its position (`PCStand`, one counter per thread). A
   `PCSchritt` fires only the pointed-to atom -- the leaf step runs the
   pointed-to footprint (`hΛa` ties the atom to the fired statement), the lock
   steps the pointed-to lock -- and advances only the acting thread
   (`pcAdvance`); every other thread resumes at its stored counter. That advance
   IS the continuation: resumption is explicit, and no step moves another
   thread's position (`pcSchritt_eigen`, `pcSchritt_fremd`).

   From positions follow the footprints: `PCMarkInv` (every mark named by a run
   event sits in its thread's program text) and `PCCarrierInv` (every accessed
   carrier is reachable from its thread's program text), both preserved by every
   step. With program-text separation -- disjoint mark codes (`PCMarkSep`), no
   unshared carrier reached from two threads (`PCUnsharedSep`) -- the projection
   premise discharges (`pc_discharge_einfaedig`, the discharge fragment) and the
   declaration side discharges (`pc_discharge_unshared`); `pc_gesittet` closes
   with neither premise, and `pc_reduktion` runs the serial order on it. The
   generated race-freedom results keep building untouched: `gen_konsistent`,
   `gen_gut_obs`, `gen_ausschluss` are consumed through the projection
   (`pcReach_gen`), never re-proved; the `pc_*` triple restates them on PC runs
   honestly in-file.

   Remainder (booked, not hidden): full `Block` continuations -- `ite` arms, call
   stacks, loop resumption as explicit continuation objects -- are not threaded
   here; the schedule flattens each body to its atom sequence. What W4/W5 need is
   positions with footprints, and that is what this section carries. The full
   run-to-`Bau` wiring (`Geteilt.lean`: unshared means reachable from at most one
   thread) still travels as the carrier-separation shape, not as a `Bau` term. -/

/-- One position in a thread program: the footprint of the statement fired here.
    `leaf` carries the static `Λ` of the pointed-to leaf `Stmt` plus the carrier
    set that step may touch; `take`/`rel` carry the lock of the pointed-to
    `locks L` side. Lock steps name no marks (`Ereignis.lambda` is `[]` there)
    and touch no carrier (`Ereignis.traeger` is `none` there). -/
inductive PCAtom (D : Deklaration) where
  | leaf (Λ : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
  | take (L : D.Lock)
  | rel (L : D.Lock)

/-- The marks named in one atom's static footprint. -/
def PCAtom.marks : PCAtom D → List D.Marke
  | .leaf Λ _ => Λ.filterMap fun r => match r with
    | .marke m _ => some m
    | _ => none
  | _ => []

/-- The carriers one atom may touch. -/
def PCAtom.carriers : PCAtom D → List (D.Tab ⊕ D.Glob)
  | .leaf _ cs => cs
  | _ => []

/-- A thread program: the schedule of one thread, one atom per step. -/
def PCProg (D : Deklaration) := Faden → List (PCAtom D)

/-- Thread positions: every thread carries its position in its program. -/
def PCStand := Faden → Nat

/-- Advance one thread, keep every other: the continuation, explicit. -/
def pcAdvance (pc : PCStand) (f : Faden) : PCStand :=
  fun g => if g = f then pc f + 1 else pc g

theorem pcAdvance_self (pc : PCStand) (f : Faden) :
    pcAdvance pc f f = pc f + 1 := by
  simp only [pcAdvance, ↓reduceIte, Nat.add_left_cancel_iff]

theorem pcAdvance_noteq (pc : PCStand) (f g : Faden) (h : g ≠ f) :
    pcAdvance pc f g = pc g := by
  simp only [pcAdvance, h, ↓reduceIte]

/-- The marks named anywhere in one thread's program text. -/
def PCProg.marks (prog : PCProg D) (f : Faden) : List D.Marke :=
  (prog f).flatMap PCAtom.marks

/-- Mark separation, over codes: no code named by one thread's text is named by
    another's. Program text, not run projection: this replaces `hEin`. -/
def PCMarkSep (code : D.Marke → Nat) (prog : PCProg D) : Prop :=
  ∀ f g, f ≠ g → ∀ c, c ∈ (prog.marks f).map code → c ∉ (prog.marks g).map code

/-- The carriers reached anywhere in one thread's program text. -/
def PCProg.carriers (prog : PCProg D) (f : Faden) : List (D.Tab ⊕ D.Glob) :=
  (prog f).flatMap PCAtom.carriers

/-- Carrier separation for unshared carriers: a carrier reached from two threads
    is shared. Program text, not declaration side: this replaces `hungeteilt`. -/
def PCUnsharedSep (prog : PCProg D) : Prop :=
  ∀ f g, f ≠ g → ∀ o, o ∈ prog.carriers f → o ∈ prog.carriers g →
    ¬ (match o with
      | .inl t => D.geteilt t = false
      | .inr x => D.ggeteilt x = false)

/-- **One PC step.** The same machine step as `GenSchritt`, firing only the
    pointed-to atom: the leaf step runs the pointed-to footprint (`hΛa` ties the
    atom to the fired statement), the lock steps the pointed-to lock. The
    footprint checks (`hmark`, `hcar`) verify the atom against the step's own
    events; the counter advances only the acting thread (`pcAdvance`). -/
inductive PCSchritt (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) : GenMaschine D → PCStand → Faden → GenMaschine D → PCStand → Prop where
  | leaf (M : GenMaschine D) (pc : PCStand) (f : Faden)
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hΛ : HeldGenau Λ (offen (M.spuren f)))
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
      (hneu : σ'.spur = neu ++ M.spuren f)
      (hkein_nimmt : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog f)[pc f]? = some (PCAtom.leaf Λa cs))
      (hΛa : Λa = Λ)
      (hmark : ∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat),
        Res.marke m st ∈ e.lambda → m ∈ PCAtom.marks (PCAtom.leaf Λa cs))
      (hcar : ∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf Λa cs)) :
      PCSchritt P O passes prog M pc f
        ⟨σ'.speicher, genUpdate M.spuren f σ'.spur,
         M.lauf ++ genEigen f neu, M.start, M.welten ++ [σ'], M.tiefe + 1⟩
        (pcAdvance pc f)
  | take (M : GenMaschine D) (pc : PCStand) (f : Faden) (L : D.Lock)
      (hself : L ∉ offen (M.spuren f))
      (hrang : ∀ K ∈ offen (M.spuren f), D.rang K < D.rang L)
      (hfrei : GenFrei M f L)
      (hpc : (prog f)[pc f]? = some (PCAtom.take L)) :
      PCSchritt P O passes prog M pc f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.nimmt L (offen (M.spuren f))],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f)],
         M.tiefe + 1⟩
        (pcAdvance pc f)
  | rel (M : GenMaschine D) (pc : PCStand) (f : Faden) (L : D.Lock)
      (hhaelt : L ∈ offen (M.spuren f))
      (hpc : (prog f)[pc f]? = some (PCAtom.rel L)) :
      PCSchritt P O passes prog M pc f
        ⟨M.speicher,
         genUpdate M.spuren f (Ereignis.gibt L :: M.spuren f),
         M.lauf ++ genEigen f [Ereignis.gibt L],
         M.start,
         M.welten ++ [M.speicher.welt (Ereignis.gibt L :: M.spuren f)],
         M.tiefe + 1⟩
        (pcAdvance pc f)

/-- Reachable PC machines, from a start machine and zeroed counters. -/
inductive PCReach (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 : GenMaschine D) : GenMaschine D → PCStand → Prop where
  | start : PCReach P O passes prog M0 M0 (fun _ => 0)
  | step (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
      (h : PCReach P O passes prog M0 M pc) (hs : PCSchritt P O passes prog M pc f M' pc') :
      PCReach P O passes prog M0 M' pc'

/-- Every PC step is a generated step: the counter constrains, the machine moves. -/
theorem pcSchritt_gen (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') :
    GenSchritt P O passes M f M' := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, _Λa, _cs, _hpc, _hΛa, _hmark, _hcar⟩ |
    ⟨L, hself, hrang, hfrei, _hpc⟩ | ⟨L, hhaelt, _hpc⟩
  · exact GenSchritt.blatt M f V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn
  · exact GenSchritt.nimmt M f L hself hrang hfrei
  · exact GenSchritt.gibt M f L hhaelt

/-- Every PC-reachable machine is generated: positions project to runs. -/
theorem pcReach_gen (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M0 M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog M0 M pc) : GenErreichbar P O passes M0 M := by
  induction h with
  | start => exact GenErreichbar.start
  | step M M' pc pc' f _ hs ih =>
      exact GenErreichbar.schritt M M' f ih (pcSchritt_gen P O passes prog M M' pc pc' f hs)

/-- A step advances its own counter: the acting thread moves to its next atom. -/
theorem pcSchritt_eigen (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') : pc' f = pc f + 1 := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, _Λa, _cs, _hpc, _hΛa, _hmark, _hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · exact pcAdvance_self pc f
  · exact pcAdvance_self pc f
  · exact pcAdvance_self pc f

/-- A step moves no other counter: every other thread resumes where it stood. -/
theorem pcSchritt_fremd (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (M M' : GenMaschine D) (pc pc' : PCStand) (f g : Faden)
    (hs : PCSchritt P O passes prog M pc f M' pc') (hne : g ≠ f) :
    pc' g = pc g := by
  rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, _Λa, _cs, _hpc, _hΛa, _hmark, _hcar⟩ |
    ⟨L, _hself, _hrang, _hfrei, _hpc⟩ | ⟨L, _hhaelt, _hpc⟩
  · exact pcAdvance_noteq pc f g hne
  · exact pcAdvance_noteq pc f g hne
  · exact pcAdvance_noteq pc f g hne

/-- W1 on PC runs: every projection of a PC run is consistent. -/
theorem pc_konsistent (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) (f : Faden) (j : Nat) :
    Konsistent (M.lauf.spur f j) :=
  gen_konsistent P O passes hO sp M (pcReach_gen P O passes prog _ M pc h) f j

/-- W2 on PC runs: every observed event of a PC run is good. -/
theorem pc_gut_obs (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) (f : Faden) (j : Nat)
    (e : Ereignis D) (he : e ∈ M.lauf.spur f j) : e.gut :=
  gen_gut_obs P O passes hO sp M (pcReach_gen P O passes prog _ M pc h) f j e he

/-- W3 on PC runs: the scheduler rule holds over the whole PC run. -/
theorem pc_ausschluss (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes prog (GenStart sp) M pc) :
    ForeignExclusion M.lauf :=
  gen_ausschluss P O passes hO sp M (pcReach_gen P O passes prog _ M pc h)

/-- Every mark a run event names sits in its thread's program text: which mark a
    thread holds follows from where its program stands. -/
def PCMarkInv (prog : PCProg D) (M : GenMaschine D) : Prop :=
  ∀ (k : Nat) (f : Faden) (e : Ereignis D),
    M.lauf[k]? = some (Schritt.mk f e) →
    ∀ (m : D.Marke) (st : Nat), Res.marke m st ∈ e.lambda → m ∈ prog.marks f

/-- Every accessed carrier is reachable from its thread's program text:
    thread position determines carrier reachability. -/
def PCCarrierInv (prog : PCProg D) (M : GenMaschine D) : Prop :=
  ∀ (k : Nat) (f : Faden) (e : Ereignis D),
    M.lauf[k]? = some (Schritt.mk f e) →
    ∀ o, e.traeger = some o → o ∈ prog.carriers f

/-- One atom's marks sit in its thread's program text. -/
theorem pcAtom_mem_marks (prog : PCProg D) (f : Faden) (a : PCAtom D)
    (h : a ∈ prog f) (m : D.Marke) (hm : m ∈ a.marks) : m ∈ prog.marks f := by
  unfold PCProg.marks
  rw [List.mem_flatMap]
  exact ⟨a, h, hm⟩


end Gabbro.Grammatik
