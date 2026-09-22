/-
  File:      Grammatik/Pflicht108.lean
  Subject:   THE USER'S HALF for `beispiele/108-disjoint-start-locks.gab`,
             over the EXPORTED UNIT -- the CONCURRENT instance.

  `GenOblig108.lean` is what `gabbro obligations --g` states over the
  program: the unit `gE : Zielsatz.Einheit gD` with its TWO DECLARED STARTS
  (`concurrent { read_a, read_c }`, each parameterless), the stated duty
  `nutzerPflicht := Zielsatz.NutzerPflicht gE`, and the closing theorem
  `gP_gabbro`.

  This file is the person's half: `p108_nutzer : Zielsatz.NutzerPflicht gE`,
  COMPLETE -- every conjunct of `LogikPflicht` at EVERY budget and both
  conjuncts of `StartPflicht`, nothing assumed. `p108_ziel` closes the chain
  with only the two NAMED assumptions beside it: `HardwareAnnahmen`
  (discharged here -- `gD` has no axiom, register or global) and A4
  (`Zielsatz.Laufzeit`, discharged by `laufzeit_initRuhe` for the runtime's
  own start).

  WHY 108 AND NOT 104: here the start obligation `StartPflicht.req` is NOT
  vacuous (two declared starts, each with its declared arguments), and the
  machine `p108_ziel` speaks about really runs two threads
  (`p108_starts_laufen`). `beispiele/124` was the other candidate and does
  not export at all (`LG004`, a floored caller into a floorless callee), so
  108 is the concurrent demonstration.

  WHAT `Ziel` CARRIES HERE THAT 104 CANNOT SHOW: race freedom
  (`rennfrei`), no deadlock, `KeinWarteZyklus` -- all over a machine with
  two threads that both read the one table. Neither start holds a lock by
  signature (no lock exists in this declaration); the checker's `renn` leg
  is what admits the shared read.
-/
import Grammatik.GenOblig108
import Grammatik.Durchgaenge
import Grammatik.ZielOrtGanz
import Grammatik.ZielOrtRahmenBeweis
import Grammatik.ZielOrtRahmenSem
import Grammatik.SperreFuss
import Grammatik.ZielOrtInv
import Grammatik.ZielOrtInvGrund
import Grammatik.ZielOrtStart
import Grammatik.RufAdaequatG
import Grammatik.ZielOrtVollZeuge

namespace Gabbro.Grammatik

open G108_disjoint_start_locks_oblig (GTab GTFeld GFn g_read_a g_read_c gCtx_read_a gCtx_read_c
  gL_read_a gL_read_c gDarf_read_a_T gDarf_read_c_T gBody_read_a gBody_read_c gD gP gFs gLs gCs
  gS gSp0 gE gP_gabbro)

/-! ## 1. The bodies -/

theorem p108_fn_zwei (f : G108_disjoint_start_locks_oblig.gD.Fn) :
    f = g_read_a ∨ f = g_read_c := by
  cases f
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Both `requires` are `true` (neither reader constrains its caller). -/
theorem p108_req (w : G108_disjoint_start_locks_oblig.gD.Fn) :
    G108_disjoint_start_locks_oblig.gP.requires w = .wahr := by
  cases w <;> rfl

/-- Both `ensures` are `true` (neither reader promises a value relation;
    108 exists for the CONCURRENCY legs, not for the contract leg). -/
theorem p108_ens (f : G108_disjoint_start_locks_oblig.gD.Fn) :
    G108_disjoint_start_locks_oblig.gP.ensures f = .wahr := by
  cases f <;> rfl

/-- **Both bodies meet their obligation**: a single `return <slot>` -- the
    `ensures` is `true` at every return, and no run has a `logik` outcome. -/
theorem p108_koerperV (f : G108_disjoint_start_locks_oblig.gD.Fn) :
    KoerperGutV G108_disjoint_start_locks_oblig.gP 0 f := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · unfold EnsAmRueck
    rw [p108_ens f]
    rfl
  · rcases p108_fn_zwei f with e | e <;> subst e
    · have hr : G108_disjoint_start_locks_oblig.gP.rumpf g_read_a = gBody_read_a := rfl
      rw [hr] at hrun
      simp only [gBody_read_a, execEnd] at hrun
      cases hrun
    · have hr : G108_disjoint_start_locks_oblig.gP.rumpf g_read_c = gBody_read_c := rfl
      rw [hr] at hrun
      simp only [gBody_read_c, execEnd] at hrun
      cases hrun

theorem p108_voll : ∀ g : G108_disjoint_start_locks_oblig.gD.Fn,
    g ∈ G108_disjoint_start_locks_oblig.gFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem p108_logikFrei : programmLogikFrei G108_disjoint_start_locks_oblig.gP
    G108_disjoint_start_locks_oblig.gFs = true := by decide

theorem p108_ohne_a : (G108_disjoint_start_locks_oblig.gP.rumpf g_read_a).ohneLocks = true := by
  decide

theorem p108_ohne_c : (G108_disjoint_start_locks_oblig.gP.rumpf g_read_c).ohneLocks = true := by
  decide

theorem p108_ohneEwig : ohneEwigB G108_disjoint_start_locks_oblig.gP
    G108_disjoint_start_locks_oblig.gFs = true := by decide

/-! ## 2. The `LogikPflicht` conjuncts, at every budget -/

/-- The `KoerperGutS` duties at budget `0`, per function. -/
theorem p108_koerper_0 : ∀ f : G108_disjoint_start_locks_oblig.gD.Fn,
    KoerperGutS G108_disjoint_start_locks_oblig.gP 0
      (axWahr G108_disjoint_start_locks_oblig.gD) G108_disjoint_start_locks_oblig.gS f := by
  intro f
  cases f
  · exact koerperGutS_ohne G108_disjoint_start_locks_oblig.gS p108_ohne_a
      ⟨koerperGutRQ_of_R _ (koerperGutR_of_V (p108_koerperV g_read_a)),
        programmLogikFrei_ok p108_voll p108_logikFrei 0 _ _⟩
  · exact koerperGutS_ohne G108_disjoint_start_locks_oblig.gS p108_ohne_c
      ⟨koerperGutRQ_of_R _ (koerperGutR_of_V (p108_koerperV g_read_c)),
        programmLogikFrei_ok p108_voll p108_logikFrei 0 _ _⟩

/-- **CONJUNCT 1, first component**: the body triple at EVERY budget. -/
theorem p108_koerper : ∀ (passes : Nat) (f : G108_disjoint_start_locks_oblig.gD.Fn),
    KoerperGutS G108_disjoint_start_locks_oblig.gP passes
      (axWahr G108_disjoint_start_locks_oblig.gD) G108_disjoint_start_locks_oblig.gS f :=
  koerperGutS_alle p108_voll p108_ohneEwig p108_koerper_0

/-- **CONJUNCT 1, second component**: no table invariant is owed
    (`gD.invs = []`). -/
theorem p108_inv : ∀ (passes : Nat) (f : G108_disjoint_start_locks_oblig.gD.Fn),
    InvGutS G108_disjoint_start_locks_oblig.gP passes
      (axWahr G108_disjoint_start_locks_oblig.gD) G108_disjoint_start_locks_oblig.gS f :=
  fun _ f => invGutS_leer rfl f

/-- **CONJUNCT 1, third component**: neither reader declares a reason, so
    there is no reason exit. -/
theorem p108_invGrund : ∀ (passes : Nat) (f : G108_disjoint_start_locks_oblig.gD.Fn),
    Zielsatz.InvGutGrund G108_disjoint_start_locks_oblig.gP passes
      (axWahr G108_disjoint_start_locks_oblig.gD) G108_disjoint_start_locks_oblig.gS f :=
  fun _ f => invGutGrund_ohneGrund (by cases f <;> rfl)

/-- **CONJUNCT 2**: the exported family is empty (this declaration has no
    lock), so its invariant reads nothing. -/
theorem p108_S_lokal : Zielsatz.SperrInvLokal G108_disjoint_start_locks_oblig.gS :=
  fun _ _ _ _ => rfl

/-- **CONJUNCT 3**: the exported axiom `ensures` (`gD` has no axiom) reads
    only the carriers the axiom declares. -/
theorem p108_ax_lokal : AxEnsLokal (axWahr G108_disjoint_start_locks_oblig.gD) := axEnsLokal_wahr

theorem p108_logik : Zielsatz.LogikPflicht G108_disjoint_start_locks_oblig.gE.P
    G108_disjoint_start_locks_oblig.gE.S G108_disjoint_start_locks_oblig.gE.Q :=
  ⟨fun passes f => ⟨p108_koerper passes f, p108_inv passes f, p108_invGrund passes f⟩,
    p108_S_lokal, p108_ax_lokal⟩

/-! ## 3. The start obligation -- NOT vacuous here -/

/-- **`StartPflicht.sperren`**: no lock exists, so every lock invariant
    holds at the declared initial memory. -/
theorem p108_start_sperren : ∀ L, G108_disjoint_start_locks_oblig.gE.S.inv L
    G108_disjoint_start_locks_oblig.gE.sp0 = true :=
  fun _ => rfl

/-- **`StartPflicht.req`**: BOTH declared starts meet their `requires` at
    the declared initial memory with their DECLARED arguments (`.nil` --
    both are parameterless). This is the conjunct 104 cannot exercise. -/
theorem p108_start_req : ∀ a ∈ G108_disjoint_start_locks_oblig.gE.starts,
    ReqAmEintritt G108_disjoint_start_locks_oblig.gE.P a.1
      (G108_disjoint_start_locks_oblig.gE.sp0.welt []) a.2 := by
  rintro ⟨w, ρ⟩ _
  cases w <;> rfl

/-- **THE USER'S DUTY ON 108, PROVED** -- exactly the `def nutzerPflicht`
    that `gabbro obligations --g beispiele/108-disjoint-start-locks.gab`
    states, with no hypothesis of any kind. -/
theorem p108_nutzer : Zielsatz.NutzerPflicht G108_disjoint_start_locks_oblig.gE where
  logik := p108_logik
  start := ⟨p108_start_sperren, p108_start_req⟩

theorem p108_nutzer_ist_stated : G108_disjoint_start_locks_oblig.nutzerPflicht := p108_nutzer

/-! ## 4. The chain, closed -/

/-- The oracle of `gD`: no axiom, register or global exists. -/
def p108_O : Orakel G108_disjoint_start_locks_oblig.gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- **THE NAMED HARDWARE ASSUMPTION, discharged on this declaration.** -/
theorem p108_hw : Zielsatz.HardwareAnnahmen p108_O G108_disjoint_start_locks_oblig.gE.Q :=
  And.intro (fun a => nomatch a)
    (And.intro (And.intro (fun r => nomatch r) (fun g => nomatch g))
      (axVertragO_wahr p108_O))

/-- **THE NAMED RUNTIME ASSUMPTION (A4), discharged for the runtime's own
    start**: the loader establishes `gE.sp0`, thread `0` runs `read_a`,
    thread `1` runs `read_c`, every other thread the idle root. -/
theorem p108_laufzeit :
    Zielsatz.Laufzeit G108_disjoint_start_locks_oblig.gE
      (speicherR G108_disjoint_start_locks_oblig.gE.sp0)
      (initRuhe G108_disjoint_start_locks_oblig.gE.starts) :=
  laufzeit_initRuhe G108_disjoint_start_locks_oblig.gE

/-- **THE CHAIN, CLOSED ON 108, CONCURRENTLY**: with the duty proved above,
    the goal holds at every reachable machine of the two-threaded run the
    runtime starts -- with NO open hypothesis beyond the two named ones,
    both discharged here. -/
theorem p108_ziel (passes : Nat)
    (M : RufMaschineG G108_disjoint_start_locks_oblig.gD.mitRuhe)
    (hr : RufErreichbarG G108_disjoint_start_locks_oblig.gE.P.mitRuhe p108_O.mitRuhe passes
      (RufStartG G108_disjoint_start_locks_oblig.gE.P.mitRuhe
        (speicherR G108_disjoint_start_locks_oblig.gE.sp0)
        (initRuhe G108_disjoint_start_locks_oblig.gE.starts)) M) :
    Zielsatz.Ziel G108_disjoint_start_locks_oblig.gE.P.mitRuhe
      G108_disjoint_start_locks_oblig.gE.S.mitRuhe p108_O.mitRuhe passes
      (RufStartG G108_disjoint_start_locks_oblig.gE.P.mitRuhe
        (speicherR G108_disjoint_start_locks_oblig.gE.sp0)
        (initRuhe G108_disjoint_start_locks_oblig.gE.starts)) M :=
  gP_gabbro p108_nutzer p108_O p108_hw passes _ _ p108_laufzeit M hr

/-! ## 5. Witnesses (rule 13): the run is really concurrent -/

/-- **THE MACHINE IS NOT IDLE**: in the start configuration `p108_ziel`
    speaks about, thread `0` runs `read_a` and thread `1` runs `read_c` --
    two different threads in two different functions. Without this the
    theorem above would be a theorem about an idle machine (which is
    exactly what 104 is, and why 108 exists beside it). -/
theorem p108_starts_laufen :
    (initRuhe G108_disjoint_start_locks_oblig.gE.starts 0).1 = some g_read_a ∧
    (initRuhe G108_disjoint_start_locks_oblig.gE.starts 1).1 = some g_read_c :=
  ⟨rfl, rfl⟩

/-- **THE TWO STARTS ARE TWO**: `read_a` and `read_c` are different
    functions, so the start list is not one function counted twice. -/
theorem p108_starts_zwei : G108_disjoint_start_locks_oblig.gE.ws = [g_read_a, g_read_c] ∧
    g_read_a ≠ g_read_c :=
  ⟨rfl, by decide⟩

/-- **THE BODIES READ DIFFERENT SLOTS**: `read_a` answers slot `0`,
    `read_c` answers slot `1` -- both from the declared initial memory,
    both `ok`. The shared table is really shared, and really read. -/
theorem p108_ruf_liest :
    (∃ σ', rufAt G108_disjoint_start_locks_oblig.gE.P p108_O 0 1 g_read_a
        (G108_disjoint_start_locks_oblig.gE.sp0.welt []) .nil
      = .ok σ' ((G108_disjoint_start_locks_oblig.gE.sp0.welt []).slots GTab.T 0 GTFeld.v)) ∧
    (∃ σ', rufAt G108_disjoint_start_locks_oblig.gE.P p108_O 0 1 g_read_c
        (G108_disjoint_start_locks_oblig.gE.sp0.welt []) .nil
      = .ok σ' ((G108_disjoint_start_locks_oblig.gE.sp0.welt []).slots GTab.T 1 GTFeld.v)) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

#print axioms Gabbro.Grammatik.p108_logik
#print axioms Gabbro.Grammatik.p108_nutzer
#print axioms Gabbro.Grammatik.p108_ziel
#print axioms Gabbro.Grammatik.p108_starts_laufen
#print axioms Gabbro.Grammatik.p108_ruf_liest

end Gabbro.Grammatik
