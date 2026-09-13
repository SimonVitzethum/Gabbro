/-
  File:      Grammatik/TravAwaitsZeuge.lean
  Subject:   REACHED RUNS THAT FIRE `traverse` AND `awaits`, jointly with the
             premises of `ziel_ort_geraet`, and the witness of the full race
             theorem `rennfrei_g_voll` on the same run.

  The declaration `taD`: one table `tab` (2 slots, field `0 .. 1`) guarded by
  the lock `l` (rank 0); one global `flag` (`0 .. 1`, shared, payload
  empty) guarded by the lock `k` (rank 1); five functions:

  * `haupt0` (thread 0's entry; holds `l` by signature; writes `tab`, `flag`):
      `fuelle(); locks k { flag := 1 publishes {} }; return`
  * `fuelle` (holds `l`; writes `tab`;
      `ensures forall i in slots of tab : tab[i] == 1`):
      `traverse tab invariant true { tab[i] := 1 }; return`
  * `haupt1` (thread 1's entry; holds nothing): `locks k { warte() }; return`
  * `warte` (holds `k` by signature): `if true { let v = flag awaits {} }; return`
  * `ruhe` (every other thread): `return`.

  The oracle `taO` makes a publication visible exactly when `flag` is `1`
  (`sichtbar flag σ = (σ.globs flag == 1)`): register-local, memory
  dependent, and the `awaits` of thread 1 fires only after thread 0's
  publish.

  The run (`taLauf`, 29 steps, by index): thread 0 calls `fuelle`, which
  unfolds the `traverse` (`dannTrav`), runs two iterations (`travNext`,
  the slot write, `travFort`), writes `tab[0]` and `tab[1]` (memory `0 -> 1`
  twice), leaves the loop (`travDone`) and returns (the non-trivial
  `ensures` is checked at this logged return); `haupt0` takes `k`,
  publishes `flag := 1` (memory `0 -> 1`), releases `k`. Thread 1 takes `k`,
  calls `warte`, which unfolds its `if`, fires `awaits` (reading `flag`),
  and returns.
-/
import Grammatik.RennfreiVoll
import Grammatik.ZielOrtGeraetZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration and the program -/

inductive TaLock where
  | l
  | k
  deriving DecidableEq

inductive TaFn where
  | haupt0
  | fuelle
  | haupt1
  | warte
  | ruhe
  deriving DecidableEq

def taSigHaupt0 : Signatur Unit Unit TaLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [.l]
  schreibt := fun _ => true
  gschreibt := fun _ => true
  konsumiert := []
  produziert := []

def taSigFuelle : Signatur Unit Unit TaLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [.l]
  schreibt := fun _ => true
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

def taSigHaupt1 : Signatur Unit Unit TaLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

def taSigWarte : Signatur Unit Unit TaLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [.k]
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

def taSigRuhe : Signatur Unit Unit TaLock Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

/-- One guarded table, one guarded global, two ranked locks, five
    functions, no axiom, no register. -/
def taD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 1
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => true
  ggeteilt := fun _ => true
  Lock := TaLock
  decLock := inferInstance
  rang := fun | .l => 0 | .k => 1
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl .l]
  gbraucht := fun _ => [.inl .k]
  eigner := fun _ => []
  Fn := TaFn
  sig := fun | .haupt0 => 0 | .fuelle => 1 | .haupt1 => 2 | .warte => 3 | .ruhe => 4
  sigNr := fun n => match n with
    | 0 => taSigHaupt0 | 1 => taSigFuelle | 2 => taSigHaupt1 | 3 => taSigWarte | _ => taSigRuhe
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ _ => Or.inl (by decide)

def taHaupt0 : taD.Fn := TaFn.haupt0
def taFuelle : taD.Fn := TaFn.fuelle
def taHaupt1 : taD.Fn := TaFn.haupt1
def taWarte : taD.Fn := TaFn.warte
def taRuhe : taD.Fn := TaFn.ruhe

abbrev taLL : List (Res taD) := [Res.held (D := taD) TaLock.l]
abbrev taKL : List (Res taD) := [Res.held (D := taD) TaLock.k]
abbrev taKLL : List (Res taD) := [Res.held (D := taD) TaLock.k, Res.held (D := taD) TaLock.l]

theorem taDarfL : darf taD () taLL := by
  intro w h
  have e : w = Sum.inl TaLock.l := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem taGdarfKLL : gdarf taD () taKLL := by
  intro w h
  have e : w = Sum.inl TaLock.k := List.mem_singleton.mp h
  subst e
  exact List.mem_cons_self

theorem taGdarfK : gdarf taD () taKL := by
  intro w h
  have e : w = Sum.inl TaLock.k := List.mem_singleton.mp h
  subst e
  exact List.mem_cons_self

theorem taLock_ne : (TaLock.k : TaLock) ≠ TaLock.l := by decide

theorem taHeld_ne : Res.held (D := taD) TaLock.k ≠ Res.held TaLock.l :=
  fun e => taLock_ne (Res.held.inj e)

def taEins {Γ : Ctx} {Λ : List (Res taD)} : Expr taD Γ Λ (.int 0 1) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- The traverse body: `tab[i] := 1`. -/
def taSchreibI : Stmt taD (vertragVon taD taFuelle) true [.index (taD.count ())] taLL taLL :=
  .assignSlot () () (.var .hier) taEins rfl taDarfL

def taTravBody : Block taD (vertragVon taD taFuelle) true [.index (taD.count ())] taLL taLL :=
  .cons taSchreibI .nil

/-- `traverse tab invariant true { tab[i] := 1 }` -/
def taTrav : Stmt taD (vertragVon taD taFuelle) false [] taLL taLL :=
  .traverse () .wahr taTravBody

def taRetF : Endblock taD (vertragVon taD taFuelle) false [] taLL :=
  .ret .keine (List.Perm.refl _)

def taRumpfFuelle : Endblock taD (vertragVon taD taFuelle) false [] taLL :=
  .cons taTrav taRetF

/-- `fuelle` ensures every slot of `tab` is `1`. -/
def taEnsFuelle : Expr taD (ErgCtx (taD.params taFuelle) (taD.erg taFuelle))
    (vertragVon taD taFuelle).ende .bool :=
  .forallSlots () (.eq (.slot () () (.var .hier) taDarfL) (.lit 1)) taDarfL

/-- `haupt0` calls `fuelle`: same lock, the callee's writes are the caller's. -/
theorem taHpFuelle : RufPasst taD (vertragVon taD taHaupt0) (taD.signatur taFuelle) taLL where
  hw := fun _ _ => rfl
  hg := fun _ h => by cases h
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => by
    cases L
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) taHeld_ne,
        fun h => absurd (List.mem_singleton.mp h) taLock_ne⟩

def taRufFuelle : Stmt taD (vertragVon taD taHaupt0) false [] taLL (nach taD taFuelle taLL) :=
  .call taFuelle .nil taHpFuelle rfl

/-- `flag := 1 publishes {}` under `k` and `l`. -/
def taPub : Stmt taD (vertragVon taD taHaupt0) false [] taKLL taKLL :=
  .publish () taEins [] rfl rfl taGdarfKLL

theorem taRangK : ∀ M, Res.held M ∈ taLL → taD.rang M < taD.rang TaLock.k := by
  intro M h
  have e : Res.held (D := taD) M = Res.held TaLock.l := List.mem_singleton.mp h
  cases e
  decide

def taPubBody : Block taD (vertragVon taD taHaupt0) false [] taKLL taKLL := .cons taPub .nil

/-- `locks k { flag := 1 publishes {} }` -/
def taLocksK : Stmt taD (vertragVon taD taHaupt0) false [] taLL taLL :=
  .locks TaLock.k taRangK taPubBody

def taRetH0 : Endblock taD (vertragVon taD taHaupt0) false [] taLL :=
  .ret .keine (List.Perm.refl _)

def taRestH0 : Endblock taD (vertragVon taD taHaupt0) false [] taLL :=
  .cons taLocksK taRetH0

def taRumpfHaupt0 : Endblock taD (vertragVon taD taHaupt0) false [] taLL :=
  .cons taRufFuelle taRestH0

/-- `haupt1` calls `warte` inside `locks k`: the callee holds exactly `k`. -/
theorem taHpWarte : RufPasst taD (vertragVon taD taHaupt1) (taD.signatur taWarte) taKL where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => by
    cases L
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm taHeld_ne),
        fun h => absurd (List.mem_singleton.mp h) (Ne.symm taLock_ne)⟩
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

def taRufWarte : Stmt taD (vertragVon taD taHaupt1) false [] taKL (nach taD taWarte taKL) :=
  .call taWarte .nil taHpWarte rfl

def taWarteBody : Block taD (vertragVon taD taHaupt1) false [] taKL taKL := .cons taRufWarte .nil

def taLocksH : Stmt taD (vertragVon taD taHaupt1) false [] [] [] :=
  .locks TaLock.k (fun _ h => nomatch h) taWarteBody

def taRetH1 : Endblock taD (vertragVon taD taHaupt1) false [] [] := .ret .keine List.Perm.nil

def taRumpfHaupt1 : Endblock taD (vertragVon taD taHaupt1) false [] [] :=
  .cons taLocksH taRetH1

/-- `let v = flag awaits {}` -/
def taAwaitsBlock : Block taD (vertragVon taD taWarte) false [] taKL taKL :=
  .awaits () [] rfl taGdarfK .nil

def taIteW : Stmt taD (vertragVon taD taWarte) false [] taKL taKL :=
  .ite .wahr taAwaitsBlock .nil

def taRetW : Endblock taD (vertragVon taD taWarte) false [] taKL :=
  .ret .keine (List.Perm.refl _)

def taRumpfWarte : Endblock taD (vertragVon taD taWarte) false [] taKL :=
  .cons taIteW taRetW

def taRumpfRuhe : Endblock taD (vertragVon taD taRuhe) false [] [] :=
  .ret .keine List.Perm.nil

/-- The program: a non-trivial `ensures` for `fuelle`, `true` elsewhere. -/
def taP : Programm taD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .haupt0 => .wahr
    | .fuelle => taEnsFuelle
    | .haupt1 => .wahr
    | .warte => .wahr
    | .ruhe => .wahr
  rumpf
    | .haupt0 => taRumpfHaupt0
    | .fuelle => taRumpfFuelle
    | .haupt1 => taRumpfHaupt1
    | .warte => taRumpfWarte
    | .ruhe => taRumpfRuhe

def taFs : List taD.Fn := [taHaupt0, taFuelle, taHaupt1, taWarte, taRuhe]

theorem taFs_voll : ∀ g : taD.Fn, g ∈ taFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem taP_fragment : programmImFragmentG taP taFs = true := by decide

theorem taP_fuss : fussOrtGB taP taFs = true := by decide

/-! ## 2. Oracle, start, and the user obligations -/

/-- The oracle: a publication of `flag` is visible exactly when `flag` is
    `1`. No axioms, no registers. -/
def taO : Orakel taD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g σ => decide ((σ.globs g).n = 1)

theorem taO_gut : GutO taO := fun a => nomatch a

theorem taO_lokal : RegLokal taO :=
  ⟨fun r => (nomatch r), fun g σ σ' h => by
    show decide ((σ.globs g).n = 1) = decide ((σ'.globs g).n = 1)
    rw [h.2 g List.mem_cons_self]⟩

/-- ... and visibility depends on memory. -/
theorem taO_liest_speicher : ∃ σ σ' : World taD, taO.sichtbar () σ ≠ taO.sichtbar () σ' :=
  ⟨⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨0, by decide, by decide⟩, []⟩,
   ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨1, by decide, by decide⟩, []⟩, by decide⟩

def taNull : Wert taD (.int 0 1) := ⟨0, by decide, by decide⟩

def taSp : Speicher taD := ⟨fun _ _ _ => taNull, fun _ => taNull⟩

def taInit : Faden → Σ f : taD.Fn, Env taD (taD.params f) :=
  fun t => if t = 0 then ⟨taHaupt0, .nil⟩ else if t = 1 then ⟨taHaupt1, .nil⟩
    else ⟨taRuhe, .nil⟩

theorem taP_start : StartGut taP taSp taInit := by
  intro t
  unfold taInit
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem taInit_haelt (t : Faden) :
    taD.haelt (taInit t).1 = (if t = 0 then [TaLock.l] else []) := by
  unfold taInit
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : t = 1
    · rw [if_pos h1]; rfl
    · rw [if_neg h1]; rfl

theorem taInit_exklusiv : StartExklusiv (D := taD) taInit := by
  intro t u htu L ht hu
  rw [taInit_haelt] at ht hu
  by_cases h0 : t = 0
  · have hu0 : u ≠ 0 := fun e => htu (h0.trans e.symm)
    rw [if_neg hu0] at hu
    exact absurd hu List.not_mem_nil
  · rw [if_neg h0] at ht
    exact absurd ht List.not_mem_nil

/-- **What `fuelle`'s body does, for every oracle and handler**: it
    returns, and its `ensures` holds at the return (the traverse wrote every
    slot). -/
theorem taFuelle_lauf (O' : Orakel taD) (passes : Nat)
    (R : ∀ f : taD.Fn, World taD → Env taD (taD.params f) → RufAusgang f) (σ : World taD)
    (ρ : Env taD (taD.params taFuelle)) :
    ∃ σ', execEnd O' passes R (taP.rumpf taFuelle) σ ρ = .zurueck σ' () ∧
      EnsAmRueck taP taFuelle σ σ' ρ () :=
  ⟨_, rfl, rfl⟩

/-- `fuelle`'s obligation: the traverse writes every slot, so the `ensures`
    holds at every return, for EVERY frame-respecting local oracle; the body
    calls nothing, so the caller duty holds. -/
theorem taP_koerper_fuelle : KoerperGutG taP 0 taFuelle := by
  intro O' _ _ R _ _ σ ρ _
  obtain ⟨σ1, h1, hens⟩ := taFuelle_lauf O' 0 R σ ρ
  obtain ⟨σ2, h2, _⟩ := taFuelle_lauf O' 0 (torRuf taP R) σ ρ
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rw [h1] at hrun
    cases hrun
    exact hens
  · rw [h2] at hrun
    cases hrun

theorem taP_koerper_haupt0 : KoerperGutG taP 0 taHaupt0 := by
  intro O' _ _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : taP.rumpf taHaupt0 = taRumpfHaupt0 := rfl
  have ht : ∀ σ1 ρ1, torRuf taP R taFuelle σ1 ρ1 = R taFuelle σ1 ρ1 := fun _ _ => if_pos rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [taRufFuelle, execStmt, ht] at h1
    split at h1
    · cases h1
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h1
      exact hOV _ _ _ _ hR g rfl
    · cases h1
  · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
    · simp only [taLocksK, execStmt] at h2
      have h3 := execBlock_eins_logikV _ _ _ _ _ _ (mapWelt_logikV h2)
      simp only [taPub, execStmt] at h3
      cases h3
    · simp only [taRetH0, execEnd] at h2
      cases h2

theorem taP_koerper_warte : KoerperGutG taP 0 taWarte := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : taP.rumpf taWarte = taRumpfWarte := rfl
  rw [hr] at hrun
  simp only [taRumpfWarte, taIteW, taAwaitsBlock, execEnd, execStmt, execBlock, eval, wahr?,
    if_true, Expr.orte] at hrun
  by_cases hv : O'.sichtbar ()
      (σ.lese (Signatur.anfang taD (taD.signatur taWarte)) []) = true
  · simp only [hv, if_true, Ausgang.schrumpf] at hrun
    cases hrun
  · simp only [hv, Bool.false_eq_true, if_false] at hrun
    cases hrun

theorem taP_koerper_haupt1 : KoerperGutG taP 0 taHaupt1 := by
  intro O' _ _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : taP.rumpf taHaupt1 = taRumpfHaupt1 := rfl
  have ht : ∀ σ1 ρ1, torRuf taP R taWarte σ1 ρ1 = R taWarte σ1 ρ1 := fun _ _ => if_pos rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · simp only [taLocksH, execStmt] at h1
    have h2 := execBlock_eins_logikV _ _ _ _ _ _ (mapWelt_logikV h1)
    simp only [taRufWarte, execStmt, ht] at h2
    split at h2
    · cases h2
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h2
      exact hOV _ _ _ _ hR g rfl
    · cases h2
  · simp only [taRetH1, execEnd] at h1
    cases h1

theorem taP_koerper_ruhe : KoerperGutG taP 0 taRuhe := by
  intro O' _ _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : taP.rumpf taRuhe = taRumpfRuhe := rfl
  rw [hr] at hrun
  simp only [taRumpfRuhe, execEnd] at hrun
  cases hrun

theorem taP_koerper : ∀ f, KoerperGutG taP 0 f := by
  intro f
  cases f
  · exact taP_koerper_haupt0
  · exact taP_koerper_fuelle
  · exact taP_koerper_haupt1
  · exact taP_koerper_warte
  · exact taP_koerper_ruhe

def taE0 : Ereignis taD := .gibt TaLock.k

/-- **All premises of `ziel_ort_geraet` hold jointly on `taP`.** -/
theorem taP_vertragAmOrt : ∀ M : RufMaschineG taD,
    RufErreichbarG taP taO 0 (RufStartG taP taSp taInit) M → VertragAmOrtG taP M :=
  ziel_ort_geraet taP taO 0 taFs taSp taInit taE0 taO_gut taO_lokal taFs_voll taP_fragment
    taP_fuss taP_koerper taP_start taInit_exklusiv

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.taP_vertragAmOrt
