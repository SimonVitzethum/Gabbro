/-
  File:      Grammatik/Nebenlaeufigkeit/Allgemein/TravLese.lean
  Subject:   THE WITNESS of the full race theorem `rennfrei_g_voll` (`rennfrei_g_voll_zeuge`): the run of
             `TravAwaitsLauf.lean` with thread 1 READING `flag` plainly instead of awaiting it.

  Since 2026-10-21 an `awaits` needs an atomic static (`Block.awaits` carries `D.atomar g = true`), and an
  atomic carrier is exempt from the lock discipline (`AtomarAusgenommen`). The race witness needs a
  lock-guarded carrier that is neither atomic nor a payload, so it lives on this copy of the declaration:
  `flag` is not atomic, and `warte` reads it with `let v = flag;` under `k`. Everything else -- the
  declaration, the program, the oracle, the 29 steps -- is the run of `TravAwaitsLauf.lean`, step 24 being
  `dannBind` instead of `dannAwaits` (same footprint `[flag]`, same recorded read event).
  The names are those of `TravAwaitsZeuge.lean`/`TravAwaitsLauf.lean` in the namespace `TravLese`.
-/
module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetZeuge

@[expose] public section



namespace Gabbro.Grammatik.TravLese

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
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
  .widen (by decide) (by decide) (.lit 1)

/-- The traverse body: `tab[i] := 1`. -/
def taSchreibI : Stmt taD (vertragVon taD taFuelle) true [.index (taD.count ())] taLL taLL :=
  .assignSlot () () (.var .here) taEins rfl taDarfL

def taTravBody : Block taD (vertragVon taD taFuelle) true [.index (taD.count ())] taLL taLL :=
  .cons taSchreibI .nil

/-- `traverse tab invariant true { tab[i] := 1 }` -/
def taTrav : Stmt taD (vertragVon taD taFuelle) false [] taLL taLL :=
  .traverse () .tru taTravBody

def taRetF : Endblock taD (vertragVon taD taFuelle) false [] taLL :=
  .ret .empty (List.Perm.refl _)

def taRumpfFuelle : Endblock taD (vertragVon taD taFuelle) false [] taLL :=
  .cons taTrav taRetF

/-- `fuelle` ensures every slot of `tab` is `1`. -/
def taEnsFuelle : Expr taD (ErgCtx (taD.params taFuelle) (taD.erg taFuelle))
    (vertragVon taD taFuelle).ende .bool :=
  .forallSlots () (.eq (.slot () () (.var .here) taDarfL) (.lit 1)) taDarfL

/-- `haupt0` calls `fuelle`: same lock, the callee's writes are the caller's. -/
theorem taHpFuelle : RufPasst taD (vertragVon taD taHaupt0) (taD.signatur taFuelle) taLL where
  hw := fun _ _ => rfl
  hg := fun _ h => by cases h
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (fun L => by
    cases L
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) taHeld_ne,
        fun h => absurd (List.mem_singleton.mp h) taLock_ne⟩)
  hx := RufPasst.hx_von (fun L => by
    cases L
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) taHeld_ne,
        fun h => absurd (List.mem_singleton.mp h) taLock_ne⟩)

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
  .ret .empty (List.Perm.refl _)

def taRestH0 : Endblock taD (vertragVon taD taHaupt0) false [] taLL :=
  .cons taLocksK taRetH0

def taRumpfHaupt0 : Endblock taD (vertragVon taD taHaupt0) false [] taLL :=
  .cons taRufFuelle taRestH0

/-- `haupt1` calls `warte` inside `locks k`: the callee holds exactly `k`. -/
theorem taHpWarte : RufPasst taD (vertragVon taD taHaupt1) (taD.signatur taWarte) taKL where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (fun L => by
    cases L
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm taHeld_ne),
        fun h => absurd (List.mem_singleton.mp h) (Ne.symm taLock_ne)⟩
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩)
  hx := RufPasst.hx_von (fun L => by
    cases L
    · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm taHeld_ne),
        fun h => absurd (List.mem_singleton.mp h) (Ne.symm taLock_ne)⟩
    · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩)

def taRufWarte : Stmt taD (vertragVon taD taHaupt1) false [] taKL (nach taD taWarte taKL) :=
  .call taWarte .nil taHpWarte rfl

def taWarteBody : Block taD (vertragVon taD taHaupt1) false [] taKL taKL := .cons taRufWarte .nil

def taLocksH : Stmt taD (vertragVon taD taHaupt1) false [] [] [] :=
  .locks TaLock.k (fun _ h => nomatch h) taWarteBody

def taRetH1 : Endblock taD (vertragVon taD taHaupt1) false [] [] := .ret .empty List.Perm.nil

def taRumpfHaupt1 : Endblock taD (vertragVon taD taHaupt1) false [] [] :=
  .cons taLocksH taRetH1

/-- `let v = flag;` -- a plain read of the lock-guarded, non-atomic `flag`. -/
def taAwaitsBlock : Block taD (vertragVon taD taWarte) false [] taKL taKL :=
  .bind (.glob () taGdarfK) .nil

def taIteW : Stmt taD (vertragVon taD taWarte) false [] taKL taKL :=
  .ite .tru taAwaitsBlock .nil

def taRetW : Endblock taD (vertragVon taD taWarte) false [] taKL :=
  .ret .empty (List.Perm.refl _)

def taRumpfWarte : Endblock taD (vertragVon taD taWarte) false [] taKL :=
  .cons taIteW taRetW

def taRumpfRuhe : Endblock taD (vertragVon taD taRuhe) false [] [] :=
  .ret .empty List.Perm.nil

/-- The program: a non-trivial `ensures` for `fuelle`, `true` elsewhere. -/
def taP : Programm taD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | .haupt0 => .tru
    | .fuelle => taEnsFuelle
    | .haupt1 => .tru
    | .warte => .tru
    | .ruhe => .tru
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


/-! ## 1. Start states and small facts -/

def taI0 : Wert taD (.index (taD.count ())) := ⟨0, by decide, by decide⟩
def taI1 : Wert taD (.index (taD.count ())) := ⟨1, by decide, by decide⟩

theorem taAlle : alleIndizes (taD.count ()) = [taI0, taI1] := by rfl

def taM0 : RufMaschineG taD := RufStartG taP taSp taInit

def taZ0 : RufFadenG taD :=
  ⟨[], ⟨taHaupt0, .nil, taSp.welt [], ⟨false, [], taLL, .nil, .ende taRumpfHaupt0⟩⟩,
    startSpur taHaupt0, [RufEreignisF.eintritt taHaupt0 .nil (taSp.welt [])]⟩

def taZ1 : RufFadenG taD :=
  ⟨[], ⟨taHaupt1, .nil, taSp.welt [], ⟨false, [], [], .nil, .ende taRumpfHaupt1⟩⟩,
    startSpur taHaupt1, [RufEreignisF.eintritt taHaupt1 .nil (taSp.welt [])]⟩

theorem taM0_faden0 : taM0.faeden 0 = taZ0 := by rfl

theorem taM0_faden1 : taM0.faeden 1 = taZ1 := by rfl

/-- Threads other than 0 and 1 hold nothing at the start. -/
theorem taM0_offen (g : Faden) (h0 : g ≠ 0) (L : TaLock) : L ∉ offen (taM0.faeden g).spur := by
  intro h
  have h' := (offen_start (P := taP) taSp taInit g L).mp h
  rw [taInit_haelt, if_neg h0] at h'
  exact List.not_mem_nil h'

theorem taHgL {s : List (Ereignis taD)} (h : offen s = [TaLock.l]) :
    HeldGenau taLL (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) taHeld_ne,
      fun h => absurd (List.mem_singleton.mp h) taLock_ne⟩

theorem taHgK {s : List (Ereignis taD)} (h : offen s = [TaLock.k]) :
    HeldGenau taKL (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun h => absurd (List.mem_singleton.mp h) (Ne.symm taHeld_ne),
      fun h => absurd (List.mem_singleton.mp h) (Ne.symm taLock_ne)⟩
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem taHgKL {s : List (Ereignis taD)} (h : offen s = [TaLock.k, TaLock.l]) :
    HeldGenau taKLL (offen s) := by
  rw [h]
  intro L
  cases L
  · exact ⟨fun _ => List.mem_cons_of_mem _ List.mem_cons_self,
      fun _ => List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem taHg0 {s : List (Ereignis taD)} (h : offen s = []) :
    HeldGenau ([] : List (Res taD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- The release marker after `haupt0`'s publish block. -/
def taKFrei : GRest taD (vertragVon taD taHaupt0) false [] taKLL :=
  .frei TaLock.k (.dann .nil (.ende taRetH0))

theorem taHoff {M : RufMaschineG taD} {f : Faden} {z : RufFadenG taD} {x : List TaLock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

/-! ## 2. Thread 0: 19 steps -/

end Gabbro.Grammatik.TravLese
