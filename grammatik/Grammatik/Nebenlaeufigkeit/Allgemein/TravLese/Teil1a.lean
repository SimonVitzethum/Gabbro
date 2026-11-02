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


end Gabbro.Grammatik.TravLese
