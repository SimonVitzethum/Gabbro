/- Two lexical releases, shared by canonical sequential execution and G7 cleanup. -/
module
public import Grammatik.Kern.Semantik.Semantik.T2.ScopedLocks
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
public import Grammatik.Logik.Ruf.Maschine.RufMaschineG.Schritt.G7
@[expose] public section

namespace Gabbro.Grammatik.ScopedLocksProbe
open Parser.Uebersetze Parser.UebersetzeAllg

def unit : UProg := {
  tabs := []
  locks := [{name := "inherited", rank := 0, guard := []},
    {name := "outer", rank := 1, guard := []}, {name := "inner", rank := 2, guard := []}]
  fns := [{name := "returner", params := [], kinds := [], res := none, resBool := true,
    gruende := 1, held := ["inherited"], puts := [], gives := [], body := [], ret := .bool .tru}] }

abbrev D := declOf unit
def fn : D.Fn := ⟨0, by decide⟩
abbrev V := vertragVon D fn
def inherited : D.Lock := ⟨0, by decide⟩
def outer : D.Lock := ⟨1, by decide⟩
def inner : D.Lock := ⟨2, by decide⟩
abbrev entryResources : List (Res D) := [.held inherited]
abbrev bodyResources : List (Res D) := [.held inner, .held outer, .held inherited]

/-- The inherited signature lock is residual, never part of lexical cleanup. -/
def cleanup : RueckRessourcen D V bodyResources :=
  ⟨[inner, outer], by decide⟩

theorem outer_rank : ∀ M, Res.held M ∈ entryResources → D.rang M < D.rang outer := by
  intro M member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Res.held.injEq] at member
  subst M
  decide

theorem inner_rank : ∀ M, Res.held M ∈ Res.held outer :: entryResources → D.rang M < D.rang inner := by
  intro M member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Res.held.injEq] at member
  rcases member with rfl | rfl <;> decide

/-- These are the same typed lexical wrappers for both return channels. -/
def nestedReturn : Stmt D V false [] entryResources entryResources :=
  .locks outer outer_rank (.cons (.locks inner inner_rank
    (.cons (.retScoped (.val .tru) cleanup) .nil)) .nil)

def nestedReason : Stmt D V false [] entryResources entryResources :=
  .locks outer outer_rank (.cons (.locks inner inner_rank
    (.cons (.retWhyScoped ⟨0, by decide⟩ cleanup) .nil)) .nil)

def memory : Speicher D where
  slots t := Fin.elim0 t
  globs g := Fin.elim0 g

def entry : World D := memory.welt [.nimmt inherited []]
def acquired : World D := (entry.nimmt outer).nimmt inner
def released : World D := (acquired.gibt inner).gibt outer

def oracle : Orakel D where
  wirkt a := Fin.elim0 a
  regLies r := Fin.elim0 r
  regSchreib r := Fin.elim0 r
  sichtbar g := Fin.elim0 g

def noCalls (f : D.Fn) (_ : World D) (_ : Env D (D.params f)) : RufAusgang f :=
  .logik (.abstieg f)

def program : Programm D where
  invariante i := Fin.elim0 i
  requires _ := .tru
  ensures _ := .tru
  rumpf f := by
    have same : f = fn := Fin.ext (by
      have bound : f.val < 1 := f.isLt
      change f.val = 0
      omega)
    subst f
    exact .cons nestedReturn (.ret (.val .tru) (List.Perm.refl _))

/-- The real source return head, with both lexical release markers still present. -/
def pending : GRest D V false [] bodyResources :=
  .dann (.cons (.retScoped (.val .tru) cleanup) .nil) (.frei inner (.frei outer .leer))

def saved : (ErgVal D V.erg ⊕ Fin V.gruende) × World D := ⟨.inl true, acquired⟩

def sourceThread : RufFadenG D :=
  ⟨[], ⟨fn, Env.nil, entry, ⟨false, [], bodyResources, Env.nil, pending⟩⟩, acquired.spur, []⟩

def sourceMachine : RufMaschineG D := ⟨memory, fun _ => sourceThread, [], entry⟩

def cleanupThread : RufFadenG D :=
  ⟨[], ⟨fn, Env.nil, entry, ⟨false, [], _, Env.nil, .aufraeumen saved [inner, outer]⟩⟩,
    acquired.spur, []⟩

def cleanupMachine : RufMaschineG D :=
  ⟨memory, rufUpdateG sourceMachine.faeden 0 cleanupThread, [], entry⟩

def lastThread : RufFadenG D :=
  ⟨[], ⟨fn, Env.nil, entry, ⟨false, [], _, Env.nil, .aufraeumen saved [outer]⟩⟩,
    (acquired.gibt inner).spur, []⟩

def lastMachine : RufMaschineG D :=
  ⟨memory, rufUpdateG cleanupMachine.faeden 0 lastThread, [⟨0, .gibt inner⟩], entry⟩

def finishedThread : RufFadenG D :=
  ⟨[], ⟨fn, Env.nil, entry, ⟨false, [], V.ende, Env.nil, .zurueckgekehrt saved⟩⟩,
    released.spur, []⟩

def finishedMachine : RufMaschineG D :=
  ⟨memory, rufUpdateG lastMachine.faeden 0 finishedThread,
    [⟨0, .gibt inner⟩, ⟨0, .gibt outer⟩], entry⟩

/-- Both channels return the exact same twice-released world, preserve the saved value
    or reason, and leave the inherited lock held. The trace lists EVERY event. -/
theorem execStmt_locks_retScoped_zeuge (passes : Nat) :
    bodyResources.Perm (V.ende ++ cleanup.scopes.map Res.held) ∧
    inherited ∉ cleanup.scopes ∧
    execStmt oracle passes noCalls nestedReturn entry Env.nil = .zurueck released true ∧
    execStmt oracle passes noCalls nestedReason entry Env.nil = .why released ⟨0, by decide⟩ ∧
    released.spur = [.gibt outer, .gibt inner, .nimmt inner [outer, inherited],
      .nimmt outer [inherited], .nimmt inherited []] ∧
    released.haelt = [inherited] ∧
    (released.spur.filterMap (fun event => match event with | .gibt L => some L | _ => none)) =
      [outer, inner] := by
  exact ⟨cleanup.genau, by decide, rfl, rfl, rfl, rfl, rfl⟩

/-- The canonical G7 save step and its two release steps agree with that same world.
    The final step delivers the already saved answer; no wrapper release follows it. -/
theorem execStmt_locks_g7_zeuge (passes : Nat) :
    RufSchrittG7 program oracle passes sourceMachine 0 cleanupMachine ∧
    RufSchrittG7 program oracle passes cleanupMachine 0 lastMachine ∧
    RufSchrittG7 program oracle passes lastMachine 0 finishedMachine ∧
    finishedMachine.weltVon 0 = released ∧
    finishedMachine.lauf = [⟨0, .gibt inner⟩, ⟨0, .gibt outer⟩] ∧
    execStmt oracle passes noCalls nestedReturn entry Env.nil =
      .zurueck (finishedMachine.weltVon 0) true := by
  have save : RufSchrittG7 program oracle passes sourceMachine 0 cleanupMachine :=
    .rueckScopedWert sourceMachine 0 Env.nil pending (.val .tru) cleanup rfl rfl
      (by decide) (by
        intro L member
        change L ∈ [inner, outer, inherited]
        simpa only [List.mem_cons, List.not_mem_nil, or_false, Res.held.injEq] using member)
      acquired rfl [] rfl (by decide)
  have first : RufSchrittG7 program oracle passes cleanupMachine 0 lastMachine :=
    .rueckFreigabe cleanupMachine 0 Env.nil saved inner [outer] rfl (by decide)
  have last : RufSchrittG7 program oracle passes lastMachine 0 finishedMachine :=
    .rueckFreigabeLetzte lastMachine 0 Env.nil saved outer rfl finishedThread rfl
  exact ⟨save, first, last, rfl, rfl, rfl⟩

/-- Ordinary continuation and loop exits still release their one lexical lock. -/
theorem execStmt_locks_continuation_zeuge (passes : Nat) :
    execStmt oracle passes noCalls (.locks (V := V) (l := true) (Γ := []) outer outer_rank .nil)
      entry Env.nil = .ok ((entry.nimmt outer).gibt outer) Env.nil ∧
    execStmt oracle passes noCalls (.locks (V := V) outer outer_rank (.cons (.leave rfl) .nil))
      entry Env.nil = .leave rfl ((entry.nimmt outer).gibt outer) Env.nil ∧
    execStmt oracle passes noCalls (.locks (V := V) outer outer_rank (.cons (.next rfl) .nil))
      entry Env.nil = .next rfl ((entry.nimmt outer).gibt outer) Env.nil := by
  exact ⟨rfl, rfl, rfl⟩

end Gabbro.Grammatik.ScopedLocksProbe
