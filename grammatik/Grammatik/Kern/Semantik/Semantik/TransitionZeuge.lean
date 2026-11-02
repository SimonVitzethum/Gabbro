module

public import Grammatik.Kern.Semantik.Semantik.Transition
public import Grammatik.Kern.Semantik.Syscall.SyscallPaarung

@[expose] public section
namespace Gabbro.Grammatik.TransitionProben

/-- The six private parameters are the index and endpoints of each write. -/
abbrev capturedContext : Ctx :=
  [.index 8, .int 0 8192, .int 0 8192, .index 8, .int 0 8192, .int 0 8192]

def capturedSignature : Signatur Unit Empty Empty Empty :=
  { swD.signatur () with params := capturedContext }

def D : Deklaration :=
  { swD with
    sigNr := fun _ => capturedSignature
    passt_ok := fun _ _ _ => SigPasst.refl _ _
    eigner_nie_erzeugt := fun _ _ _ _ member => by cases member }

def firstIndex : Var capturedContext (.index 8) := .here
def firstSource : Var capturedContext (.int 0 8192) := .there .here
def firstTarget : Var capturedContext (.int 0 8192) := .there (.there .here)
def secondIndex : Var capturedContext (.index 8) := .there (.there (.there .here))
def secondSource : Var capturedContext (.int 0 8192) := .there (.there (.there (.there .here)))
def secondTarget : Var capturedContext (.int 0 8192) := .there (.there (.there (.there (.there .here))))

def first : TransitionWrite D capturedContext [] :=
  .slot () () rfl (.var firstIndex) (.var firstSource) (.var firstTarget) (by intro w h; cases h)

def second : TransitionWrite D capturedContext [] :=
  .slot () () rfl (.var secondIndex) (.var secondSource) (.var secondTarget) (by intro w h; cases h)

def writes : List (TransitionWrite D capturedContext []) := [first, second]

theorem writes_frozen : ∀ write ∈ writes, write.Frozen := by
  intro write member
  rcases List.mem_cons.mp member with same | member
  · subst same; exact .slot _ _ rfl firstIndex firstSource firstTarget _
  · rcases List.mem_cons.mp member with same | member
    · subst same; exact .slot _ _ rfl secondIndex secondSource secondTarget _
    · cases member

theorem writes_rights : ∀ write ∈ writes, write.Permitted (vertragVon D ()) := by
  intro write member
  rcases List.mem_cons.mp member with same | member
  · subst same; rfl
  · rcases List.mem_cons.mp member with same | member
    · subst same; rfl
    · cases member

/-- Potentially aliased targets are not admitted just because both stores type-check. -/
def distinct : Expr D capturedContext [] .bool :=
  .not (.eq (.var firstIndex) (.var secondIndex))

def finish : Endblock D (vertragVon D ()) false capturedContext [] :=
  .ret .empty List.Perm.nil

def P : Programm D where
  invariante i := nomatch i
  requires _ := transitionRequires writes distinct
  ensures _ := transitionEnsures writes
  rumpf _ := transitionEnd (vertragVon D ()) writes writes_rights finish

def expansion : TransitionExpansion P () where
  writes := writes
  clause := distinct
  frozen := writes_frozen
  rights := writes_rights
  result_none := rfl
  resources := rfl
  requires_exact := rfl
  ensures_exact := rfl
  body_exact := rfl

/-- Capture reads both targets from the same entry memory. In particular,
    the second target reads cell zero before the first store changes it. -/
def capture : Args D [] [] capturedContext :=
  .cons (.widen (by decide) (by decide) (.lit 0))
    (.cons (.slot () () (.widen (by decide) (by decide) (.lit 0)) (by intro w h; cases h))
      (.cons (.widen (by decide) (by decide) (.lit 7))
        (.cons (.widen (by decide) (by decide) (.lit 1))
          (.cons (.slot () () (.widen (by decide) (by decide) (.lit 1)) (by intro w h; cases h))
            (.cons (.slot () () (.widen (by decide) (by decide) (.lit 0))
              (by intro w h; cases h)) .nil)))))

def entry : World D :=
  { slots := fun _ _ _ => ⟨0, by decide, by decide⟩
    globs := fun g => nomatch g
    spur := [] }

def captured : Env D capturedContext := evalArgs entry capture entry .nil

def after : World D := transitionWorld writes entry captured entry

theorem captured_independent :
    writes.Pairwise (fun earlier later => earlier.Preserves later entry captured) := by
  apply List.Pairwise.cons
  · intro later member
    have same := List.mem_singleton.mp member
    subst same
    intro state
    rfl
  · exact List.Pairwise.cons (fun _ member => by cases member) List.Pairwise.nil

/-- The full certificate's effect, frame and postcondition premises hold
    jointly for this actual two-write call. -/
theorem transitionExpansion_correct_zeuge (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    writes.Pairwise (fun earlier later => earlier.Preserves later entry captured) ∧
    execEnd O passes R (P.rumpf ()) entry captured =
      execEnd O passes R finish after captured ∧
    Rahmen (D.schreibt ()) (D.gschreibt ()) entry after ∧
    wahr? (eval entry (P.ensures ()) after captured) = true ∧
    (after.slots () 0 ()).n = 7 := by
  have correct := expansion.correct O passes R entry captured captured_independent
  exact ⟨captured_independent, correct.1, correct.2.1, correct.2.2, rfl⟩

/-- The real generic expansion theorem is inhabited by two ordered writes,
    a nontrivial requires clause and an entry read of an earlier target. -/
theorem transitionEnd_correct_zeuge (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    (∀ write ∈ writes, write.Frozen ∧ write.Permitted (vertragVon D ())) ∧
    wahr? (eval entry (P.requires ()) entry captured) = true ∧
    wahr? (eval entry (P.ensures ()) after captured) = true ∧
    execEnd O passes R (P.rumpf ()) entry captured = execEnd O passes R finish after captured ∧
    Rahmen (D.schreibt ()) (D.gschreibt ()) entry after ∧
    (after.slots () 0 ()).n = 7 ∧ (after.slots () 1 ()).n = 0 ∧
    after.slots () 0 () ≠ entry.slots () 0 () := by
  refine ⟨fun write member => ⟨writes_frozen write member, writes_rights write member⟩,
    rfl, rfl, expansion.body_correct O passes R entry entry captured,
    transitionWorld_frame writes writes_rights entry entry captured, rfl, rfl, ?_⟩
  intro same
  have numbers := congrArg Zahl.n same
  change (7 : Int) = 0 at numbers
  exact (by decide : (7 : Int) ≠ 0) numbers

/-- A false declaration clause remains a false caller duty. -/
theorem transitionRequires_iff_zeuge :
    wahr? (eval entry (transitionRequires writes .fls) entry captured) = false ∧
    wahr? (eval entry distinct entry captured) = true := ⟨rfl, rfl⟩

/-- A requires-only transition performs no store and preserves the continuation. -/
theorem transition_requires_only_zeuge (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) :
    execEnd O passes R (transitionEnd (vertragVon D ()) [] (by intro w h; cases h) finish)
      entry captured = execEnd O passes R finish entry captured ∧
    transitionWorld ([] : List (TransitionWrite D capturedContext [])) entry captured entry = entry :=
  ⟨rfl, rfl⟩

/-- Equal target indices violate the generated function's real requires
    check, before either store can execute. -/
def aliased : Env D capturedContext :=
  captured.set secondIndex ⟨0, by decide, by decide⟩

theorem transition_alias_refused_zeuge (O : Orakel D) (passes : Nat) :
    rufAt P O passes 2 () entry aliased = .logik (.vorbedingung ()) := rfl

/-- The existing primitive constant shift is unchanged. The comparison is
    of the resulting memory under its legal-entry premise. -/
def constantD : Deklaration := { D with erlaubt := fun _ _ source target => decide (source = 0 ∧ target = 7) }

def constantEntry : World constantD :=
  { slots := fun _ _ _ => ⟨0, by decide, by decide⟩
    globs := fun g => nomatch g
    spur := [] }

def constantEnv : Env constantD [.index 8] := .cons ⟨0, by decide, by decide⟩ .nil

theorem transition_constant_shift_zeuge (O : Orakel constantD) (passes : Nat)
    (R : ∀ f : constantD.Fn, World constantD → Env constantD (constantD.params f) → RufAusgang f) :
    let value : Wert constantD (constantD.typ () ()) := ⟨7, by decide, by decide⟩
    let shifted := (constantEntry.lese [] [.inl ()]).schreibSlot () [] 0 () value
    let stored := constantEntry.schreibSlot () [] 0 () value
    execStmt O passes R (Stmt.shift (V := vertragVon constantD ()) (l := false)
      () () rfl (.var .here) 0 7 (by decide) rfl rfl (by intro w h; cases h))
      constantEntry constantEnv = .ok shifted constantEnv ∧
    execStmt O passes R (Stmt.assignSlot (V := vertragVon constantD ()) (l := false)
      () () (.var .here) (.widen (by decide) (by decide) (.lit 7)) rfl
      (by intro w h; cases h)) constantEntry constantEnv = .ok stored constantEnv ∧
    shifted.slots = stored.slots ∧ shifted.globs = stored.globs :=
  transition_constant_shift O passes R () () rfl .here 0 7 (by decide) rfl rfl
    (by intro w h; cases h) constantEntry constantEnv rfl

end Gabbro.Grammatik.TransitionProben
