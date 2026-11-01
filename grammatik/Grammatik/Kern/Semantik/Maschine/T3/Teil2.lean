module

public import Grammatik.Kern.Semantik.Maschine.T2
public import Grammatik.Kern.Semantik.Maschine.T3.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}

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
