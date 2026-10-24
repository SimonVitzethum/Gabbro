import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Bausteine.Arena.Ownership.Body.Witness
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaAllocForm

/-! **A witness of the ownership leg of `GabbroZiel`.** One function on the
four-slot arena `FA` allocates from the counter, stores a payload, releases
the allocation and returns; the unit declares the arena with its interfaces.
The concrete checker of the goal accepts the unit -- its ownership acceptance
included: the bodies pass the ownership check, the allocator words are plain,
the declared start memory holds an empty arena, the start is handed no
allocation -- the user's obligation holds and the oracle meets the hardware
assumptions: every premise of `gabbro_ziel` is discharged, and its leg
`besitz` holds on every thread-machine run over GX. The function's actual run
executes both allocator forms. -/

namespace Gabbro.Grammatik.ArenaOwnership.Ruhe.GoalWitness

open InvDynZeuge Source Body Machine Zielsatz

abbrev V : Vertrag FD := vertragVon FD ()

theorem tab_right : darf FD FA.tab [] := fun _ h => by cases h
theorem glob_right (g : FD.Glob) : gdarf FD g [] := fun _ h => by cases h

def seven {Γ : Ctx} : Expr FD Γ [] (FD.typ FA.tab FA.feld) := .widen (by decide) (by decide) (.lit 7)

/-- `free x;` of the bound allocation. -/
def release : Block FD V false [Ty.index 4] [] [] :=
  Block.freiVar FA .here rfl tab_right rfl (glob_right _) .nil

/-- `let x = alloc FA (7) else return; free x;` -/
def allocFree : Block FD V false [] [] [] :=
  Block.arenaAlloc FA.toArenaForm seven rfl tab_right rfl (glob_right _) (.ret .empty (List.Perm.refl [])) release

def body : Endblock FD V false [] [] :=
  .cons (.ite .tru allocFree allocFree) (.ret .empty (List.Perm.refl []))

def P : Programm FD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => body

/-- The function takes no parameter and returns nothing. -/
def I : Interfaces FA := fun _ => ⟨.nil, rfl, .plain⟩

def S : SperrInv FD := ⟨(fun L => nomatch L), (fun L => nomatch L)⟩

/-- The declared start memory: every slot zero, the free-list head at the empty marker. -/
def sp0 : Speicher FD where
  slots := fun _ _ f => by
    change Wert FD (if f = 0 then .int 0 255 else .int 0 4)
    split
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  globs := fun g => if g = 2 then ⟨4, by decide, by decide⟩ else ⟨0, by decide, by decide⟩

def E : Einheit FD where
  P := P
  S := S
  Q := axWahr FD
  starts := [⟨(), .nil⟩]
  sp0 := sp0
  arenen := [⟨FA, I⟩]

def fs : List FD.Fn := [()]
def cs : List (FD.Tab ⊕ FD.Glob) := [.inl (), .inr 0, .inr 1, .inr 2, .inr 3]

theorem fs_voll : ∀ g : FD.Fn, g ∈ fs := fun g => by cases g; simp [fs]
theorem ls_voll : ∀ L : FD.Lock, L ∈ ([] : List FD.Lock) := fun L => nomatch L
theorem cs_voll : ∀ c : FD.Tab ⊕ FD.Glob, c ∈ cs := by
  intro c
  rcases c with t | g
  · cases t; simp [cs]
  · revert g; decide

/-- (a) The goal's concrete checker accepts the unit, its arena included. -/
theorem check : akzeptiertX_pruefer.akzeptiert E fs [] cs = true := by decide

/-- The executable ownership check accepts the program. -/
theorem owner_check : checkProgram E.P FA I fs = true := by decide

def O : Orakel FD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => true

/-- (c) The oracle meets the hardware assumptions. -/
theorem hardware : HardwareAnnahmen O E.Q :=
  ⟨(fun a => nomatch a), ⟨(fun r => nomatch r), fun _ _ _ _ => rfl⟩, axVertragO_wahr O⟩

/-- The body never ends in a `logik` outcome, whatever the environment answers. -/
theorem body_no_logik (S' : SperrInv FD) (O' : Orakel FD) (U : Umwelt FD) (A' : AUmwelt FD) (passes : Nat)
    (R : ∀ f : FD.Fn, World FD → Env FD (FD.params f) → RufAusgang f) (σ : World FD) (ρ : Env FD (FD.params ()))
    (e : Logik FD) : execEndHA (V := V) S' O' U A' passes R body σ ρ ≠ EndAusgang.logik e := by
  simp only [body, allocFree, release, Block.arenaAlloc, Block.arenaRumpf, Block.freiVar, execEndHA, execStmtHA,
    execBlockHA]
  repeat' (first
    | (simp [Ausgang.schrumpf, EndAusgang.zuAusgang]; done)
    | split
    | (rename_i heq; (repeat' split at heq) <;> simp [Ausgang.schrumpf, EndAusgang.zuAusgang] at heq))

/-- (b) The user's obligation with the atomic rely. -/
theorem nutzer : NutzerPflichtA E := by
  refine ⟨⟨fun passes f => ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨(fun L => nomatch L), axEnsLokal_wahr⟩⟩,
    ⟨(fun L => nomatch L), fun _ _ => rfl⟩⟩
  · intro O' _ _ _ U _ A' _ R _ _ σ ρ _
    exact ⟨fun _ _ _ => rfl, fun g => body_no_logik _ O' U A' passes _ σ ρ _⟩
  · intro O' _ _ _ U _ A' _ R _ _ σ ρ _ e
    exact body_no_logik _ O' U A' passes R σ ρ e
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
    exact nomatch i
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r _
    exact r.elim0

/-- **The witness**: every premise of `gabbro_ziel` holds on this unit, so its leg `besitz` -- ownership of
    the arena -- holds on every thread-machine run over GX of its runtime start. -/
theorem besitz_zeuge (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine FD.mitRuhe)
    (hK : FadenErreichbarX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := FD) E.P E.ws)
      (FadenStart E.P.mitRuhe (speicherR E.sp0) (initRuhe E.starts) lebt0) K) :
    OwnInv (liftA FA) (liftI I) K.m :=
  (gabbro_ziel akzeptiertX_pruefer FD E ⟨fs, fs_voll⟩ ⟨[], ls_voll⟩ ⟨cs, cs_voll⟩ check nutzer O hardware
    passes _ _ (laufzeit_voll E) lebt0 K hK).besitz _ (List.Mem.head _)

/-- Non-degenerate: the function's actual run allocates slot `0` and puts it back on the list. -/
theorem actual_run (O' : Orakel FD) (passes : Nat) :
    ∃ σ', rufAt P O' passes 1 () (sp0.welt []) .nil = .ok σ' () ∧ FA.stand σ' = 1 ∧ FA.kopfSt σ' = 0 :=
  ⟨_, rfl, rfl, rfl⟩

#print axioms besitz_zeuge
#print axioms actual_run

end Gabbro.Grammatik.ArenaOwnership.Ruhe.GoalWitness
