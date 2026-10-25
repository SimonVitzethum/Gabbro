import Grammatik.Zielsatz.Projekte.Ziel
import Grammatik.Zielsatz.Projekte.Ohne
import Grammatik.Bausteine.Arena.Ownership.Body.Witness

/-!
  File:      Grammatik/Zielsatz/Projekte/ZeugeBesitz.lean
  Subject:   A WITNESS of `gabbro_ziel_projekte`: an ALLOCATION handed across a project boundary.

  The ownership fixture `Body/Witness.lean` cut into two projects: the library owns `make`, which
  allocates a slot of the four-slot arena and RETURNS the owning index (or its reason on a full
  arena); the application owns `user`, which calls `make` with an `else`, RELEASES the allocation
  it was handed, and returns. The arena and its ownership interfaces are declared by the program;
  the goal's concrete checker accepts the composed unit, its ownership acceptance included (both
  bodies pass the ownership check, the allocator words are plain, the arena is empty in the start
  memory, the start is handed no allocation). `gabbro_ziel_projekte` then gives every leg of
  `ZielFX`, `besitz` included: the allocation made in one project and released in the other is
  owned exactly once on every reachable machine.
-/

namespace Gabbro.Grammatik.ProjekteBesitzZeuge

open Gabbro.Grammatik Zielsatz ArenaOwnership Body InvDynZeuge Source

/-! ## The fixture: `make` allocates and hands over, `user` releases (it handles a full arena
    itself, so it has no reason exit and is a thread root). -/

def userSig : Signatur FD.Tab FD.Glob FD.Lock FD.Marke :=
  { Witness.makeSig with erg := none, gruende := 0 }

def sigTable : Nat → Signatur FD.Tab FD.Glob FD.Lock FD.Marke
  | 0 => Witness.makeSig
  | _ => userSig

@[reducible] def WD : Deklaration :=
  { FD with
    Fn := Bool
    sig := Witness.sigOf
    passt := fun f n => decide (Witness.sigOf f = n)
    rzusage := fun e => nomatch e
    sigNr := sigTable
    passt_ok := by
      intro f n h
      have hn : Witness.sigOf f = n := of_decide_eq_true h
      subst hn
      exact SigPasst.refl _ _
    eigner_nie_erzeugt := fun _ _ _ _ h => by cases h
    invarianten_gehalten := fun _ i => nomatch i }

def A : FreiForm WD where
  tab := ()
  feld := 0
  zaehl := 0
  hz := rfl
  hpos := by decide
  komm := 1
  hk := rfl
  hzwei := by decide
  kopf := 2
  hkopf := rfl
  nxt := 1
  hnxt := rfl
  hk1 := by decide
  hk2 := by decide
  hf := by decide

theorem tab_right : darf WD A.tab [] := fun _ h => by cases h
theorem glob_right (g : WD.Glob) : gdarf WD g [] := fun _ h => by cases h

def seven {Γ : Ctx} : Expr WD Γ [] (WD.typ A.tab A.feld) := .widen (by decide) (by decide) (.lit 7)

theorem hpUser : RufPasst WD (vertragVon WD false) (WD.signatur true) [] where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], List.Sublist.refl []⟩
  hh := fun _ h => by cases h

def makeReturn : Block WD (vertragVon WD true) false [Ty.index 4] [] [] :=
  .cons (.ret (valueResult (τ := Ty.index 4) rfl (.var .here)) (List.Perm.refl [])) .nil

def makeAlloc : Block WD (vertragVon WD true) false [] [] [] :=
  Block.arenaAlloc A.toArenaForm seven rfl tab_right rfl (glob_right _)
    (.retWhy ⟨0, by decide⟩ (List.Perm.refl [])) makeReturn

/-- `make` (library): allocate, return the owning index; a full arena is its reason. -/
def makeBody : Endblock WD (vertragVon WD true) false [] [] :=
  .cons (.ite .tru makeAlloc makeAlloc) (.retWhy ⟨0, by decide⟩ (List.Perm.refl []))

def release : Block WD (vertragVon WD false) false [Ty.index 4] [] [] :=
  Block.freiVar A .here rfl tab_right rfl (glob_right _) .nil

/-- `user` (application): call `make`, release what it hands over; on a full arena return. -/
def userBody : Endblock WD (vertragVon WD false) false [] [] :=
  .bindCallElse true .nil rfl hpUser (by decide)
    (.ret .empty (List.Perm.refl []))
    (.cons (.ite .tru release release) (.ret .empty (List.Perm.refl [])))

def P : Programm WD where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun | true => makeBody | false => userBody

/-- `make` returns an owning index, `user` returns nothing; neither takes a parameter. -/
def I : Interfaces A
  | true => ⟨.nil, rfl, .owner⟩
  | false => ⟨.nil, rfl, .plain⟩

/-! ## The program and its two projects -/

/-- The declared start memory: every slot zero, the free-list head at the empty marker. -/
def sp0 : Speicher WD where
  slots := fun _ _ f => by
    change Wert WD (if f = 0 then .int 0 255 else .int 0 4)
    split
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  globs := fun g => if g = 2 then ⟨4, by decide, by decide⟩ else ⟨0, by decide, by decide⟩

/-- The program's unit: `user` is the root, the arena with its ownership interfaces is declared. -/
def E : Einheit WD where
  P := P
  S := SperrInv.leer WD
  Q := axWahr WD
  starts := [⟨false, .nil⟩]
  sp0 := sp0
  arenen := [⟨A, I⟩]

/-- **The library**: it owns `make` and declares the arena. -/
def pLib : Projekt WD := ⟨fun f => f, { E with starts := [] }⟩

/-- **The application**: it owns `user`, the thread root. -/
def pApp : Projekt WD := ⟨fun f => !f, { E with arenen := [] }⟩

def ps : List (Projekt WD) := [pApp, pLib]

theorem verbindbar : ∀ p ∈ ps, Verbindbar E p.E := by
  intro p hp
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem deckend : Deckend ps := by
  intro f
  cases f
  · exact ⟨pApp, List.mem_cons_self, rfl⟩
  · exact ⟨pLib, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

theorem komp_eq : komponiere E ps = E := by
  have hP : koerperVon P ps = P.rumpf := by
    funext f
    cases f <;> rfl
  have hQ : qAlle ps = axWahr WD := by
    funext a
    exact nomatch a
  show (⟨mitRumpf P (koerperVon P ps), SperrInv.leer WD, qAlle ps, _, sp0, _, _⟩ : Einheit WD) = E
  rw [hP, hQ]
  rfl

def fs : List WD.Fn := [true, false]
def cs : List (WD.Tab ⊕ WD.Glob) := [.inl (), .inr 0, .inr 1, .inr 2, .inr 3]

theorem fs_voll : ∀ g : WD.Fn, g ∈ fs := fun g => by cases g <;> simp [fs]
theorem ls_voll : ∀ L : WD.Lock, L ∈ ([] : List WD.Lock) := fun L => nomatch L
theorem cs_voll : ∀ c : WD.Tab ⊕ WD.Glob, c ∈ cs := by
  intro c
  rcases c with t | g
  · cases t; simp [cs]
  · revert g; decide

/-- (a) The goal's concrete checker accepts the composed unit, its ownership acceptance included. -/
theorem akzeptiert_E : akzeptiertX_pruefer.akzeptiert E fs [] cs = true := by decide

theorem akzeptiert : akzeptiertX_pruefer.akzeptiert (komponiere E ps) fs [] cs = true := by
  rw [komp_eq]
  exact akzeptiert_E

def O : Orakel WD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => true

theorem hardware : HardwareAnnahmen O (komponiere E ps).Q := by
  rw [komp_eq]
  exact ⟨(fun a => nomatch a), ⟨(fun r => nomatch r), fun _ _ _ _ => rfl⟩, axVertragO_wahr O⟩

theorem frei : programmLogikFrei P fs = true := by decide

/-- (b) Neither project owes a hand-written proof: no contract, no invariant, `logik`-free bodies,
    no atomic global (`nutzerTeilO_ohne`). -/
theorem nutzer : ∀ p ∈ ps, NutzerTeilO p := by
  intro p hp
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact nutzerTeilO_ohne fs_voll (fun _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl) rfl frei
      (fun a ha => by
        simp only [pApp, E, List.append_nil, List.mem_singleton] at ha
        subst ha
        rfl)
  · exact nutzerTeilO_ohne fs_voll (fun _ => rfl) rfl rfl (fun _ => rfl) (fun _ => rfl) rfl frei
      (fun a ha => by simp [pLib, E] at ha)

/-! ## The witness -/

/-- **The witness**: every leg of `ZielFX`, `besitz` over the program's arena included, on every
    reachable thread machine over GX of the program linked from the two projects. -/
theorem projekte_besitz_zeuge (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine WD.mitRuhe)
    (hK : FadenErreichbarX (komponiere E ps).P.mitRuhe O.mitRuhe passes
      (GeteiltV (D := WD) (komponiere E ps).P (komponiere E ps).ws)
      (FadenStart (komponiere E ps).P.mitRuhe (speicherR (komponiere E ps).sp0)
        (initRuhe (komponiere E ps).starts) lebt0) K) :
    ZielFX (komponiere E ps).P.mitRuhe (komponiere E ps).S.mitRuhe O.mitRuhe passes
      (GeteiltV (D := WD) (komponiere E ps).P (komponiere E ps).ws)
      (RufStartG (komponiere E ps).P.mitRuhe (speicherR (komponiere E ps).sp0)
        (initRuhe (komponiere E ps).starts))
      ((komponiere E ps).arenen.map (·.mitRuhe)) K :=
  gabbro_ziel_projekte akzeptiertX_pruefer WD E ps ⟨fs, fs_voll⟩ ⟨[], ls_voll⟩ ⟨cs, cs_voll⟩
    verbindbar (by simp [ps]) deckend akzeptiert nutzer O hardware passes _ _ (laufzeit_voll _)
    lebt0 K hK

/-- **The ownership leg itself**: the allocation `make` (library) hands to `user` (application) is
    owned exactly once on every reachable machine. -/
theorem besitz_ueber_die_grenze (passes : Nat) (lebt0 : Faden → Bool) (K : FadenMaschine WD.mitRuhe)
    (hK : FadenErreichbarX (komponiere E ps).P.mitRuhe O.mitRuhe passes
      (GeteiltV (D := WD) (komponiere E ps).P (komponiere E ps).ws)
      (FadenStart (komponiere E ps).P.mitRuhe (speicherR (komponiere E ps).sp0)
        (initRuhe (komponiere E ps).starts) lebt0) K) :
    Machine.OwnInv (Ruhe.liftA A) (Ruhe.liftI I) K.m :=
  (projekte_besitz_zeuge passes lebt0 K hK).besitz _ (List.Mem.head _)

/-- **Non-degenerate**: the allocating and the releasing function lie in different projects, the
    releasing one calls the allocating one, and the actual run of `user` from the declared start
    memory allocates slot `0` in the library and puts it back on the free list in the application. -/
theorem grenze : pLib.eigen true = true ∧ pApp.eigen false = true ∧
    ruftB (komponiere E ps).P false true = true ∧
    ∃ σ', rufAt P O 0 2 false (sp0.welt []) .nil = .ok σ' () ∧ A.stand σ' = 1 ∧ A.kopfSt σ' = 0 := by
  refine ⟨rfl, rfl, ?_, ⟨_, rfl, rfl, rfl⟩⟩
  rw [komp_eq]
  decide

#print axioms projekte_besitz_zeuge
#print axioms besitz_ueber_die_grenze
#print axioms grenze

end Gabbro.Grammatik.ProjekteBesitzZeuge
