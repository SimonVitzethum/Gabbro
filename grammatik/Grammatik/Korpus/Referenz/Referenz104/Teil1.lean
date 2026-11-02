module

public import Grammatik.Korpus.Referenz.Referenz104.Teil1Basis
public import Grammatik.Logik.Fortschritt.KostenGZeuge
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge

@[expose] public section


namespace Gabbro.Grammatik
/-- The translated program. -/
def r4P : Programm r4D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures
    | .einzahlen => r4EnsEin
    | .lies => r4EnsLies
    | .treiber => .tru
    | .ruhe => .tru
  rumpf
    | .einzahlen => r4RumpfEin
    | .lies => r4RumpfLies
    | .treiber => r4RumpfTreiber
    | .ruhe => r4RumpfRuhe

def r4Fs : List r4D.Fn := [r4Ein, r4Lies, r4Treiber, r4Ruhe]

theorem r4Fs_voll : ∀ g : r4D.Fn, g ∈ r4Fs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self))

/-! ## 3. The decidable premises -/

theorem r4P_fragment : programmImFragmentV r4P r4Fs = true := by decide

theorem r4P_fuss : fussOrtB r4P r4Fs = true := by decide

instance r4D_fn_deq : DecidableEq r4D.Fn := inferInstanceAs (DecidableEq R4Fn)

/-- `costs <= 16 ops` / `costs <= 8 ops` as a declared cost table (the driver
    and the idle function get their own). -/
def r4Decl : r4D.Fn → Nat
  | .einzahlen => 16
  | .lies => 8
  | .treiber => 40
  | .ruhe => 4

theorem r4P_kostenPasst : kostenPasst r4P 0 r4Decl r4Fs = true := by decide

/-! ## 4. Oracle, start, and the user obligations -/

def r4O : Orakel r4D where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

theorem r4O_gut : GutO r4O := fun a => nomatch a

def r4Null : Wert r4D (.int 0 100) := ⟨0, by decide, by decide⟩

def r4Sp : Speicher r4D := ⟨fun _ _ _ => r4Null, fun g => nomatch g⟩

/-- Thread 0 runs the driver (holding `M`), every other thread is idle. -/
def r4Init : Faden → Σ f : r4D.Fn, Env r4D (r4D.params f) :=
  fun t => if t = 0 then ⟨r4Treiber, .nil⟩ else ⟨r4Ruhe, .nil⟩

theorem r4P_start : StartGut r4P r4Sp r4Init := by
  intro t
  unfold r4Init
  by_cases h0 : t = 0
  · rw [if_pos h0]; rfl
  · rw [if_neg h0]; rfl

theorem r4Init_exklusiv : StartExklusiv (D := r4D) r4Init := by
  intro t u htu L ht hu
  unfold r4Init at ht hu
  by_cases h0 : t = 0
  · have hu0 : u ≠ 0 := fun e => htu (h0.trans e.symm)
    rw [if_neg hu0] at hu
    exact absurd hu List.not_mem_nil
  · rw [if_neg h0] at ht
    exact absurd ht List.not_mem_nil

/-- `lies` meets its obligation: the returned value is the slot. -/
theorem r4P_koerper_lies : KoerperGutV r4P 0 r4Lies := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · have hr : r4P.rumpf r4Lies = r4RumpfLies := rfl
    rw [hr] at hrun
    simp only [r4RumpfLies, execEnd] at hrun
    cases hrun
    exact decide_eq_true rfl
  · have hr : r4P.rumpf r4Lies = r4RumpfLies := rfl
    rw [hr] at hrun
    simp only [r4RumpfLies, execEnd] at hrun
    cases hrun

theorem r4P_koerper_ruhe : KoerperGutV r4P 0 r4Ruhe := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : r4P.rumpf r4Ruhe = r4RumpfRuhe := rfl
  rw [hr] at hrun
  simp only [r4RumpfRuhe, execEnd] at hrun
  cases hrun

/-- A call of a `requires true` function through the gate never fails the
    gate when the handler blames nobody. -/
theorem r4_call_tor {V : Vertrag r4D} {l : Bool} {Γ : Ctx} {Λ : List (Res r4D)}
    (O : Orakel r4D) (passes : Nat)
    (R : ∀ f : r4D.Fn, World r4D → Env r4D (r4D.params f) → RufAusgang f) (hOV : OhneVorbedingung R)
    (g : r4D.Fn) (args : Args r4D Γ Λ (r4D.params g)) (hp : RufPasst r4D V (r4D.signatur g) Λ)
    (hr : r4D.gruende g = 0) (σ : World r4D) (ρ : Env r4D Γ) (g' : r4D.Fn) :
    execStmt O passes (torRuf r4P R) (Stmt.call (l := l) g args hp hr) σ ρ ≠
      .logik (.vorbedingung g') := by
  have ht : ∀ σ1 ρ1, torRuf r4P R g σ1 ρ1 = R g σ1 ρ1 := fun _ _ => if_pos (by cases g <;> rfl)
  simp only [execStmt, ht]
  cases hR : R g (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => intro h; cases h
  | why σ' r => exact (Fin.cast hr r).elim0
  | logik e => intro h; cases h; exact hOV _ _ _ _ hR g' rfl
  | hardware e => intro h; cases h

theorem r4P_koerper_treiber : KoerperGutV r4P 0 r4Treiber := by
  intro O' _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : r4P.rumpf r4Treiber = r4RumpfTreiber := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · exact r4_call_tor _ _ R hOV _ _ _ _ _ _ _ h1
  · rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ h1 with h2 | ⟨σ2, ρ2, _, h2⟩
    · exact r4_call_tor _ _ R hOV _ _ _ _ _ _ _ h2
    · simp only [r4RetT, execEnd] at h2
      cases h2

/-! ## 5. The finding: `einzahlen`'s obligation fails -/

/-- The world with every slot `0` (the trace kept). -/
def r4Nullwelt (σ : World r4D) : World r4D :=
  ⟨fun _ _ _ => r4Null, fun g => (nomatch g), σ.spur⟩

/-- A handler that answers `lies` with the slot set to `0` and result `0`
    (meeting `lies`'s `ensures`), and fails every other call with a
    non-caller logic outcome. -/
def r4Boese : ∀ f : r4D.Fn, World r4D → Env r4D (r4D.params f) → RufAusgang f
  | .lies, σ, _ => .ok (r4Nullwelt σ) r4Null
  | f, _, _ => .logik (.abstieg f)

theorem r4Boese_respektiert : RespektiertVertraege r4P r4Boese := by
  intro f σ ρ _ σ' v h
  cases f with
  | lies =>
      cases h
      rfl
  | einzahlen => cases h
  | treiber => cases h
  | ruhe => cases h

theorem r4Boese_ohne : OhneVorbedingung r4Boese := by
  intro g σ ρ e h g' he
  cases g with
  | lies => cases h
  | einzahlen => cases h; cases he
  | treiber => cases h; cases he
  | ruhe => cases h; cases he

/-- **The finding (`r4_einzahlen_nicht_V`).** `einzahlen` of
    `0104-referenz.gab` does NOT meet the user obligation of the goal
    theorems: from an entry world with the slot at `50`, the body writes
    `100` and calls `lies`; the contract-respecting handler `r4Boese`
    answers `lies` with the slot at `0` (and result `0`, so `lies`'s
    `ensures` holds), and `einzahlen` returns with `old(stand) = 50 > 0`.
    The handler class does not bound a callee by its declared frame. -/
theorem r4_einzahlen_nicht_V : ¬ KoerperGutV r4P 0 r4Ein := by
  intro h
  let σ : World r4D := ⟨fun _ _ _ => ⟨50, by decide, by decide⟩, fun g => (nomatch g), []⟩
  let ρ : Env r4D (r4D.params r4Ein) := .cons () (.cons ⟨0, by decide, by decide⟩
    (.cons ⟨7, by decide, by decide⟩ .nil))
  have hK := (h r4O (gutO_rahmenO r4O_gut) r4Boese r4Boese_respektiert r4Boese_ohne σ ρ rfl).1
  have hrun : execEnd r4O 0 r4Boese (r4P.rumpf r4Ein) σ ρ = .zurueck _ () := rfl
  have := hK _ _ hrun
  exact (by decide : (false = true) → False) this

/-! ## 6. The run on G, and the contracts on it -/

/-- The start log of a thread: the entry of its start function. -/
theorem r4_start_log (t : Faden) :
    ((RufStartG r4P r4Sp r4Init).faeden t).log =
      [RufEreignisF.eintritt (r4Init t).1 (r4Init t).2 (r4Sp.welt [])] := by
  show (match r4Init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, r4Sp.welt [], ⟨false, r4D.params g,
        Signatur.anfang r4D (r4D.signatur g), rho, .ende (r4P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (r4Sp.welt [])]⟩ : RufFadenG r4D)).log = _
  cases r4Init t
  rfl

theorem r4HgM {s : List (Ereignis r4D)} (h : offen s = [()]) : HeldGenau r4M (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem r4Hoff {M : RufMaschineG r4D} {f : Faden} {z : RufFadenG r4D} {x : List Unit}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

end Gabbro.Grammatik
