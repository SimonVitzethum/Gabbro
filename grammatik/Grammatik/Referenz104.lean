/-
  File:      Grammatik/Referenz104.lean
  Subject:   `beispiele/104-referenz.gab`, TRANSLATED BY HAND into the Lean
             syntax, run on machine G, and checked against the premises of
             `ziel_ort_voll`.

  ## The translation, construct by construct

  | surface (104-referenz.gab)                    | Lean form here                                  |
  |-----------------------------------------------|-------------------------------------------------|
  | `module beispiel::referenz { … }`             | NO FORM (a namespace; this file)                |
  | `const NKONTO : u32 = 2;`                     | inlined: `count := fun _ => 2`                  |
  | `type Betrag = u32 in 0 .. 10;`               | `Ty.int 0 10` (the carrier width `u32`: NO FORM)|
  | `type Stand = u32 in 0 .. 100;`               | `Ty.int 0 100` (width: NO FORM)                 |
  | `table Konto count NKONTO { slot { stand } }` | `Tab := Unit`, `count 2`, `Feld := Unit`,       |
  |                                               | `typ := .int 0 100`, `tabNr 0 = some ()`        |
  | `lock M protects { stand } rank 0`            | `Lock := Unit`, `rang 0`, `braucht := [.inl M]` |
  | `held <= 50 ops` (lock hold budget)           | NO FORM (no hold budget in `Deklaration`)       |
  | `impl fn einzahlen(k : ptr<normal, rw> Konto, | params `[.ptr 0 true, .index 2, .int 0 10]`;    |
  |   i : index into Konto, b : Betrag)`          | the address space `normal`: NO FORM             |
  | `requires Held(M)`                            | `haelt := [M]`, `requires := .wahr`             |
  | `ensures old(k.slots[i].stand) <=             | `.le (.altSlot Konto stand i) (.durch k … i)`;  |
  |   k.slots[i].stand`                           | `old(p->…)` has no pointer form (`altDurch`):   |
  |                                               | written `altSlot` of the table the type names   |
  | `effects { reads k.slots, writes k.slots,     | `schreibt := true`; `reads`: NO FORM (reads are |
  |   locks M }`                                  | the computed footprint); `locks M`: `haelt`     |
  | `costs <= 16 ops` / `<= 8 ops`                | `r4Decl` with `kostenPasst` (`KostenG.lean`)    |
  | `k.slots[i].stand = 100;`                     | `.assignDurch (.var k) Konto rfl stand (.var i) |
  |                                               |   100 rfl hL`                                   |
  | `lies(k, i);`                                 | `.call lies [ptrOf Konto false, var i] hp rfl`: |
  |                                               | a `rw` pointer passed as `r` has no coercion    |
  |                                               | form; `ptrOf` of the same table (a pointer's    |
  |                                               | value is `()`, the denotation is identical)     |
  | end of `einzahlen` (falls off)                | `.ret .keine perm` (an `Endblock` must end)     |
  | `impl fn lies(k : ptr<normal, r> Konto,       | params `[.ptr 0 false, .index 2]`,              |
  |   i : index into Konto) -> Stand`             | `erg := some (.int 0 100)`                      |
  | `ensures result == k.slots[i].stand`          | `.eq (.var .hier) (.durch k … i)`               |
  | `effects { reads k.slots, locks M }`          | `schreibt := false`, `haelt := [M]`             |
  | `return k.slots[i].stand;`                    | `.ret (.wert (.durch (.var k) … (.var i))) perm`|

  NOT in the file, added and flagged: the driver `treiber` (the file's
  header says the C driver runs `einzahlen` then `lies`; in Lean it is a
  function holding `M` by signature: `einzahlen(&Konto, 0, 7);
  lies(&Konto, 0); return`) and the idle function `ruhe` for every other
  thread (G starts every thread in some function).

  ## The finding

  Every premise of `ziel_ort_voll` holds on this translation EXCEPT the user
  obligation of `einzahlen` (`r4_einzahlen_nicht_V`): its `ensures
  old(stand) <= stand` is not provable from the body triple, because the
  call `lies(k, i)` sits between the write and the return, and the handler
  class of the obligation (`RespektiertVertraege`) constrains a callee only
  by its `ensures` -- NOT by its declared frame (`lies` writes nothing). A
  contract-respecting handler may answer `lies` with a world where the
  slot is `0` (and result `0`, meeting `lies`'s `ensures`), and the caller's
  `ensures` fails. The machine's `lies` writes nothing, and on the reached
  run the contracts hold at every logged event (`r4_vertragAmOrt_lauf`,
  checked directly) -- the goal theorem just cannot deliver it. The repair
  is the callee analogue of `RahmenO`: handlers that also respect the
  callee's declared writes.
-/
import Grammatik.KostenGZeuge
import Grammatik.ZielOrtVollZeuge

namespace Gabbro.Grammatik

/-! ## 1. The declaration -/

inductive R4Fn where
  | einzahlen
  | lies
  | treiber
  | ruhe
  deriving DecidableEq

def r4SigEin : Signatur Unit Empty Unit Empty where
  params := [.ptr 0 true, .index 2, .int 0 10]
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def r4SigLies : Signatur Unit Empty Unit Empty where
  params := [.ptr 0 false, .index 2]
  erg := some (.int 0 100)
  gruende := 0
  haelt := [()]
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def r4SigTreiber : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def r4SigRuhe : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- `104-referenz.gab`'s declarations: table `Konto` (2 slots, field
    `stand : 0 .. 100`), lock `M` (rank 0) protecting it; functions
    `einzahlen`, `lies`, and the flagged additions `treiber`, `ruhe`. -/
def r4D : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 100
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => true
  ggeteilt := fun e => nomatch e
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => [.inl ()]
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := R4Fn
  sig := fun | .einzahlen => 0 | .lies => 1 | .treiber => 2 | .ruhe => 3
  sigNr := fun n => match n with
    | 0 => r4SigEin | 1 => r4SigLies | 2 => r4SigTreiber | _ => r4SigRuhe
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
  ggeteilt_bewacht := fun e => nomatch e

def r4Ein : r4D.Fn := R4Fn.einzahlen
def r4Lies : r4D.Fn := R4Fn.lies
def r4Treiber : r4D.Fn := R4Fn.treiber
def r4Ruhe : r4D.Fn := R4Fn.ruhe

abbrev r4M : List (Res r4D) := [Res.held (D := r4D) ()]

theorem r4Darf : darf r4D () r4M := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

/-! ## 2. The bodies and contracts -/

/-- `einzahlen`'s parameters: `k` (`.hier`), `i`, `b`. -/
abbrev r4GEin : Ctx := [.ptr 0 true, .index 2, .int 0 10]

/-- `k.slots[i].stand = 100;` -/
def r4Schreib : Stmt r4D (vertragVon r4D r4Ein) false r4GEin r4M r4M :=
  .assignDurch (.var .hier) () rfl () (.var (.dort .hier)) (.weiter (by decide) (by decide) (.lit 100))
    rfl r4Darf

/-- `einzahlen` calls `lies`: same lock, `lies` writes nothing. -/
theorem r4HpLies : RufPasst r4D (vertragVon r4D r4Ein) (r4D.signatur r4Lies) r4M where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩

/-- `lies(k, i);` -- `k` (rw) passed as `r`: the pointer to the same table. -/
def r4RufLies : Stmt r4D (vertragVon r4D r4Ein) false r4GEin r4M (nach r4D r4Lies r4M) :=
  .call r4Lies (.cons (.ptrOf () 0 rfl false) (.cons (.var (.dort .hier)) .nil)) r4HpLies rfl

def r4RetEin : Endblock r4D (vertragVon r4D r4Ein) false r4GEin r4M :=
  .ret .keine (List.Perm.refl _)

def r4RestEin : Endblock r4D (vertragVon r4D r4Ein) false r4GEin r4M := .cons r4RufLies r4RetEin

/-- `einzahlen`: `k.slots[i].stand = 100; lies(k, i);` -/
def r4RumpfEin : Endblock r4D (vertragVon r4D r4Ein) false r4GEin r4M := .cons r4Schreib r4RestEin

/-- `ensures old(k.slots[i].stand) <= k.slots[i].stand` -/
def r4EnsEin : Expr r4D (ErgCtx (r4D.params r4Ein) (r4D.erg r4Ein)) (vertragVon r4D r4Ein).ende
    .bool :=
  .le (.altSlot () () (.var (.dort .hier)) r4Darf)
    (.durch (.var .hier) () rfl () (.var (.dort .hier)) r4Darf)

/-- `lies`'s parameters: `k` (`.hier`), `i`. -/
abbrev r4GLies : Ctx := [.ptr 0 false, .index 2]

/-- `return k.slots[i].stand;` -/
def r4RumpfLies : Endblock r4D (vertragVon r4D r4Lies) false r4GLies r4M :=
  .ret (.wert (.durch (.var .hier) () rfl () (.var (.dort .hier)) r4Darf)) (List.Perm.refl _)

/-- `ensures result == k.slots[i].stand` -/
def r4EnsLies : Expr r4D (ErgCtx (r4D.params r4Lies) (r4D.erg r4Lies)) (vertragVon r4D r4Lies).ende
    .bool :=
  .eq (.var .hier) (.durch (.var (.dort .hier)) () rfl () (.var (.dort (.dort .hier))) r4Darf)

/-- The driver (flagged addition): `einzahlen(&Konto, 0, 7); lies(&Konto, 0); return`. -/
theorem r4HpEinT : RufPasst r4D (vertragVon r4D r4Treiber) (r4D.signatur r4Ein) r4M where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩

theorem r4HpLiesT : RufPasst r4D (vertragVon r4D r4Treiber) (r4D.signatur r4Lies) r4M where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => by
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩

def r4Idx0 {Γ : Ctx} : Expr r4D Γ r4M (.index 2) := .weiter (by decide) (by decide) (.lit 0)
def r4Sieben {Γ : Ctx} : Expr r4D Γ r4M (.int 0 10) := .weiter (by decide) (by decide) (.lit 7)

def r4RufEinT : Stmt r4D (vertragVon r4D r4Treiber) false [] r4M (nach r4D r4Ein r4M) :=
  .call r4Ein (.cons (.ptrOf () 0 rfl true) (.cons r4Idx0 (.cons r4Sieben .nil))) r4HpEinT rfl

def r4RufLiesT : Stmt r4D (vertragVon r4D r4Treiber) false [] r4M (nach r4D r4Lies r4M) :=
  .call r4Lies (.cons (.ptrOf () 0 rfl false) (.cons r4Idx0 .nil)) r4HpLiesT rfl

def r4RetT : Endblock r4D (vertragVon r4D r4Treiber) false [] r4M := .ret .keine (List.Perm.refl _)

def r4RestT : Endblock r4D (vertragVon r4D r4Treiber) false [] r4M := .cons r4RufLiesT r4RetT

def r4RumpfTreiber : Endblock r4D (vertragVon r4D r4Treiber) false [] r4M := .cons r4RufEinT r4RestT

def r4RumpfRuhe : Endblock r4D (vertragVon r4D r4Ruhe) false [] [] := .ret .keine List.Perm.nil

/-- The translated program. -/
def r4P : Programm r4D where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .einzahlen => r4EnsEin
    | .lies => r4EnsLies
    | .treiber => .wahr
    | .ruhe => .wahr
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
  | grund σ' r => exact (Fin.cast hr r).elim0
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
    `104-referenz.gab` does NOT meet the user obligation of the goal
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

/-- **The run of `104-referenz.gab` on G** (7 steps of thread 0): the driver
    calls `einzahlen(&Konto, 0, 7)` (1), which writes `Konto[0].stand = 100`
    through its pointer (2: memory `0 -> 100`), calls `lies(k, 0)` (3), which
    returns the slot (4, logged); `einzahlen` returns (5, logged); the
    driver calls `lies(&Konto, 0)` (6), which returns (7, logged). -/
theorem r4Lauf : ∃ M : RufMaschineG r4D,
    RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
    (M.speicher.slots () 0 ()).n = 100 ∧
    (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
      RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log) ∧
    VertragAmOrtG r4P M := by
  have h00 : (RufStartG r4P r4Sp r4Init).faeden 0 = ⟨[], ⟨r4Treiber, .nil, r4Sp.welt [],
      ⟨false, [], r4M, .nil, .ende r4RumpfTreiber⟩⟩, startSpur r4Treiber,
      [RufEreignisF.eintritt r4Treiber .nil (r4Sp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG r4P r4Sp r4Init).faeden 0).spur = [()] := rfl
  -- 1: call `einzahlen`
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := r4P) (O := r4O) (passes := 0) h00 r4Ein _ r4HpEinT rfl
    r4RestT .nil rfl (r4HgM hoff0)
  have hoff1 : offen (M1.faeden 0).spur = [()] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- 2: the write through the pointer
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := r4P) (O := r4O) (passes := 0) e1 r4Schreib r4RestEin _
    rfl rfl (r4HgM (r4Hoff e1 hoff1)) _ _ rfl ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [()] := by
    rw [hZ2.spur]
    exact ((Erw.schreibSlot _ _ _ _ _ _).offen).trans (((Erw.lese _ _ _).offen).trans hoff1)
  have e2 := hZ2.1
  try dsimp only at e2
  -- 3: call `lies`
  obtain ⟨M3, s3, hZ3⟩ := w_rufEnde (P := r4P) (O := r4O) (passes := 0) e2 r4Lies _ r4HpLies rfl
    r4RetEin _ rfl (r4HgM (r4Hoff e2 hoff2))
  have hoff3 : offen (M3.faeden 0).spur = [()] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  -- 4: `lies` returns
  obtain ⟨M4, s4, hG4⟩ := w_rueckP (P := r4P) (O := r4O) (passes := 0) e3 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (r4HgM (r4Hoff e3 hoff3))
  have hoff4 : offen (M4.faeden 0).spur = [()] := by
    rw [hG4.1]; exact ((Erw.lese _ _ _).offen).trans hoff3
  have e4 := hG4.1
  try dsimp only at e4
  -- 5: `einzahlen` returns
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := r4P) (O := r4O) (passes := 0) e4 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (r4HgM (r4Hoff e4 hoff4))
  have hoff5 : offen (M5.faeden 0).spur = [()] := by
    rw [hG5.1]; exact ((Erw.lese _ _ _).offen).trans hoff4
  have e5 := hG5.1
  try dsimp only at e5
  -- 6: the driver calls `lies`
  obtain ⟨M6, s6, hZ6⟩ := w_rufEnde (P := r4P) (O := r4O) (passes := 0) e5 r4Lies _ r4HpLiesT rfl
    r4RetT .nil rfl (r4HgM (r4Hoff e5 hoff5))
  have hoff6 : offen (M6.faeden 0).spur = [()] := by
    rw [hZ6.spur, (Erw.lese _ _ _).offen]; exact hoff5
  have e6 := hZ6.1
  try dsimp only at e6
  -- 7: `lies` returns
  obtain ⟨M7, s7, hG7⟩ := w_rueckP (P := r4P) (O := r4O) (passes := 0) e6 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (r4HgM (r4Hoff e6 hoff6))
  have hr7 : RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M7 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7
  have hsp4 : (M4.speicher.slots () 0 ()).n = 100 := by
    rw [hG4.2]
    show (M3.speicher.slots () 0 ()).n = 100
    rw [hZ3.2]
    show (M2.speicher.slots () 0 ()).n = 100
    rw [hZ2.2]
    rfl
  have hsp7 : (M7.speicher.slots () 0 ()).n = 100 := by
    rw [hG7.2]
    show (M6.speicher.slots () 0 ()).n = 100
    rw [hZ6.2]
    show (M5.speicher.slots () 0 ()).n = 100
    rw [hG5.2]
    exact hsp4
  have hfremd : ∀ t : Faden, t ≠ 0 → M7.faeden t = (RufStartG r4P r4Sp r4Init).faeden t := by
    intro t ht
    rw [rufSchrittG_fremd s7 t ht, rufSchrittG_fremd s6 t ht, rufSchrittG_fremd s5 t ht,
      rufSchrittG_fremd s4 t ht, rufSchrittG_fremd s3 t ht, rufSchrittG_fremd s2 t ht,
      rufSchrittG_fremd s1 t ht]
  have hlog7 := congrArg RufFadenG.log hG7.1
  have hlog6 := congrArg RufFadenG.log e6
  have hlog5 := congrArg RufFadenG.log e5
  have hlog4 := congrArg RufFadenG.log e4
  refine ⟨M7, hr7, hsp7, ?_, ?_⟩
  · rw [hlog7]
    dsimp only
    exact ⟨_, _, _, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · intro t ev hev
    refine ⟨fun g rho s0 _ => rfl, ?_⟩
    intro g rho v s0 s1' he
    subst he
    by_cases ht : t = 0
    · subst ht
      rw [hlog7] at hev
      dsimp only at hev
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with h | h | h | h | h | h | h
      · cases h
        exact decide_eq_true rfl
      · cases h
      · cases h
        show decide ((r4Sp.slots () 0 ()).n ≤ (M4.speicher.slots () 0 ()).n) = true
        rw [hsp4]
        rfl
      · cases h
        exact decide_eq_true rfl
      · cases h
      · cases h
      · cases h
    · rw [hfremd t ht, r4_start_log] at hev
      have hi : r4Init t = ⟨r4Ruhe, .nil⟩ := if_neg ht
      rw [hi] at hev
      simp only [List.mem_singleton] at hev
      cases hev

/-! ## 7. The premises, jointly -/

/-- **`referenz104_zeuge`.** On the hand translation of
    `104-referenz.gab` (plus the flagged driver and idle function), every
    premise of `ziel_ort_voll` holds EXCEPT the user obligation of
    `einzahlen`, which is refuted; the declared costs pass `kostenPasst`;
    on the reached run (memory `0 -> 100`, the return of `einzahlen`
    logged) the contracts hold at every logged event, checked directly. -/
theorem referenz104_zeuge :
    GutO r4O ∧ (∀ g : r4D.Fn, g ∈ r4Fs) ∧ programmImFragmentV r4P r4Fs = true ∧
    fussOrtB r4P r4Fs = true ∧ StartGut r4P r4Sp r4Init ∧ StartExklusiv (D := r4D) r4Init ∧
    KoerperGutV r4P 0 r4Lies ∧ KoerperGutV r4P 0 r4Treiber ∧ KoerperGutV r4P 0 r4Ruhe ∧
    ¬ KoerperGutV r4P 0 r4Ein ∧ kostenPasst r4P 0 r4Decl r4Fs = true ∧
    ∃ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
      (r4Sp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
        RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log) ∧
      VertragAmOrtG r4P M := by
  obtain ⟨M, hr, hsp, hlog, hV⟩ := r4Lauf
  exact ⟨r4O_gut, r4Fs_voll, r4P_fragment, r4P_fuss, r4P_start, r4Init_exklusiv,
    r4P_koerper_lies, r4P_koerper_treiber, r4P_koerper_ruhe, r4_einzahlen_nicht_V,
    r4P_kostenPasst, M, hr, rfl, hsp, hlog, hV⟩

/-! ## CUTS:

  What is proved: the hand translation `r4D`/`r4P` of `104-referenz.gab`
  (the construct table in the header); the decidable premises
  (`r4P_fragment`, `r4P_fuss`), the declared costs (`r4P_kostenPasst`),
  `GutO`, the start facts, the user obligations of `lies`, the driver and
  the idle function; the refutation of `einzahlen`'s obligation
  (`r4_einzahlen_nicht_V`); a reached run of G and the contracts on it
  (`r4Lauf`, `referenz104_zeuge`).

  What is NOT proved: `ziel_ort_voll` (or `ziel_ort_geraet`) for `r4P` --
  its premise `∀ f, KoerperGutV r4P 0 f` is false. The repair (handlers
  that respect the callee's declared frame, the call analogue of
  `RahmenO`) is proposed, not built. Constructs without a Lean form: the
  module, named constants, carrier widths, address spaces, the lock hold
  budget `held <= N ops`, the `reads` effect, the implicit fall-off
  return, the `rw`-to-`r` pointer coercion (written as `ptrOf` of the same
  table), `old(p->f)` through a pointer (written as `old` of the table).
-/

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.r4_einzahlen_nicht_V
#print axioms Gabbro.Grammatik.r4Lauf
#print axioms Gabbro.Grammatik.referenz104_zeuge
