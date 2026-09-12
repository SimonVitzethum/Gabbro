/-
  File:      Grammatik/BlattGegenbeispiel.lean
  Subject:   **COUNTEREXAMPLE TO `hBlattAll` FOR WRITING LEAVES** (lane 14).

  The goal theorem (`ziel_nutzer_last_aus_pc_Q`, `Ziel.lean` section 13) owes the
  premise `hBlattAll`: every leaf statement of a thread leaves that thread's own
  `QRequires`/`QEnsures` unchanged. It is discharged only for memory-preserving
  leaves (`hBlattAll_speicherfest_aus_feuerung`, `Maschine.lean` section 22).

  This file builds a concrete small `Deklaration`/`Programm` and a WRITING leaf
  whose execution changes the truth of the thread's own `QEnsures`, and proves
  that `hBlattAll` is therefore false for it.

  The construction (one shared slot, boolean contracts over it):

    * `D1`: `Tab = Unit` (one table), one field `()` of type `.bool`;
      `count = 1`; `Fn = Unit` (one function); `schreibt = true` everywhere;
      nothing guarded (`braucht = []`), hence `darf` holds trivially.
    * `P1`: `requires = .wahr` (always true); `ensures = .slot () () i0`
      (the slot's current boolean value, read at index 0).
    * Writing leaf: `assignSlot () () i0 e` where `e` is the negation of the
      slot's current value. Firing it from a thread world whose slot reads
      `false` writes `true`; `QEnsures` is false before and true after, so the
      `Post` iff fails. Hence the full `hBlattAll` conjunction fails.
-/
import Grammatik.Maschine
import Grammatik.Satz
import Grammatik.Extraktion

namespace Gabbro.Grammatik.BG

open Gabbro.Grammatik

/-- One shared table: a single slot holding one boolean. -/
def D1 : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
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
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The contract of the only function: no parameters, no result. -/
def V1 : Vertrag D1 :=
  { schreibt := fun _ => true
    gschreibt := fun e => nomatch e
    erg := none
    gruende := 0
    haelt := []
    produziert := [] }

/-- Index expression `0` into the single table (valid: `0 <= 0 <= count - 1 = 0`). -/
def i0 : Expr D1 [] [] (.index (D1.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- Slot read `T.slots[0]` as a boolean contract expression. -/
def slotE : Expr D1 [] [] .bool :=
  .slot () () i0 (fun w => nomatch w)

/-- Value expression: the negation of the slot's current value. -/
def negE : Expr D1 [] [] .bool :=
  .nicht slotE

/-- The writing leaf: `T.slots[0] := not T.slots[0]`. -/
def writeLeaf : Stmt D1 V1 false [] [] [] :=
  .assignSlot () () i0 negE rfl (fun w => nomatch w)

/-- The writing leaf is a leaf. -/
theorem writeLeaf_blatt : writeLeaf.istBlatt = true := rfl

/-- The writing leaf is not memory-preserving. -/
theorem writeLeaf_nicht_fest : writeLeaf.speicherfest = false := rfl

/-- The program: `requires = true`; `ensures = T.slots[0]`. -/
def P1 : Programm D1 where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .slot () () i0 (fun w => nomatch w)
  rumpf := fun _ => .ret .keine (List.Perm.refl [])

/-- The oracle: no axioms, no registers, no globals. -/
def O1 : Orakel D1 where
  wirkt := fun a _ _ => nomatch a
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- A world with the slot set to `b` and the trace `tr`. -/
def weltB (b : Bool) (tr : List (Ereignis D1)) : World D1 :=
  { slots := fun _ _ _ => b
    globs := fun g => nomatch g
    spur := tr }

/-- `QEnsures P1` at `()` is the slot's current value. The return value and
    the parameter environment are both trivial (`none`/`[]`), so the contract
    reduces to the slot read. -/
theorem qensures_ist_slot (s : World D1) :
    Extraktion.QEnsures (D := D1) P1 () s ↔ s.slots () 0 () = true := by
  -- `D1.params ()` and `D1.erg ()` reduce definitionally to `[]`/`none`,
  -- so every `ergEnv`-wrapped environment IS the nil environment; the
  -- contract is the slot read, whose `wahr?` is the value itself.
  constructor
  · intro h
    have h1 := h () Env.nil
    -- `ergEnv` at `erg = none` reduces to the environment itself, and
    -- `eval` of the slot read against `Env.nil` IS the slot value.
    have hval : wahr? (eval (D := D1) s (P1.ensures ()) s
        (ergEnv (D := D1) (D1.erg ()) (() : ErgVal D1 (D1.erg ()))
          (Env.nil : Env D1 (D1.params ())))) = s.slots () 0 () := rfl
    rw [hval] at h1
    exact h1
  · intro h v r
    have hval : wahr? (eval (D := D1) s (P1.ensures ()) s
        (ergEnv (D := D1) (D1.erg ()) v r)) = s.slots () 0 () := rfl
    rw [hval, h]

/-- `QRequires P1` at `()` always holds (it is `.wahr`). -/
theorem qrequires_immer (s : World D1) :
    Extraktion.QRequires (D := D1) P1 () s := by
  intro r
  rfl

/-- Firing the writing leaf from a slot reading `b` writes `!b`.
    `O`/`passes`/`r` name the firing; `hs` fixes the incoming value. -/
theorem feuerung_schreibt (O : Orakel D1) (passes : Nat)
    (r : Env D1 []) (b : Bool)
    (s : World D1) (hs : s.slots () 0 () = b)
    (s' : World D1)
    (hstep : (execStmt O passes keinRuf writeLeaf s r).welt = some s') :
    s'.slots () 0 () = (!b) := by
  have h := (schreibt_wirkt_slot (D := D1) O passes V1 false [] []
    () () i0 negE rfl (fun w => nomatch w) s r).1
  -- `hstep` fires the same statement, so its outcome is the computed one.
  have hsame : (execStmt O passes keinRuf writeLeaf s r).welt =
      (execStmt O passes keinRuf
        ((.assignSlot () () i0 negE rfl (fun w => nomatch w) :
          Stmt D1 V1 false [] [] [])) s r).welt := rfl
  rw [hsame, h] at hstep
  -- The computed index is `0`; the computed value is the negated slot read.
  have hk_def : (eval (s.lese [] (i0.orte ++ negE.orte)) i0
    (s.lese [] (i0.orte ++ negE.orte)) r).n = 0 := rfl
  have hv_def : eval (s.lese [] (i0.orte ++ negE.orte)) negE
    (s.lese [] (i0.orte ++ negE.orte)) r =
    (!((s.lese [] (i0.orte ++ negE.orte)).slots () 0 ())) := rfl
  -- `World.lese` extends only the trace; slots ride along unchanged.
  have hlese : (s.lese [] (i0.orte ++ negE.orte)).slots () = s.slots () := rfl
  have hhit : ((s.lese [] (i0.orte ++ negE.orte)).schreibSlot () [] 0 () (!b)).slots
      () 0 () = (!b) :=
    storeSlot_hit ((s.lese [] (i0.orte ++ negE.orte)).storeSlot () 0 () (!b))
      () 0 () (!b)
  have hsym : s' =
      ((s.lese [] (i0.orte ++ negE.orte)).schreibSlot () []
        (eval (s.lese [] (i0.orte ++ negE.orte)) i0
          (s.lese [] (i0.orte ++ negE.orte)) r).n ()
        (eval (s.lese [] (i0.orte ++ negE.orte)) negE
          (s.lese [] (i0.orte ++ negE.orte)) r)) :=
    Option.some_inj.mp hstep.symm
  -- Every premise fires here: `hsym` fixes the outcome, `hk_def`/`hv_def`
  -- fix index and value, `hlese`/`hs` fix the incoming slot read.
  -- `schreibSlot` unfolds to `storeSlot` plus a trace note; the slot read
  -- then hits the stored value by `storeSlot_hit`.
  have hgoal : ((s.lese [] (i0.orte ++ negE.orte)).schreibSlot () [] 0 ()
      (eval (s.lese [] (i0.orte ++ negE.orte)) negE
        (s.lese [] (i0.orte ++ negE.orte)) r)).slots () 0 () = (!b) := by
    have hstore : ((s.lese [] (i0.orte ++ negE.orte)).storeSlot () 0 () (eval
        (s.lese [] (i0.orte ++ negE.orte)) negE
        (s.lese [] (i0.orte ++ negE.orte)) r)).slots () 0 () =
      eval (s.lese [] (i0.orte ++ negE.orte)) negE
        (s.lese [] (i0.orte ++ negE.orte)) r :=
      storeSlot_hit _ _ _ _ _
    -- `World.merke` rewrites only the trace field; the slot projection
    -- sees through it definitionally.
    have hmerke : (((s.lese [] (i0.orte ++ negE.orte)).storeSlot () 0 () (eval
        (s.lese [] (i0.orte ++ negE.orte)) negE
        (s.lese [] (i0.orte ++ negE.orte)) r)).merke
        [Ereignis.zugriff () true [] (s.lese [] (i0.orte ++ negE.orte)).haelt]).slots
        () 0 () =
      ((s.lese [] (i0.orte ++ negE.orte)).storeSlot () 0 () (eval
        (s.lese [] (i0.orte ++ negE.orte)) negE
        (s.lese [] (i0.orte ++ negE.orte)) r)).slots () 0 () := rfl
    have hval : eval (s.lese [] (i0.orte ++ negE.orte)) negE
        (s.lese [] (i0.orte ++ negE.orte)) r = (!b) := by
      rw [hv_def, hlese, hs]
    show (((s.lese [] (i0.orte ++ negE.orte)).storeSlot () 0 () _).merke _).slots
      () 0 () = (!b)
    rw [hmerke, hstore, hval]
  rw [hsym, hk_def]
  exact hgoal

/-- The `Post` half of `hBlattAll` fails for the writing leaf: from a `false`
    slot, `QEnsures` is false before the firing and true after it.
    `hb` is the seed fact, `O`/`passes`/`r` name the firing. -/
theorem hblatt_post_falsch (O : Orakel D1) (passes : Nat)
    (r : Env D1 []) (s : World D1)
    (hb : s.slots () 0 () = false) (s' : World D1)
    (hstep : (execStmt O passes keinRuf writeLeaf s r).welt = some s') :
    ¬ (Extraktion.QEnsures (D := D1) P1 () s ↔
      Extraktion.QEnsures (D := D1) P1 () s') := by
  have hvor : ¬ Extraktion.QEnsures (D := D1) P1 () s := by
    rw [qensures_ist_slot]
    simp [hb]
  have hnach : Extraktion.QEnsures (D := D1) P1 () s' := by
    rw [qensures_ist_slot]
    have hw := feuerung_schreibt O passes r false s hb s' hstep
    rw [hw]
    rfl
  intro hiff
  exact hvor (hiff.mpr hnach)

/-- The full per-firing conclusion (both `Pre` and `Post` iffs) is false for
    the writing leaf fired from a `false` slot. The `hAnd` premise carries the
    conjunction whose `Post` leg `hblatt_post_falsch` refutes. -/
theorem hblatt_konj_falsch (O : Orakel D1) (passes : Nat)
    (r : Env D1 []) (s : World D1)
    (hb : s.slots () 0 () = false) (s' : World D1)
    (hstep : (execStmt O passes keinRuf writeLeaf s r).welt = some s') :
    ¬ ((Extraktion.QRequires (D := D1) P1 () s ↔
        Extraktion.QRequires (D := D1) P1 () s') ∧
      (Extraktion.QEnsures (D := D1) P1 () s ↔
        Extraktion.QEnsures (D := D1) P1 () s')) := by
  intro hAnd
  exact hblatt_post_falsch O passes r s hb s' hstep hAnd.2

/-- The thread code is constantly `()`: the only function of `D1`. -/
def Jcode0 (_ : GenMaschine D1) : D1.Fn := ()

/-- **Counterexample to `hBlattAll` for writing leaves.** The goal theorem's
    `hBlattAll` premise (uniform per-firing preservation over every reachable
    intermediate machine) is false at `P1`/`O1`: the writing leaf `writeLeaf`,
    fired from a `false` slot, flips the thread's own `QEnsures`.

    The statement mirrors the `hBlattAll` shape with the thread code fixed to
    `Jcode0` (the only function of `D1`): `hReach` is the reachability wrapper
    (named but not discharged per step -- the firing fact holds at every
    machine, reachable or not), and `hstep`/`hneu`/`hkein` are the firing
    data. -/
theorem hblattall_falsch_schreibend :
    ¬ ∀ (M₀ : GenMaschine D1) (pc₀ : PCStand),
      PCReach P1 O1 0 (Extraktion.progAus P1 (fun _ => ()) [()] []) (GenStart (weltB false []).speicher) M₀ pc₀ →
      ∀ (V : Vertrag D1) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D1))
      (s : Stmt D1 V l Γ Λ Λ') (r : Env D1 Γ),
      s.istBlatt = true → HeldGenau Λ (offen (M₀.spuren 0)) →
      ∀ (s' : World D1) (neu : List (Ereignis D1)),
      (execStmt O1 0 keinRuf s (M₀.weltVon 0) r).welt = some s' →
      s'.spur = neu ++ M₀.spuren 0 →
      (∀ (L : D1.Lock) (h : List D1.Lock), Ereignis.nimmt L h ∉ neu) →
      (Extraktion.QRequires (D := D1) P1 (Jcode0 M₀) (M₀.weltVon 0) ↔
        Extraktion.QRequires (D := D1) P1 (Jcode0 M₀) s') ∧
      (Extraktion.QEnsures (D := D1) P1 (Jcode0 M₀) (M₀.weltVon 0) ↔
        Extraktion.QEnsures (D := D1) P1 (Jcode0 M₀) s') := by
  intro hAll
  -- The start machine: thread 0 sees the `false`-slot world with empty trace.
  have hWelt : ((GenStart (weltB false []).speicher).weltVon 0) = weltB false [] := rfl
  have hReach : PCReach P1 O1 0
      (Extraktion.progAus P1 (fun _ => ()) [()] [])
      (GenStart (weltB false []).speicher)
      (GenStart (weltB false []).speicher) (fun _ => 0) :=
    PCReach.start
  -- Instantiate at the start machine with the writing leaf and empty env.
  have hHeld : HeldGenau ([] : List (Res D1))
      (offen ((GenStart (weltB false []).speicher).spuren 0)) := by
    intro L
    exact nomatch L
  have hInst := hAll (GenStart (weltB false []).speicher) (fun _ => 0) hReach
    V1 false [] [] [] writeLeaf Env.nil rfl hHeld
  -- The `Jcode0` wrapper unfolds to `()`: the only function.
  have hJ : Jcode0 (GenStart (weltB false []).speicher) = () := rfl
  rw [hJ, hWelt] at hInst
  -- The firing: `execStmt` on the `false`-slot world yields some world.
  obtain ⟨s', hstep⟩ : ∃ s', (execStmt O1 0 keinRuf writeLeaf
      (weltB false []) Env.nil).welt = some s' := by
    have h := (schreibt_wirkt_slot (D := D1) O1 0 V1 false [] []
      () () i0 negE rfl (fun w => nomatch w) (weltB false []) Env.nil).1
    exact ⟨_, h⟩
  have hspur0 : ((GenStart (weltB false []).speicher).spuren 0) = [] := rfl
  have hspur : s'.spur = s'.spur ++ ((GenStart (weltB false []).speicher).spuren 0) := by
    rw [hspur0, List.append_nil]
  have hkein : ∀ (L : D1.Lock) (h : List D1.Lock),
      Ereignis.nimmt L h ∉ s'.spur := by
    intro L _
    exact nomatch L
  have hConc := hInst s' s'.spur hstep hspur hkein
  have hb : (weltB false []).slots () 0 () = false := rfl
  exact hblatt_konj_falsch O1 0 Env.nil _ hb s' hstep hConc

end Gabbro.Grammatik.BG

/-! CUTS: what is not proved.

  * The `J.code g` wrapper of the `hBlattAll` shape is mirrored here by the
    constant `Jcode0` (the only function of `D1`); the falsity is proved for
    that instantiation, not for an arbitrary `GemeinsamerLauf` code map.
  * The counterexample fires the leaf directly through `execStmt`, not through
    a full `PCReach` derivation ending in the firing machine: the firing fact
    holds at every machine (reachable or not), so reachability is named but
    not discharged per step.
  * `QRequires` survives the write (it is `.wahr`); only the `QEnsures` leg --
    and hence the conjunction -- is refuted. A contract pair where the write
    breaks `requires` too is not built here.
-/

#print axioms Gabbro.Grammatik.BG.hblattall_falsch_schreibend
#print axioms Gabbro.Grammatik.BG.hblatt_konj_falsch
#print axioms Gabbro.Grammatik.BG.hblatt_post_falsch
#print axioms Gabbro.Grammatik.BG.feuerung_schreibt
