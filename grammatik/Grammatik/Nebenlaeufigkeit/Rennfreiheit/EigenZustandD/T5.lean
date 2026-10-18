/- Part 5 of 5 of `EigenZustandD` (split by instrumente/teile/lean-teilen.py; the umbrella `EigenZustandD.lean` imports all parts). -/
import Grammatik.Nebenlaeufigkeit.Rennfreiheit.EigenZustandD.T4

namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik
variable {D : Deklaration}

namespace AxGegen

open Gabbro.Grammatik

/-- One table, one axiom that declares a write to the table. -/
def D2 : Deklaration where
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
  gtyp := fun e => (nomatch e)
  nutzlast := fun e => (nomatch e)
  atomar := fun e => (nomatch e)
  geteilt := fun _ => false
  ggeteilt := fun e => (nomatch e)
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => (nomatch e)
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
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
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

/-- Contract: writes the table. -/
def V2 : Vertrag D2 :=
  { schreibt := fun _ => true
    gschreibt := fun e => nomatch e
    erg := none
    gruende := 0
    haelt := []
    produziert := [] }

/-- Flipped world: the slot negated, the axiom's write event recorded (as the
    recording `GutO` demands), everything else kept. -/
def Wflip2 (σ : World D2) : World D2 :=
  { slots := fun _ _ _ => !(σ.slots () 0 ()), globs := fun g => (nomatch g),
    spur := axiomSpur [()] [] () [] σ.haelt ++ σ.spur }

/-- Oracle: flips the slot and records the write event. -/
def O2 : Orakel D2 where
  wirkt := fun _ σ _ => (Wflip2 σ, 0)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- The oracle is good: it writes only the declared (unguarded) table and
    records its write event over complete domains with the empty guard
    trace. The conditional antecedents hold vacuously (`D2` carriers are
    unguarded) and are not needed below. -/
theorem O2gut : GutO (D := D2) O2 := by
  intro a σ ρ
  cases a with
  | unit =>
      have hW : O2.wirkt () σ ρ = (Wflip2 σ, 0) := rfl
      rw [hW]
      refine ⟨?_, by rfl, ?_⟩
      · show (∀ (t : D2.Tab), D2.aschreibt () t = false → ∀ (k : Int) (f : D2.Feld t),
            (Wflip2 σ).slots t k f = σ.slots t k f) ∧
          (∀ (g : D2.Glob), D2.agschreibt () g = false →
            (Wflip2 σ).globs g = σ.globs g)
        exact ⟨fun t ht => absurd ht (by simp [D2]), fun g _ => nomatch g⟩
      · intro hgt hgg
        refine ⟨[()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro t _; cases t; exact List.Mem.head _
        · intro g; exact nomatch g
        · intro t _ w hw; simp [D2] at hw; cases hw
        · intro g; exact nomatch g
        · intro m st hm; simp at hm
        · intro L hL; simp at hL
        · rfl

/-- The axiom call statement (answer type `none`, so it is a `Stmt`).
    The new guard premises hold: `D2`'s table is UNGUARDED (`braucht = []`),
    so `darf` is vacuous at any `Λ` (this is exactly the case the lane-74
    repair does not cover); there are no globals. -/
def axCall : Stmt D2 V2 false [] [] [] :=
  .axiomCall (a := ()) (Args.nil (D := D2) (Γ := []) (Λ := [])) rfl
    (fun t _ => rfl) (fun g => nomatch g)
    (fun t _ w hw => by simp [D2] at hw; cases hw) (fun g => nomatch g)

/-- Firing the axiom call flips the slot. -/
theorem axFeuert (σ : World D2) (ρ : Env D2 [])
    (σ' : World D2)
    (hstep : (execStmt (O := O2) 0 keinRuf axCall σ ρ).welt = some σ') :
    σ'.slots () 0 () = !(σ.slots () 0 ()) := by
  have hcomp : (execStmt (O := O2) 0 keinRuf axCall σ ρ).welt =
      (match axiomAntwort (O := O2) () (σ.lese [] [])
        (evalArgs (Γ := []) (Λ := []) (σ.lese [] [])
          (Args.nil (D := D2) (Γ := []) (Λ := [])) (σ.lese [] []) ρ) with
      | (σ₂, Option.some _) => some σ₂
      | (_, Option.none) => none) := rfl
  rw [hcomp] at hstep
  -- The oracle answers `0` against answer type `none`: `some ()`.
  have hAns : axiomAntwort (O := O2) () (σ.lese [] [])
      (evalArgs (Γ := []) (Λ := []) (σ.lese [] [])
        (Args.nil (D := D2) (Γ := []) (Λ := [])) (σ.lese [] []) ρ) =
      (Wflip2 (σ.lese [] []), Option.some ()) := by
    rfl
  rw [hAns] at hstep
  simp only [Option.some.injEq] at hstep
  subst hstep
  -- `Wflip2` flips the slot; `lese` keeps slots by `rfl`.
  show (Wflip2 (σ.lese [] [])).slots () 0 () = _
  have hlese : (σ.lese [] []).slots () 0 () = σ.slots () 0 () := rfl
  show (!(σ.lese [] []).slots () 0 ()) = _
  rw [hlese]

/-- Start memory for the counterexample: slot `false`. -/
def wspF : Speicher D2 := ⟨fun _ _ _ => false, fun g => (nomatch g)⟩

/-- Program texts: every thread holds the carrier-free atom. -/
def progF : PCProg D2 := fun _ => [PCAtom.leaf [] []]

/-- Any program: bodies never fire here (only the axiom step matters). -/
def P2w : Programm D2 where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => .ret .empty (List.Perm.refl [])

/-- `hNurG` for the counterexample program: all atoms are carrier-free. -/
theorem hNurF : ∀ h : Faden, h ≠ (0 : Faden) → ∀ a ∈ progF h,
    (Sum.inl () : D2.Tab ⊕ D2.Glob) ∉ PCAtom.carriers a := by
  intro h _ a ha
  simp only [progF] at ha
  simp only [List.mem_singleton] at ha
  subst ha
  simp [PCAtom.carriers]


/- REMOVED (lane 80): `axNeu_kein_schrieb` and `axiomCall_ohne_ereignis_falsch`
    are false under the recording `GutO` -- the oracle now records its write
    event (`O2gut`), so the recorded list DOES carry a `Sum.inl ()` event and
    the target-as-stated is no longer refuted at `Stmt.axiomCall`. The lane-80
    target (`EigenZustand.lean`) proves the original statement; the `AxGegen`
    fixture (`D2`/`V2`/`O2`/`axCall`/`axFeuert`/`wspF`/`progF`/`P2w`/`hNurF`)
    is kept for its second witness. -/

end AxGegen
/-! ## 15. Reference-fixture witnesses (merge-gate inhabitation).

  The merge gate owes `pcSchritt_fremd_fest_zeuge` (the `hNoAx` premise
  quantifies over `Vertrag`/`Stmt`) and a witness for
  `eigenzustand_nur_eigene_schritteD_rep`. Both are built on the reference
  fixture (`ReferenzB`): `refD` declares no axiom, so `hNoAx` is provable
  (vacuous over the empty `Ax`); the witnessed foreign step is thread `0`
  firing `leave` (memory-preserving, carrier-free atom) from a machine whose
  thread-0 trace is empty. Non-degeneracy comes from the fixture itself:
  `refEin` writes `konto`, and `refB_pc_erreicht`/`refB_pc_schreibt` exhibit
  a reached run whose write moves memory. -/

/-- Joint witness for `pcSchritt_fremd_fest` (rule 13): all premises
    instantiated together on `refD` -- the foreign `leave` step by thread
    `0 ≠ 1` from the reached machine `refPC2`, `hNurG` by `ezdProg_nurG`,
    `hNoAx` vacuous over the empty `Ax` (provable here, as the reviewer
    asked to check) -- plus the conclusion proved by the theorem itself
    and the non-degeneracy evidence (`refEin` writes `konto`; the
    `refB_prog` run reaches `refPC2` with a memory-changing write). -/
theorem pcSchritt_fremd_fest_zeuge :
    ∃ (P : Programm refD) (O : Orakel refD) (passes : Nat) (hO : GutO O)
      (prog : PCProg refD) (M : GenMaschine refD) (pc : PCStand) (h : Faden)
      (M' : GenMaschine refD) (pc' : PCStand) (g : Faden) (t : refD.Tab)
      (hs : PCSchritt P O passes prog M pc h M' pc')
      (hOg : h ≠ g)
      (hNurG : ∀ a ∈ prog h,
        (Sum.inl t : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a)
      (hNoAx : ∀ (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
        (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
        (σ' : World refD) (neu : List (Ereignis refD))
        (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
        (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
        (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
        ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
          (hh : refD.aerg a = none)
          (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
          (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
          (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
          (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
          (execStmt O passes keinRuf
            (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
            (M.weltVon h) ρ).welt = some σ' ∧ refD.aschreibt a t = true)
      (k : Int) (f : refD.Feld t),
      M'.speicher.slots t k f = M.speicher.slots t k f ∧
      (∃ fn : refD.Fn, (vertragVon refD fn).schreibt t = true) ∧
      (∃ (prog2 : PCProg refD) (M2 : GenMaschine refD) (pc2 : PCStand),
        PCReach P O passes prog2 (GenStart refSp0) M2 pc2 ∧
        M2.speicher.slots t 0 () ≠ refSp0.slots t 0 ()) := by
  have hs0 : PCSchritt (P := refP) (O := refO) 0 ezdProg refPC2 (fun _ => 0) 0
      ⟨(refPC2.weltVon 0).speicher, genUpdate refPC2.spuren 0 (refPC2.weltVon 0).spur,
        refPC2.lauf ++ genEigen 0 [], refPC2.start,
        refPC2.welten ++ [(refPC2.weltVon 0)], refPC2.tiefe + 1⟩
      (pcAdvance (fun _ => 0) 0) :=
    ezdLeave_step refPC2 rfl
  have hNurG0 : ∀ a ∈ ezdProg 0,
      (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a :=
    fun a ha => ezdProg_nurG 0 a ha
  have hNoAx0 : ∀ (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
      (σ' : World refD) (neu : List (Ereignis refD))
      (hstep : (execStmt refO 0 keinRuf s (refPC2.weltVon 0) ρ).welt = some σ')
      (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
      (hpc : (ezdProg 0)[(fun _ : Faden => 0) 0]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
        (hh : refD.aerg a = none)
        (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
        (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
        (execStmt refO 0 keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (refPC2.weltVon 0) ρ).welt = some σ' ∧ refD.aschreibt a () = true := by
    intro V l Γ Λ Λ' s ρ σ' neu hstep Λa cs hpc hEx
    obtain ⟨a, _, _, _, _, _, _, _, _⟩ := hEx
    exact nomatch a
  refine ⟨refP, refO, 0, refO_gut, ezdProg, refPC2, fun _ => 0, 0, _, _,
    1, (), hs0, by decide, hNurG0, hNoAx0, 0, (), ?_, ?_, ?_⟩
  · exact pcSchritt_fremd_fest refP refO refO_gut 0 ezdProg refPC2 (fun _ => 0) 0 _ _
      1 () hs0 (by decide) hNurG0 hNoAx0 0 ()
  · exact ⟨refEin, refEin_schreibt ()⟩
  · exact ⟨refB_prog, refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩


/-! CUTS: what is not proved.

  * (lane 80) The TARGET AS STATED (`eigenzustand_nur_eigene_schritte`, no
    remainder) is now PROVED in `EigenZustand.lean` (the recording `GutO`
    discharges the old `hNoAx` remainder: an oracle write records its event).
    The `AxGegen` counterexample (`axiomCall_ohne_ereignis_falsch`) and its
    `axNeu_kein_schrieb` lemma were false under the recording `GutO` and are
    removed; the `AxGegen` fixture is kept for the lane-80 second witness.
  * The positive result here stays the separately named
    `eigenzustand_nur_eigene_schritteD_rep` with the explicit open remainder
    `hNoAx` (rule 12): no declared oracle write to `t` fires at the foreign
    step. `hNoAx` is not quantified over contracts or
    statements (rule 13): it quantifies over this step's own firing data.
  * `hNoAx` is discharged in the witnesses only because the fixture declares
    no axiom (`refD.Ax` is empty, so the oracle-write existential is absurd
    by `nomatch`; previously the same was shown on `BG.D1` via `wNoAx`).
    For programs with axioms writing `t`, it stays owed per step.
  * `blattSlots_dispatch`'s third arm (declared oracle write) is the same remainder
    in disjunctive form; the merge gate's `ZEUGE` line names the exact target, whose
    `_zeuge` cannot exist (premises contradictory at `axiomCall`) -- the joint
    witnesses are proved for the repaired theorem instead
    (`eigenzustand_nur_eigene_schritteD_rep_zeuge`) and for the step lemma
    (`pcSchritt_fremd_fest_zeuge`), both on the reference fixture (`refD`):
    non-degeneracy comes from the fixture (`refEin` writes `konto`; the
    `refB_prog` run reaches `refPC2` with a memory-changing write). The
    wave-3 `BG.D1` witness of the same `rep_zeuge` name was superseded by the
    `refD` version per reviewer direction; its helpers (`wStep1`, `wStep2`,
    `wM1`, `wNoAx`, …) stay as proved facts.
  * No premise of any added theorem has type `Prop` itself; every premise is used
    by its proof (take/rel branches of `pcSchritt_fremd_fest` close by `rfl`,
    using no hypotheses -- the premises are consumed in the leaf branch).
-/

#print axioms Gabbro.Grammatik.EZD.eigenzustand_nur_eigene_schritteD_rep
#print axioms Gabbro.Grammatik.EZD.eigenzustand_nur_eigene_schritteD_rep_zeuge
#print axioms Gabbro.Grammatik.EZD.blattSlots_dispatch
#print axioms Gabbro.Grammatik.EZD.pcSchritt_fremd_fest
#print axioms Gabbro.Grammatik.EZD.pcSchritt_fremd_fest_zeuge


end Gabbro.Grammatik.EZD
