/-
  File:      Grammatik/ZielOrtRegister.lean
  Subject:   WHY REGISTER READS ARE NOT IN THE FRAGMENT OF `ziel_ort_voll` --
             the statement of `ziel_ort_voll` with register reads admitted
             is false, on a two-thread program.

  The sequential semantics reads a register as `O.regLies r σ`, a function
  of the reader's world: two reads at the same world give the same answer.
  So the body

      leser: if true { let x = R; let y = R; return x == y }; return true

  satisfies `ensures result` for EVERY oracle (`KoerperGutV`). On G the
  reader's world between the two reads changes when another thread writes
  memory -- here a table the reader never reads, outside its footprint --
  and a `GutO` oracle may read that memory (`GutO` constrains axiom
  answers only). With the register reading the table, thread 1 writing it
  between thread 0's two reads makes `leser` return `false`.

  Every other premise of `ziel_ort_voll` holds (`rP_praemissen`); the
  program is in the fragment widened by the register forms
  (`programmImFragmentR`); a reached machine violates `VertragAmOrtG`
  (`rLauf`). Hence the statement quantified over all programs of the
  widened fragment is false (`ziel_ort_register_falsch`).

  What premise would repair it: "register (and visibility) answers do not
  depend on memory outside the reader's footprint" -- a statement about the
  oracle RELATIVE TO A PROGRAM's footprint. It is neither a user obligation,
  nor a program-independent hardware assumption, nor a decidable program
  fact; the extension stops here. (A program-independent alternative,
  "register answers do not depend on memory at all", would exclude every
  memory-mapped device.)
-/
import Grammatik.ZielOrtVollZeuge
import Grammatik.ZielOrtZeuge

namespace Gabbro.Grammatik

/-! ## 1. The fragment widened by the register forms -/

mutual

/-- `vOk K` with the register and visibility forms admitted. -/
def Stmt.rOk {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (K : Nat → Bool) : Stmt D V l Γ Λ Λ' → Bool
  | .ite _ t e => t.rOk K && e.rOk K
  | .onOption _ p a => p.rOk K && a.rOk K
  | .onTag _ arms => arms.rOk K
  | .onGrund _ arms => arms.rOk K
  | .locks _ _ body => body.rOk K
  | .breaking _ body => body.rOk K
  | .traverse _ _ body => body.rOk K
  | .retry _ _ body ueber => body.rOk K && ueber.rOk K
  | .forever _ _ body => body.rOk K
  | .callInd (n := n) .. => K n
  | _ => true

def Block.rOk {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (K : Nat → Bool) : Block D V l Γ Λ Λ' → Bool
  | .nil => true
  | .cons s rest => s.rOk K && rest.rOk K
  | .bind _ rest => rest.rOk K
  | .bindCall _ _ _ _ _ rest => rest.rOk K
  | .bindCallInd (n := n) _ _ _ _ _ rest => K n && rest.rOk K
  | .bindCallElse _ _ _ _ _ err rest => err.rOk K && rest.rOk K
  | .bindAxiom _ _ _ _ _ _ _ rest => rest.rOk K
  | .regLies _ _ rest => rest.rOk K
  | .regLiesElse _ _ _ sonst rest => sonst.rOk K && rest.rOk K
  | .awaits _ _ _ _ rest => rest.rOk K
  | .exchange _ _ _ _ rest => rest.rOk K
  | .narrow _ _ _ sonst rest => sonst.rOk K && rest.rOk K
  | .pruefung _ sonst rest => sonst.rOk K && rest.rOk K
  | .gleit _ _ _ _ _ rest => rest.rOk K
  | .gleitLit _ _ _ rest => rest.rOk K
  | .gleitVon _ _ _ rest => rest.rOk K
  | .gleitNarrow _ _ _ sonst rest => sonst.rOk K && rest.rOk K

def Endblock.rOk {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (K : Nat → Bool) : Endblock D V l Γ Λ → Bool
  | .ret .. => true
  | .retGrund .. => true
  | .leave .. => true
  | .next .. => true
  | .cons s rest => s.rOk K && rest.rOk K
  | .bind _ rest => rest.rOk K

def Arms.rOk {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (K : Nat → Bool) : Arms D V l Γ Λ Λ' cs → Bool
  | .nil => true
  | .cons b rest => b.rOk K && rest.rOk K

def GrundArms.rOk {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (K : Nat → Bool) : GrundArms D V l Γ Λ Λ' n → Bool
  | .nil => true
  | .cons b rest => b.rOk K && rest.rOk K

end

/-- The decided fragment of `ziel_ort_voll`, widened by register reads and
    `awaits`. -/
def programmImFragmentR {D : Deklaration} (P : Programm D) (fs : List D.Fn) : Bool :=
  fs.all fun f => (P.rumpf f).rOk (kandB P fs (fussOrte P f))

/-! ## 2. The declaration and the program -/

inductive RFn where
  | haupt
  | leser
  | schreiber
  deriving DecidableEq

def rSigHaupt : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def rSigLeser : Signatur Unit Empty Unit Empty where
  params := []
  erg := some .bool
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

def rSigSchreiber : Signatur Unit Empty Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := [()]
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- One guarded table (one slot of `0 .. 1`), one lock, one readable
    register of `0 .. 1`, no axiom, three functions. -/
def rD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
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
  Fn := RFn
  sig := fun | .haupt => 0 | .leser => 1 | .schreiber => 2
  sigNr := fun | 0 => rSigHaupt | 1 => rSigLeser | _ => rSigSchreiber
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Unit
  rtyp := fun _ => .int 0 1
  rklasse := fun _ => .r
  spiegel := fun _ => none
  rzusage := fun _ _ => true
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t _ => by decide
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

def rHaupt : rD.Fn := RFn.haupt
def rLeser : rD.Fn := RFn.leser
def rSchreiber : rD.Fn := RFn.schreiber

abbrev rL : List (Res rD) := [Res.held (D := rD) ()]

theorem rDarf : darf rD () rL := by
  intro w h
  have e : w = Sum.inl () := List.mem_singleton.mp h
  subst e
  exact List.mem_singleton.mpr rfl

theorem rHpLeser : RufPasst rD (vertragVon rD rHaupt) (rD.signatur rLeser) [] where
  hw := fun t h => by cases t; exact absurd h (by decide)
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := RufPasst.hh_von (fun L => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)
  hx := RufPasst.hx_von (fun L => ⟨(fun h => nomatch h), (fun h => nomatch h)⟩)

/-- `R; R; return x == y` inside `if true`. -/
def rLesBlock : Block rD (vertragVon rD rLeser) false [] [] [] :=
  .regLies () rfl (.regLies () rfl
    (.cons (.ret (.wert (.eq (.var (.dort .hier)) (.var .hier))) List.Perm.nil) .nil))

def rRumpfLeser : Endblock rD (vertragVon rD rLeser) false [] [] :=
  .cons (.ite .wahr rLesBlock .nil) (.ret (.wert .wahr) List.Perm.nil)

def rRumpfHaupt : Endblock rD (vertragVon rD rHaupt) false [] [] :=
  .cons (.call rLeser .nil rHpLeser rfl) (.ret .keine List.Perm.nil)

def rIdx {Γ : Ctx} {Λ : List (Res rD)} : Expr rD Γ Λ (.index (rD.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

def rEins {Γ : Ctx} {Λ : List (Res rD)} : Expr rD Γ Λ (.int 0 1) :=
  .weiter (by decide) (by decide) (.lit 1)

/-- `schreiber` (holds the lock): `t[0] := 1; return`. -/
def rRumpfSchreiber : Endblock rD (vertragVon rD rSchreiber) false [] rL :=
  .cons (.assignSlot () () rIdx rEins rfl rDarf) (.ret .keine (by rfl))

/-- The program: `ensures result` for `leser`, `true` elsewhere. -/
def rP : Programm rD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .haupt => .wahr
    | .leser => .var .hier
    | .schreiber => .wahr
  rumpf
    | .haupt => rRumpfHaupt
    | .leser => rRumpfLeser
    | .schreiber => rRumpfSchreiber

def rFs : List rD.Fn := [rHaupt, rLeser, rSchreiber]

theorem rFs_voll : ∀ g : rD.Fn, g ∈ rFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem rP_fragmentR : programmImFragmentR rP rFs = true := by decide

/-- The register reads are exactly what keeps `rP` out of the fragment of
    `ziel_ort_voll`. -/
theorem rP_nicht_fragmentV : programmImFragmentV rP rFs = false := by decide

theorem rP_fuss : fussOrtB rP rFs = true := by decide

/-! ## 3. Oracle, start, and the user obligations -/

/-- The oracle: no axioms; the register answers the table's slot. -/
def rO : Orakel rD where
  wirkt := fun a => nomatch a
  regLies := fun _ σ => (σ.slots () 0 ()).n
  regSchreib := fun _ _ => ()
  sichtbar := fun g => nomatch g

theorem rO_gut : GutO rO := fun a => nomatch a

def rSp : Speicher rD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

/-- Thread 1 starts in `schreiber` (holding the lock), every other thread in
    `haupt`. -/
def rInit : Faden → Σ f : rD.Fn, Env rD (rD.params f) :=
  fun t => if t = 1 then ⟨rSchreiber, .nil⟩ else ⟨rHaupt, .nil⟩

theorem rP_start : StartGut rP rSp rInit := by
  intro t
  unfold rInit
  by_cases h : t = 1
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

theorem rInit_exklusiv : StartExklusiv (D := rD) rInit := by
  intro f g hfg L hf hg
  unfold rInit at hf hg
  by_cases h1 : f = 1
  · have h2 : g ≠ 1 := fun e => hfg (h1.trans e.symm)
    rw [if_neg h2] at hg
    exact nomatch hg
  · rw [if_neg h1] at hf
    exact nomatch hf

/-- What `leser`'s body does for ANY oracle and handler: a return of `true`
    or a hardware outcome (a register answer outside its type). -/
theorem rZusage (v : Wert rD (rD.rtyp ())) : rD.rzusage () v = true := rfl

theorem rLeser_lauf (O' : Orakel rD) (passes : Nat)
    (R : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → RufAusgang f) (σ : World rD)
    (ρ : Env rD (rD.params rLeser)) :
    (∃ σ', execEnd O' passes R (rP.rumpf rLeser) σ ρ = .zurueck σ' true) ∨
      ∃ e, execEnd O' passes R (rP.rumpf rLeser) σ ρ = .hardware e := by
  show (∃ σ', execEnd O' passes R rRumpfLeser σ ρ = .zurueck σ' true) ∨
    ∃ e, execEnd O' passes R rRumpfLeser σ ρ = .hardware e
  simp only [rRumpfLeser, rLesBlock, execEnd, execStmt, execBlock, if_true, rZusage]
  cases hv : einpassen O'.zeiger (rD.rtyp ()) (O'.regLies () (σ.lese [] (Expr.wahr : Expr rD [] [] .bool).orte)) with
  | none =>
      right
      exact ⟨_, rfl⟩
  | some v =>
      left
      refine ⟨(σ.lese [] []).lese [] [], ?_⟩
      simp only [Ausgang.schrumpf, evalErg, eval, wahr?, if_true]
      show EndAusgang.zurueck (V := vertragVon rD rLeser) (l := false) (Γ := [])
        ((σ.lese [] []).lese [] []) (decide (v.n = v.n)) = _
      rw [decide_eq_true rfl]

theorem rP_koerper_leser : KoerperGutV rP 0 rLeser := by
  intro O' _ R _ _ σ ρ _
  have hr : rP.rumpf rLeser = rRumpfLeser := rfl
  refine ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩
  · rcases rLeser_lauf O' 0 R σ ρ with ⟨σ'', h⟩ | ⟨e, h⟩
    · rw [h] at hrun
      cases hrun
      rfl
    · rw [h] at hrun
      cases hrun
  · rcases rLeser_lauf O' 0 (torRuf rP R) σ ρ with ⟨σ'', h⟩ | ⟨e, h⟩
    · rw [h] at hrun
      cases hrun
    · rw [h] at hrun
      cases hrun

theorem rP_koerper_schreiber : KoerperGutV rP 0 rSchreiber := by
  intro O' _ R _ _ σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : rP.rumpf rSchreiber = rRumpfSchreiber := rfl
  rw [hr] at hrun
  simp only [rRumpfSchreiber, execEnd, execStmt] at hrun
  cases hrun

theorem rP_koerper_haupt : KoerperGutV rP 0 rHaupt := by
  intro O' _ R _ hOV σ ρ _
  refine ⟨fun _ _ _ => rfl, fun g hrun => ?_⟩
  have hr : rP.rumpf rHaupt = rRumpfHaupt := rfl
  rw [hr] at hrun
  rcases execEnd_cons_logikV _ _ _ _ _ _ _ _ hrun with h1 | ⟨σ1, ρ1, _, h1⟩
  · have ht : ∀ σ1 ρ1, torRuf rP R rLeser σ1 ρ1 = R rLeser σ1 ρ1 := fun _ _ => if_pos rfl
    simp only [execStmt, ht] at h1
    split at h1
    · cases h1
    · rename_i r _
      exact nomatch r
    · rename_i e hR
      cases h1
      exact hOV _ _ _ _ hR g rfl
    · cases h1
  · simp only [execEnd] at h1
    cases h1

theorem rP_koerper : ∀ f, KoerperGutV rP 0 f := by
  intro f
  cases f
  · exact rP_koerper_haupt
  · exact rP_koerper_leser
  · exact rP_koerper_schreiber

/-! ## 4. The run -/

def rZ0 : RufFadenG rD :=
  ⟨[], ⟨rHaupt, .nil, rSp.welt [], ⟨false, [], [], .nil, .ende rRumpfHaupt⟩⟩, [],
    [RufEreignisF.eintritt rHaupt .nil (rSp.welt [])]⟩

def rZ1 : RufFadenG rD :=
  ⟨[], ⟨rSchreiber, .nil, rSp.welt [], ⟨false, [], rL, .nil, .ende rRumpfSchreiber⟩⟩,
    startSpur rSchreiber, [RufEreignisF.eintritt rSchreiber .nil (rSp.welt [])]⟩

theorem rM0_faden0 : (RufStartG rP rSp rInit).faeden 0 = rZ0 := rfl

theorem rM0_faden1 : (RufStartG rP rSp rInit).faeden 1 = rZ1 := rfl

theorem rHg0 {s : List (Ereignis rD)} (h : offen s = []) :
    HeldGenau ([] : List (Res rD)) (offen s) := by
  rw [h]
  intro L
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem rHgL {s : List (Ereignis rD)} (h : offen s = [()]) : HeldGenau rL (offen s) := by
  rw [h]
  intro L
  cases L
  exact ⟨fun _ => List.mem_cons_self, fun _ => List.mem_cons_self⟩

theorem rOffen_weltVon (M : RufMaschineG rD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := rfl

theorem rHoff_e {M : RufMaschineG rD} {f : Faden} {z : RufFadenG rD} {x : List rD.Lock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

def rNull : Wert rD (.int 0 1) := ⟨0, by decide, by decide⟩
def rEinsW : Wert rD (.int 0 1) := ⟨1, by decide, by decide⟩

/-- **The run.** Thread 0 calls `leser`, unfolds its `if`, reads the
    register (`0`); thread 1 writes the table's slot to `1` under its
    signature lock; thread 0 reads the register again (`1`) and returns
    `0 == 1`, i.e. `false`: its log ends in a return of `leser` whose
    `ensures result` is false. -/
theorem rLauf : ∃ M : RufMaschineG rD,
    RufErreichbarG rP rO 0 (RufStartG rP rSp rInit) M ∧
    ∃ (rho : Env rD (rD.params rLeser)) (v : ErgVal rD (rD.erg rLeser)) (s0 s1 : World rD),
      RufEreignisF.rueck rLeser rho v s0 s1 ∈ (M.faeden 0).log ∧
      ¬ EnsAmRueck rP rLeser s0 s1 rho v := by
  have h0 := rM0_faden0
  have hoff0 : offen ((RufStartG rP rSp rInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := rP) (O := rO) (passes := 0) h0 rLeser .nil rHpLeser rfl
    (.ret .keine List.Perm.nil) .nil rfl (rHg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen, rOffen_weltVon]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := rP) (O := rO) (passes := 0) e1
    (.ite .wahr rLesBlock .nil) (.ret (.wert .wahr) List.Perm.nil) .nil rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur, rOffen_weltVon]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  obtain ⟨M3, s3, hZ3⟩ := w_iteWahr (P := rP) (O := rO) (passes := 0) e2 .wahr rLesBlock .nil
    .nil (.ende (.ret (.wert .wahr) List.Perm.nil)) .nil rfl rfl (rHg0 (rHoff_e e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, rOffen_weltVon]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  have hsp3 : M3.speicher = rSp := by
    rw [hZ3.2]
    show M2.speicher = rSp
    rw [hZ2.2]
    show M1.speicher = rSp
    rw [hZ1.2]
    rfl
  -- first read: 0
  obtain ⟨M4, s4, hZ4⟩ := w_regLies (P := rP) (O := rO) (passes := 0) e3 () rfl _ _ .nil rfl rNull
    (by show einpassen rO.zeiger (.int 0 1) ((M3.speicher.slots () 0 ()).n) = some rNull
        rw [hsp3]; rfl)
    rfl (rHg0 (rHoff_e e3 hoff3)).heldIn
  have e4 := hZ4.1
  try dsimp only at e4
  -- thread 1 writes the slot
  have h41 : M4.faeden 1 = rZ1 := by
    rw [rufSchrittG_fremd s4 1 (by decide), rufSchrittG_fremd s3 1 (by decide),
      rufSchrittG_fremd s2 1 (by decide), rufSchrittG_fremd s1 1 (by decide), rM0_faden1]
  obtain ⟨M5, s5, hZ5⟩ := w_blatt (P := rP) (O := rO) (passes := 0) h41
    (.assignSlot () () rIdx rEins rfl rDarf) (.ret .keine (by rfl)) .nil rfl rfl (rHgL rfl).heldIn _ _
    (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have h50 : M5.faeden 0 = M4.faeden 0 := rufSchrittG_fremd s5 0 (by decide)
  have hsp5 : (M5.speicher.slots () 0 ()).n = 1 := by
    rw [hZ5.2]
    rfl
  have e4' : M5.faeden 0 = _ := h50.trans e4
  -- second read: 1
  obtain ⟨M6, s6, hZ6⟩ := w_regLies (P := rP) (O := rO) (passes := 0) e4' () rfl _ _ _ rfl rEinsW
    (by show einpassen rO.zeiger (.int 0 1) ((M5.speicher.slots () 0 ()).n) = some rEinsW
        rw [hsp5]; rfl)
    rfl (rHg0 (rHoff_e e4' (by rw [h50, hZ4.spur, rOffen_weltVon]; exact hoff3))).heldIn
  have e6 := hZ6.1
  try dsimp only at e6
  have hoff6 : offen (M6.faeden 0).spur = [] := by
    rw [hZ6.spur, rOffen_weltVon, h50, hZ4.spur, rOffen_weltVon]; exact hoff3
  -- return `x == y`, which is `false`
  obtain ⟨M7, s7, hG7⟩ := w_dannRetP (P := rP) (O := rO) (passes := 0) e6 _ _ rfl
    (PopArt.wie rfl) _ List.Perm.nil .nil _ _ rfl (rHg0 (rHoff_e e6 hoff6)).heldIn
  refine ⟨M7, .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
    (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7, _, _, _, _,
    by rw [hG7.1]; exact List.mem_cons_self, ?_⟩
  intro hE
  have h' : wahr? (decide ((0 : Int) = 1)) = true := hE
  exact absurd h' (by decide)

/-! ## 5. The statement with register reads admitted is false -/

/-- **`ziel_ort_voll` does not extend to register reads.** Quantified over
    every declaration, program, oracle, `forever` budget, complete member
    list, start memory, start assignment and event, the statement of
    `ziel_ort_voll` with its fragment widened by the register forms
    (`programmImFragmentR`) is false: `rP` satisfies every premise and a
    reachable machine violates `VertragAmOrtG`. -/
theorem ziel_ort_register_falsch :
    ¬ (∀ (D : Deklaration) (P : Programm D) (O : Orakel D) (passes : Nat) (fs : List D.Fn)
        (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) (_e0 : Ereignis D),
        GutO O → (∀ g : D.Fn, g ∈ fs) → programmImFragmentR P fs = true →
        fussOrtB P fs = true → (∀ f : D.Fn, KoerperGutV P passes f) → StartGut P sp init →
        StartExklusiv init →
        ∀ M : RufMaschineG D, RufErreichbarG P O passes (RufStartG P sp init) M →
          VertragAmOrtG P M) := by
  intro h
  obtain ⟨M, hr, rho, v, s0, s1, hmem, hens⟩ := rLauf
  exact hens ((h rD rP rO 0 rFs rSp rInit (.gibt ()) rO_gut rFs_voll rP_fragmentR rP_fuss
    rP_koerper rP_start rInit_exklusiv M hr 0 _ hmem).2 _ _ _ _ _ rfl)

/-- All premises of `ziel_ort_voll` but the fragment hold on `rP`, which is
    in the widened fragment and not in the fragment of `ziel_ort_voll`. -/
theorem rP_praemissen :
    GutO rO ∧ (∀ g : rD.Fn, g ∈ rFs) ∧ programmImFragmentR rP rFs = true ∧
    programmImFragmentV rP rFs = false ∧ fussOrtB rP rFs = true ∧
    (∀ f : rD.Fn, KoerperGutV rP 0 f) ∧ StartGut rP rSp rInit ∧
    StartExklusiv (D := rD) rInit :=
  ⟨rO_gut, rFs_voll, rP_fragmentR, rP_nicht_fragmentV, rP_fuss, rP_koerper, rP_start,
    rInit_exklusiv⟩

/-! ## CUTS:

  What is proved: the statement of `ziel_ort_voll` with register reads
  admitted is false (`ziel_ort_register_falsch`), on a program satisfying
  every other premise (`rP_praemissen`) with a reached violating machine
  (`rLauf`). The same shape refutes `awaits` (its visibility answer
  `O.sichtbar g σ` is a function of the world as well); not built.

  What is NOT proved: a repair. The premise that would make register reads
  sound is a property of the oracle relative to a program's footprint (see
  the header); by the task's rule the extension stops there.
  The repair that followed splits that property into a program-independent
  hardware class and a decidable program fact: `RegLokal` (a register
  answers from the carriers the declaration attributes to its device,
  `Deklaration.rtraeger`) and the widened footprint check `fussOrtGB` (the
  reader's footprint contains those carriers). `ziel_ort_geraet`
  (`ZielOrtGeraet.lean`) proves the theorem with register reads under them;
  `ziel_ort_register_ausgeschlossen` (`ZielOrtGeraetAus.lean`) shows that
  THIS counterexample fails exactly `RegLokal`.
-/

#print axioms Gabbro.Grammatik.rP_koerper
#print axioms Gabbro.Grammatik.rLauf
#print axioms Gabbro.Grammatik.ziel_ort_register_falsch
#print axioms Gabbro.Grammatik.rP_praemissen

end Gabbro.Grammatik
