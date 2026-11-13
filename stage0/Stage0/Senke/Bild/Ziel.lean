/-
  File:      stage0/Stage0/Senke/Bild/Ziel.lean
  Subject:   The goal legs at the machines G that the image corresponds to (image theorem, piece T1, one thread).
             What is proved is NOT a property of the image's states themselves: for an image state reached by a
             memory-only run, it is `Korrespondenz` (or `Rand`) of that state with a machine `M'` of machine G, and
             `Ziel` of that machine `M'`. Every machine the correspondence names is reached from the start machine
             by steps of the image's thread (`rufErreichbar_lauf`), so `ziel_aus` — the generic form of the goal
             theorem over machine G of the program `P` (not `P.mitRuhe`), under the checker's facts (a′), the user's
             logic (b), the hardware assumptions (c) and the admissible start (d′) — gives every leg of `Ziel` at
             `M'` (`bild_ziel_seq`). From the image's first body boundary, the named premise `StartEntspricht`
             (piece T2) replaces the reachability premise (`bild_ziel_start`). `ls`, the lock enumeration, appears
             in no other premise: `ziel_aus` uses it for the deadlock leg (`keine_verklemmungG`), so it is an
             explicit argument.
-/
module
public import Stage0.Senke.Bild.Korrespondenz
public import Grammatik.Zielsatz.Kern.Beweis
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- Steps of one thread continue a reachable machine to a reachable machine. -/
theorem rufErreichbar_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {M0 M M' : RufMaschineG D}
    {thr : Faden} (hl : RufLaufG P O passes thr M M') :
    RufErreichbarG P O passes M0 M → RufErreichbarG P O passes M0 M' := by
  induction hl with
  | refl => exact id
  | schritt hs _ ih => exact fun h => ih (RufErreichbarG.schritt _ _ thr h hs)

variable [Kern]

/-- **The named start premise of T1** (`StartEntspricht`; proving it from the image's start code is piece T2): the
    image stands in front of the first statement of the body of `B.f`, behind its prologue, and corresponds there
    to the start machine of G — thread `thr` runs its root frame (no caller) with the residue `.ende (B.P.rumpf B.f)`,
    the entry environment `rho` and the world `σ` that the image holds in memory. -/
def StartEntspricht (B : BodyFrame D) (sp : Speicher D) (init : Faden → Σ g : D.Fn, Env D (D.params g))
    (thr : Faden) (rho : Env D (D.params B.f)) (Agl : D.Lock → Prop) (pc : Runner.W) (m : Runner.Mem)
    (σ : World D) : Prop :=
  Rand B thr [] rho (sp.welt []) Agl (B.P.rumpf B.f) pc m (RufStartG B.P sp init) σ rho

/-- **`Ziel` at the machines G the sequential image corresponds to (T1)**. Under the checker's facts (a′), the
    user's logic (b), the named hardware assumptions (c) and an admissible start (d′) of machine G of `B.P`, let the
    image stand at a body boundary that corresponds to a reachable machine `M`, in front of a decomposed prefix.
    Then every prefix of `n` memory-only image steps either ends in a state that corresponds (`Korrespondenz`,
    inside a decomposed step) to a reachable machine `M'` at which every leg of `Ziel` holds, or has passed
    the boundary behind the decomposed prefix, and that boundary corresponds (`Rand`) to a reachable machine at
    which every leg of `Ziel` holds. `Ziel` is a statement about those machines G, not about the image's states;
    what links an image state to its machine is the correspondence. -/
theorem bild_ziel_seq [DecidableEq D.Fn] {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn} (ls : Aufzaehlung D.Lock) {ws : List D.Fn}
    {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec B.P S fs.1 ws Acc) (hN : LogikPflicht B.P S Q) (hH : HardwareAnnahmen B.O Q)
    {sp : Speicher D} {init : Faden → Σ g : D.Fn, Env D (D.params g)} (hZ : StartZulaessig B.P S fs.1 ws sp init)
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {thr : Faden} {stapel : List (RufRahmenG D)}
    {rho : Env D (D.params B.f)} {s0 : World D} (hRuf : RufOk B.P B.O B.passes thr Agl B.R Cg)
    {l : Bool} {Γ Γe : Ctx} {Λ Λe : List (Res D)} {eb : Endblock D (vertragVon D B.f) l Γ Λ}
    {ebe : Endblock D (vertragVon D B.f) l Γe Λe} {σ σe : World D} {ρ : Env D Γ} {ρe : Env D Γe}
    (hk : Zerlegung B Agl Cg eb σ ρ ebe σe ρe) {pc : Runner.W} {m : Runner.Mem} {M : RufMaschineG D}
    (hM : RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M)
    (hR : Rand B thr stapel rho s0 Agl eb pc m M σ ρ) {n : Nat} {t : T} {m' : Runner.Mem}
    (hrun : StarM n ⟨pc, B.fp⟩ m t m') :
    (∃ M', Korrespondenz B thr stapel rho s0 Agl l t m' M' ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M' ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) M') ∨
    (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        Rand B thr stapel rho s0 Agl ebe pce me Me σe ρe ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) Me ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) Me ∧ ∃ k, StarM k ⟨pce, B.fp⟩ me t m') := by
  rcases korrespondenz_lauf hB hRuf hk hR hrun with ⟨M', hl, hK⟩ | ⟨pce, me, Me, hRe, hl, k, hk'⟩
  · have hr := rufErreichbar_lauf hl hM
    exact Or.inl ⟨M', hK, hr, ziel_aus B.P S Q fs ls ws hA hN B.O hH B.passes sp init hZ M' hr⟩
  · have hr := rufErreichbar_lauf hl hM
    exact Or.inr ⟨pce, me, Me, hRe, hr, ziel_aus B.P S Q fs ls ws hA hN B.O hH B.passes sp init hZ Me hr, k, hk'⟩

/-- **T1 from the image's first body boundary**: `bild_ziel_seq` with the start machine, under `StartEntspricht`;
    as there, `Ziel` holds at the machines G the image states correspond to. -/
theorem bild_ziel_start [DecidableEq D.Fn] {B : BodyFrame D} [TorOK B.L B.O] [SichtOK B.O] (hB : B.Ok)
    {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn} (ls : Aufzaehlung D.Lock) {ws : List D.Fn}
    {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec B.P S fs.1 ws Acc) (hN : LogikPflicht B.P S Q) (hH : HardwareAnnahmen B.O Q)
    {sp : Speicher D} {init : Faden → Σ g : D.Fn, Env D (D.params g)} (hZ : StartZulaessig B.P S fs.1 ws sp init)
    {Agl : D.Lock → Prop} {Cg : D.Fn → Prop} {thr : Faden} {rho : Env D (D.params B.f)}
    (hRuf : RufOk B.P B.O B.passes thr Agl B.R Cg) {Γe : Ctx} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D B.f) false Γe Λe} {σ σe : World D} {ρe : Env D Γe}
    (hk : Zerlegung B Agl Cg (B.P.rumpf B.f) σ rho ebe σe ρe) {pc : Runner.W} {m : Runner.Mem}
    (hSt : StartEntspricht B sp init thr rho Agl pc m σ) {n : Nat} {t : T} {m' : Runner.Mem}
    (hrun : StarM n ⟨pc, B.fp⟩ m t m') :
    (∃ M', Korrespondenz B thr [] rho (sp.welt []) Agl false t m' M' ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) M' ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) M') ∨
    (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        Rand B thr [] rho (sp.welt []) Agl ebe pce me Me σe ρe ∧
        RufErreichbarG B.P B.O B.passes (RufStartG B.P sp init) Me ∧
        Ziel B.P S B.O B.passes (RufStartG B.P sp init) Me ∧ ∃ k, StarM k ⟨pce, B.fp⟩ me t m') :=
  bild_ziel_seq (ls := ls) hB hA hN hH hZ hRuf hk RufErreichbarG.start hSt hrun

end Gabbro.Stage0.Senke.BildLauf
