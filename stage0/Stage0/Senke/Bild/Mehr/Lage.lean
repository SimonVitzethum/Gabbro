/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Lage.lean
  Subject:   Where one runner thread stands in machine G (multi-thread image theorem, package MT1). `MLage` bundles
             what the single-thread chain needs about one thread: its body frame `B`, its G thread `thr`, the caller
             stack and entry data, the boundary it last passed (`eb` with world `σ` and environment `ρ`, the image's
             `pc` and memory `mb` there, the view machine `M` that corresponds to it) and the end `ebe` of the
             decomposed prefix in front of it. `MLage.Ok` is the premise set of `korrespondenz_lauf`. With a solo run
             of the thread from that boundary (`SoloLauf`), the single-thread chain P0-P5 applies to the thread
             UNCHANGED at every instruction boundary (`MLage.korrespondenz`): its solo state corresponds to a
             machine its G thread reaches from `M`, or the thread has passed the end of the decomposed prefix.
-/
module
public import Stage0.Senke.Bild.Korrespondenz
public import Stage0.Senke.Bild.Mehr.Solo
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik Gabbro.Stage0.Senke Gabbro.Stage0.Senke.BildLauf Runner.IR

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- **The G position of one runner thread.** -/
structure MLage (D : Deklaration) where
  B : BodyFrame D
  thr : Faden
  stapel : List (RufRahmenG D)
  rho : Env D (D.params B.f)
  s0 : World D
  Agl : D.Lock → Prop
  Cg : D.Fn → Prop
  l : Bool
  Γ : Ctx
  Λ : List (Res D)
  eb : Endblock D (vertragVon D B.f) l Γ Λ
  σ : World D
  ρ : Env D Γ
  Γe : Ctx
  Λe : List (Res D)
  ebe : Endblock D (vertragVon D B.f) l Γe Λe
  σe : World D
  ρe : Env D Γe
  pc : Runner.W
  mb : Runner.Mem
  M : RufMaschineG D

variable [Kern]

/-- **The premises of the single-thread chain at the position**: the gate and view assumptions, the frame's standing
    premises, the call obligation, the decomposed prefix from the boundary, and the correspondence at the boundary. -/
structure MLage.Ok (x : MLage D) : Prop where
  tor : TorOK x.B.L x.B.O
  sicht : SichtOK x.B.O
  frame : x.B.Ok
  ruf : RufOk x.B.P x.B.O x.B.passes x.thr x.Agl x.B.R x.Cg
  zerl : Zerlegung x.B x.Agl x.Cg x.eb x.σ x.ρ x.ebe x.σe x.ρe
  rand : Rand x.B x.thr x.stapel x.rho x.s0 x.Agl x.eb x.pc x.mb x.M x.σ x.ρ

/-- The image state at the boundary of the position. -/
def MLage.start (x : MLage D) : T := ⟨x.pc, x.B.fp⟩

/-- **P0-P5 for one thread of several**: at an instruction boundary of its solo run, the thread's state corresponds
    to a machine its G thread reaches from the view machine (`Korrespondenz`), or it has passed the end of the
    decomposed prefix, whose boundary corresponds to a machine its G thread reaches. -/
theorem MLage.korrespondenz {x : MLage D} (hx : x.Ok) {t : T} {m : Runner.Mem}
    (hs : SoloLauf x.start x.mb (.next t) m) :
    (∃ M', RufLaufG x.B.P x.B.O x.B.passes x.thr x.M M' ∧
        Korrespondenz x.B x.thr x.stapel x.rho x.s0 x.Agl x.l t m M') ∨
    (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
        Rand x.B x.thr x.stapel x.rho x.s0 x.Agl x.ebe pce me Me x.σe x.ρe ∧
        RufLaufG x.B.P x.B.O x.B.passes x.thr x.M Me ∧ ∃ k, StarM k ⟨pce, x.B.fp⟩ me t m) := by
  obtain ⟨n, hn⟩ := hs.starM
  have := hx.tor
  have := hx.sicht
  exact korrespondenz_lauf hx.frame hx.ruf hx.zerl hx.rand hn

end Gabbro.Stage0.Senke.BildMehr
