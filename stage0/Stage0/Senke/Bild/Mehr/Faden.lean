/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Faden.lean
  Subject:   A segment's G steps on the thread machine over GX (multi-thread image theorem, first piece of package
             MT2). At a segment end the runner thread's G thread takes the steps the single-thread chain names
             (`RufLaufG` of one thread). A live thread that joins nothing takes them on the thread machine over GX
             too: each G step is a `lauf` step (a G step is a GX step presenting G's own memory, `gx_aus_g`); the
             live threads, the join lists, the ranks and the clock stay (`fadenErreichbarX_lauf`). So every machine
             the chain reaches from a reachable thread machine is the G state of a reachable thread machine, from
             the same start -- the premise of `gabbro_ziel`'s conclusion `ZielFX`.
-/
module
public import Grammatik.Speichermodell.Maschine.GXMaschine
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **The steps of one live, non-joining thread continue a reachable thread machine over GX.** -/
theorem fadenErreichbarX_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {K0 : FadenMaschine D} {f : Faden} {M M' : RufMaschineG D} (hl : RufLaufG P O passes f M M') :
    ∀ {lebt : Faden → Bool} {wartet : Faden → List Faden} {rang : Faden → Nat} {uhr : Nat},
      lebt f = true → wartet f = [] → FadenErreichbarX P O passes Tg K0 ⟨M, lebt, wartet, rang, uhr⟩ →
      FadenErreichbarX P O passes Tg K0 ⟨M', lebt, wartet, rang, uhr⟩ := by
  induction hl with
  | refl => exact fun _ _ h => h
  | schritt hs _ ih =>
    intro lebt wartet rang uhr hf hw h
    exact ih hf hw (.schritt _ _ h (.lauf ⟨_, lebt, wartet, rang, uhr⟩ f _ hf hw (gx_aus_g hs)))

/-- The same for a thread machine given whole: its G state moves by the thread's steps, the rest stays. -/
theorem fadenErreichbarX_lauf' {P : Programm D} {O : Orakel D} {passes : Nat} {Tg : D.Tab ⊕ D.Glob → Prop}
    {K0 K : FadenMaschine D} {f : Faden} {M' : RufMaschineG D} (hl : RufLaufG P O passes f K.m M')
    (hf : K.lebt f = true) (hw : K.wartet f = []) (h : FadenErreichbarX P O passes Tg K0 K) :
    FadenErreichbarX P O passes Tg K0 ⟨M', K.lebt, K.wartet, K.rang, K.uhr⟩ :=
  fadenErreichbarX_lauf hl hf hw h

end Gabbro.Stage0.Senke.BildMehr
