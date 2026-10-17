/- Part 3 of 3 of `RufHaeltG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufHaeltG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.RufHaeltG.T2

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The start machine satisfies the invariant: the start trace holds the
    signature locks, the entry residue names them. -/
theorem haeltInvG_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    HaeltInvG ((RufStartG P sp init).faeden t) := by
  show HaeltInvG (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D))
  cases init t with
  | mk g rho =>
    refine ⟨?_, ?_, trivial⟩
    · intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · intro L hL
        exact (offen_startSpur g L).mpr ((held_anfang _ L).mp hL)
      · exact absurd hF List.not_mem_nil
    · intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact fun L hL => (held_anfang _ L).mpr hL
      · exact absurd hF List.not_mem_nil

/-- The invariant holds at every thread of every reachable machine. -/
theorem rufG_haeltInv {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) : ∀ t, HaeltInvG (M.faeden t) := by
  induction h with
  | start => exact haeltInvG_start P sp init
  | schritt M M' g _ hs ih =>
      intro t
      by_cases htg : t = g
      · subst htg
        exact rufSchrittG_haeltInv hO hs (ih t)
      · rw [rufSchrittG_passt_anders P O passes M M' g t htg hs]
        exact ih t

/-- **STATIC HOLDINGS ARE HELD (`rufG_haelt_statisch`).** On every machine
    reachable from the start, for every thread `t` and every frame `F` on
    its stack -- the head and every suspended caller -- every lock the
    frame's static holdings name (`Res.held L ∈ Λ` of its residue) is held
    by `t` (`L ∈ offen` of its trace). The only assumption is `GutO` (the
    oracle keeps the held locks). -/
theorem rufG_haelt_statisch {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (t : Faden) :
    ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, ∀ L : D.Lock,
      Res.held L ∈ F.rest.2.2.1 → L ∈ offen (M.faeden t).spur :=
  (rufG_haeltInv hO sp init h t).alle

/-- **Signature locks are held for the whole life of a frame.** Every
    frame on a reachable stack holds every lock of its function's signature
    (`requires Held(L)`), from entry to return. -/
theorem rufG_haelt_signatur {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f)) {M : RufMaschineG D}
    (h : RufErreichbarG P O passes (RufStartG P sp init) M) (t : Faden) :
    ∀ F ∈ (M.faeden t).kopf :: (M.faeden t).stapel, ∀ L ∈ D.haelt F.f,
      L ∈ offen (M.faeden t).spur :=
  (rufG_haeltInv hO sp init h t).signatur

/-! ## CUTS:

  What is proved: on every machine of the repaired G reachable from ANY
  start (any program, oracle with `GutO`, start memory and start
  assignment), every frame on every stack names in its static holdings
  only locks its thread holds (`rufG_haelt_statisch`), in particular its
  function's signature locks (`rufG_haelt_signatur`); the thread invariant
  `HaeltInvG` is kept by every one of the 70 rules
  (`rufSchrittG_haeltInv`). The witnesses on a non-degenerate two-thread
  program are in `ZielOrtZeuge.lean` (`rufG_haelt_statisch_zeuge`,
  `rufG_haelt_signatur_zeuge`).

  What is NOT proved here: exclusivity of held locks across threads needs
  a fact about the start assignment (`StartExklusiv`) and is in
  `ZielOrt.lean` (`exklusivG`). The rules of G demand `HeldIn` of the
  head's holdings -- exactly the first part of this invariant -- so the
  side condition holds on every reachable machine; `HeldGenau` (equality)
  is not an invariant any more: a callee runs under its caller's extra
  locks.
-/

#print axioms Gabbro.Grammatik.rufSchrittG_haeltInv
#print axioms Gabbro.Grammatik.rufG_haelt_statisch
#print axioms Gabbro.Grammatik.rufG_haelt_signatur


end Gabbro.Grammatik
