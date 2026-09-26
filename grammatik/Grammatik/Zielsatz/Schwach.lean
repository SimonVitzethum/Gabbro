/-
  File:      Grammatik/Zielsatz/Schwach.lean
  Subject:   THE GOAL OVER THE WEAK MACHINE (Opus agent B, 2026-09-26): every leg of `Ziel`
             holds at every machine the weak machine W reaches (`gabbro_ziel_schwach`).

  `gabbro_ziel_g` proves `Ziel` at every machine G reaches (since the merge with Opus agent A,
  2026-09-26, `gabbro_ziel` itself is over the thread machine and `gabbro_ziel_g` is its
  corollary on G's runs), and since 2026-09-26 `Ziel` carries
  the leg `schwach` (`SchwachSC`, Spec.lean): at every such machine every step of W over it is
  a step of G. By induction over the runs of W that makes every machine W reaches a G-part G
  reaches (`schwach_erreichbar`), and `Ziel` holds there. Conversely every machine G reaches
  is the G-part of one W reaches (`w_aus_g`, MaschineW.lean), so on an accepted program the
  two machines reach exactly the same G-states (`schwach_gleich_g`), for every assignment of
  memory orders.

  On the THREAD machine (`gabbro_ziel`, `ZielF`) the leg is `ZielF.g.schwach` at `K.m`
  (`gabbro_zielF_schwach`): the weak machine is taken over G's runs from the start machine, and
  every thread-machine state is the G-part of such a run (`fadenErreichbar_G`). W does NOT model
  spawn and join as synchronisation points (`pthread_create`/`pthread_join` order): a thread
  spawned at run time is, in W, a thread of G's start whose first step comes later. Under the
  DRF-by-exclusion argument that costs nothing -- a child reading what its parent wrote is
  refused by `fuss` unless the carrier is guarded -- but it is not a claim about spawn/join
  as release/acquire.
-/
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **From the leg to the runs**: if `SchwachSC` holds at every machine G reaches from `M0`,
    every machine W reaches from the weak start over `M0` has a G-part G reaches. -/
theorem schwach_erreichbar {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    (hS : ∀ M, RufErreichbarG P O passes M0 M → SchwachSC P O passes M0 M)
    {ord : D.Glob → Speichermodell.Ordnung} {W : RufMaschineW D}
    (hr : RufErreichbarW P O passes ord (RufStartW M0) W) :
    RufErreichbarG P O passes M0 W.g := by
  induction hr with
  | start => exact .start
  | schritt W W' u hW hs ih =>
      exact .schritt _ _ _ ih (hS W.g ih ord W W' u hW rfl hs)

/-- **GABBRO_ZIEL OVER THE WEAK MACHINE.** Under the premises of `GabbroZiel`, for every
    assignment of memory orders to the atomics, every leg of `Ziel` holds at every machine
    the weak machine W reaches from the runtime's start. -/
theorem gabbro_ziel_schwach (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflicht E) (O : Orakel D)
    (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (ord : D.mitRuhe.Glob → Speichermodell.Ordnung)
    (W : RufMaschineW D.mitRuhe)
    (hr : RufErreichbarW E.P.mitRuhe O.mitRuhe passes ord
      (RufStartW (RufStartG E.P.mitRuhe sp init)) W) :
    RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) W.g ∧
      Ziel E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) W.g := by
  have hZ := fun M hM => gabbro_ziel_g C D E fs ls cs hC hN O hH passes sp init hL M hM
  have hg := schwach_erreichbar (fun M hM => (hZ M hM).schwach) hr
  exact ⟨hg, hZ W.g hg⟩

/-- **On an accepted program W and G reach the same G-states**, for every order assignment. -/
theorem schwach_gleich_g (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflicht E) (O : Orakel D)
    (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (ord : D.mitRuhe.Glob → Speichermodell.Ordnung)
    (M : RufMaschineG D.mitRuhe) :
    RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) M ↔
      ∃ W, RufErreichbarW E.P.mitRuhe O.mitRuhe passes ord
        (RufStartW (RufStartG E.P.mitRuhe sp init)) W ∧ W.g = M := by
  constructor
  · intro hM
    obtain ⟨W, hW, hg, _⟩ := w_aus_g (ord := ord) hM
    exact ⟨W, hW, hg⟩
  · rintro ⟨W, hW, rfl⟩
    exact (gabbro_ziel_schwach C D E fs ls cs hC hN O hH passes sp init hL ord W hW).1

/-- **The weak leg on the thread machine**: at every reachable thread machine, every step of W
    over its G-part is a step of G. A named projection of `gabbro_ziel` (`ZielF.g.schwach`);
    the W runs meant are those from the runtime's start machine (spawn/join order not modelled
    in W, see the header). -/
theorem gabbro_zielF_schwach (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflicht E) (O : Orakel D)
    (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbar E.P.mitRuhe O.mitRuhe passes
      (FadenStart E.P.mitRuhe sp init lebt0) K) :
    SchwachSC E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) K.m :=
  (gabbro_ziel C D E fs ls cs hC hN O hH passes sp init hL lebt0 K hK).g.schwach

#print axioms Gabbro.Grammatik.Zielsatz.schwach_erreichbar
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_zielF_schwach
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_schwach
#print axioms Gabbro.Grammatik.Zielsatz.schwach_gleich_g

end Gabbro.Grammatik.Zielsatz
