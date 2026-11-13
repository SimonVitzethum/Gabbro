module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollZeuge.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem vHoff_gg {M : RufMaschineG vD} {f : Faden} {caller : RufRahmenG vD}
    {rst : List (RufRahmenG vD)} {fn : vD.Fn} {rho : Env vD (vD.params fn)} {s0 : World vD}
    {log : List (RufEreignisF vD)} {r : Fin (vD.gruende fn)} {σ : World vD}
    {x : List vD.Lock} (h : GepopptGrundG M f caller rst fn rho s0 log r σ)
    (ho : offen (M.faeden f).spur = x) : offen σ.spur = x := by
  rw [h.1] at ho; exact ho

theorem vHoff_e {M : RufMaschineG vD} {f : Faden} {z : RufFadenG vD} {x : List vD.Lock}
    (e : M.faeden f = z) (ho : offen (M.faeden f).spur = x) : offen z.spur = x := by
  rw [← e]; exact ho

/-- `rufCallInd` over a thread state (as `w_rufEnde`): the pointer read at
    the key names the callee `g`. -/
theorem w_rufCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {M : RufMaschineG D} {f : Faden} {z : RufFadenG D}
    (hz : M.faeden f = z) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (hp : RufPasst D (vertragVon D z.kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
    (rest : Endblock D (vertragVon D z.kopf.f) l Γ (nachSig D (D.sigNr n) Λ)) (ρ : Env D Γ)
    (hhead : z.kopf.rest = ⟨l, Γ, Λ, ρ, .ende (.cons (.callInd p args hp hr) rest)⟩)
    (hΛ : HeldGenau Λ (offen z.spur)) (g : D.Fn) (hg : D.passt g n = true)
    (hv : eval ((M.weltVon f).lese Λ (p.orte ++ args.orte)) p
      ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f (⟨z.kopf.f, z.kopf.rho, z.kopf.s0,
          ⟨l, Γ, nachSig D (D.sigNr n) Λ, ρ, .ende rest⟩⟩ :: z.stapel) g
        (umsig hg (evalArgs ((M.weltVon f).lese Λ (p.orte ++ args.orte)) args
          ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ))
        ((M.weltVon f).lese Λ (p.orte ++ args.orte))
        (RufEreignisF.eintritt g
          (umsig hg (evalArgs ((M.weltVon f).lese Λ (p.orte ++ args.orte)) args
            ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ))
          ((M.weltVon f).lese Λ (p.orte ++ args.orte)) :: z.log)
        (umsig hg (evalArgs ((M.weltVon f).lese Λ (p.orte ++ args.orte)) args
          ((M.weltVon f).lese Λ (p.orte ++ args.orte)) ρ))
        (.ende (P.rumpf g)) ((M.weltVon f).lese Λ (p.orte ++ args.orte)) := by
  subst hz
  exact ⟨_, RufSchrittG.rufCallInd M f l Γ Λ n p args hp hr rest ρ hhead hΛ.heldIn _ rfl g hg hv _ rfl
    _ rfl, zustandG_neu rfl rfl⟩

/-- The axiom's answer world appends only access events. -/
theorem vO_erw (σ : World vD) (ρ : Env vD (vD.aparams ())) :
    Erw σ (vO.wirkt () σ ρ).1 :=
  ⟨_, rfl, fun e he => by
    simp only [Orakel.wirkt, vO, World.auf, axiomSpur, List.mem_append, List.mem_map,
      List.mem_filter] at he
    rcases he with ⟨t, _, rfl⟩ | ⟨g, _, _⟩
    · rfl
    · exact nomatch g⟩

/-- **The run.** Fourteen steps of thread 0 of G from the start machine of
    `vP` (every thread in `haupt`, the slot `false`): `haupt` calls `mid`
    through the pointer `&mid`,
    `mid` unfolds its `if` and calls `ferr` in `let … else`; `ferr` returns
    its reason, which pops into `mid`'s `else` block (logged `grund`);
    `mid` returns to `haupt` (logged `rueck`); `haupt` enters the `retry`
    loop, whose body is left by `leave`; `haupt` takes the lock and calls
    the axiom, which writes the slot `true`. -/
theorem vLauf : ∃ M : RufMaschineG vD,
    RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M ∧
    M.speicher.slots () 0 () = true ∧
    (∃ rho r s0 s1, RufEreignisF.why vErr rho r s0 s1 ∈ (M.faeden 0).log) ∧
    (∃ rho v s0 s1, RufEreignisF.rueck vMid rho v s0 s1 ∈ (M.faeden 0).log) ∧
    (M.faeden 0).kopf.f = vHaupt ∧ (() : vD.Lock) ∈ offen (M.faeden 0).spur ∧
    M.faeden 1 = (RufStartG vP vSp vInit).faeden 1 := by
  have h0 := vM0_faden (0 : Faden)
  have hoff0 : offen ((RufStartG vP vSp vInit).faeden 0).spur = [] := rfl
  -- `haupt` calls `mid`
  obtain ⟨M1, s1, hZ1⟩ := w_rufCallInd (P := vP) (O := vO) (passes := 0) h0 vZeigerMid .nil vHpMid
    rfl vRestHaupt .nil rfl (vHg0 hoff0) vMid rfl rfl
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff0
  have e1 := hZ1.1
  try dsimp only at e1
  -- `mid`: unfold the `if`, take its true branch, call `ferr` in `let … else`
  obtain ⟨M2, s2, hZ2⟩ := w_endeEntf (P := vP) (O := vO) (passes := 0) e1 vIte
    (.ret .empty List.Perm.nil) .nil rfl rfl
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur, vOffen_weltVon]; exact hoff1
  have e2 := hZ2.1
  try dsimp only at e2
  obtain ⟨M3, s3, hZ3⟩ := w_iteWahr (P := vP) (O := vO) (passes := 0) e2 .tru vLetElse .nil
    .nil (.ende (.ret .empty List.Perm.nil)) .nil rfl rfl (vHg0 (vHoff_e e2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hZ3.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff2
  have e3 := hZ3.1
  try dsimp only at e3
  obtain ⟨M4, s4, hZ4⟩ := w_bindCallElse (P := vP) (O := vO) (passes := 0) e3 vErr .nil rfl
    vHpErr (by decide) vErrBlock .nil (.dann .nil (.ende (.ret .empty List.Perm.nil))) .nil rfl
    (vHg0 (vHoff_e e3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff3
  have e4 := hZ4.1
  try dsimp only at e4
  -- `ferr` returns its reason; `mid` runs its `else` block
  obtain ⟨M5, s5, hG5⟩ := w_rueckGrundP (P := vP) (O := vO) (passes := 0) e4 _ _ rfl
    (PopGrund.sonst vErrBlock .nil (.dann .nil (.ende (.ret .empty List.Perm.nil))) .nil rfl)
    vR0 List.Perm.nil .nil rfl (vHg0 (vHoff_e e4 hoff4)).heldIn
  have hoff5 : offen (M5.faeden 0).spur = [] := by
    rw [hG5.1]; exact hoff4
  have e5 := hG5.1
  try dsimp only at e5
  -- `mid` returns to `haupt`
  obtain ⟨M6, s6, hG6⟩ := w_dannRetP (P := vP) (O := vO) (passes := 0) e5 _ _ rfl
    (PopArt.wie rfl) .empty List.Perm.nil .nil _ _ rfl (vHg0 (vHoff_e e5 hoff5)).heldIn
  have hoff6 : offen (M6.faeden 0).spur = [] := by
    rw [hG6.1]
    exact ((Erw.lese _ _ _).offen).trans hoff5
  have e6 := hG6.1
  try dsimp only at e6
  -- `haupt`: the loop, left by `leave`
  obtain ⟨M7, s7, hZ7⟩ := w_endeEntf (P := vP) (O := vO) (passes := 0) e6 vRetry
    (.cons vLocks (.ret .empty List.Perm.nil)) .nil rfl rfl
  have hoff7 : offen (M7.faeden 0).spur = [] := by
    rw [hZ7.spur, vOffen_weltVon]; exact hoff6
  have e7 := hZ7.1
  try dsimp only at e7
  obtain ⟨M8, s8, hZ8⟩ := w_dannRetry (P := vP) (O := vO) (passes := 0) e7 1 .fls vLeave
    .nil .nil (.ende (.cons vLocks (.ret .empty List.Perm.nil))) .nil rfl
  have hoff8 : offen (M8.faeden 0).spur = [] := by
    rw [hZ8.spur, vOffen_weltVon]; exact hoff7
  have e8 := hZ8.1
  try dsimp only at e8
  obtain ⟨M9, s9, hZ9⟩ := w_wiederSchritt (P := vP) (O := vO) (passes := 0) e8 0 .fls vLeave
    .nil (.dann .nil (.ende (.cons vLocks (.ret .empty List.Perm.nil)))) .nil rfl rfl
    (vHg0 (vHoff_e e8 hoff8)).heldIn
  have hoff9 : offen (M9.faeden 0).spur = [] := by
    rw [hZ9.spur, (Erw.lese _ _ _).offen, vOffen_weltVon]; exact hoff8
  have e9 := hZ9.1
  try dsimp only at e9
  obtain ⟨M10, s10, hZ10⟩ := w_abbWieder (P := vP) (O := vO) (passes := 0) e9 true 0 .fls
    vLeave .nil (.dann .nil (.ende (.cons vLocks (.ret .empty List.Perm.nil)))) .nil .nil rfl
    (vHg0 (vHoff_e e9 hoff9)).heldIn
  have hoff10 : offen (M10.faeden 0).spur = [] := by
    rw [hZ10.spur, vOffen_weltVon]; exact hoff9
  have e10 := hZ10.1
  try dsimp only at e10
  obtain ⟨M11, s11, hZ11⟩ := w_dannLeer (P := vP) (O := vO) (passes := 0) e10
    (.ende (.cons vLocks (.ret .empty List.Perm.nil))) .nil rfl
  have hoff11 : offen (M11.faeden 0).spur = [] := by
    rw [hZ11.spur, vOffen_weltVon]; exact hoff10
  have e11 := hZ11.1
  try dsimp only at e11
  -- `haupt`: take the lock, call the axiom
  obtain ⟨M12, s12, hZ12⟩ := w_endeEntf (P := vP) (O := vO) (passes := 0) e11 vLocks
    (.ret .empty List.Perm.nil) .nil rfl rfl
  have hoff12 : offen (M12.faeden 0).spur = [] := by
    rw [hZ12.spur, vOffen_weltVon]; exact hoff11
  have e12 := hZ12.1
  try dsimp only at e12
  have hfremd12 : ∀ u, u ≠ 0 → M12.faeden u = vZ0 := by
    intro u hu
    rw [rufSchrittG_fremd s12 u hu, rufSchrittG_fremd s11 u hu, rufSchrittG_fremd s10 u hu,
      rufSchrittG_fremd s9 u hu, rufSchrittG_fremd s8 u hu, rufSchrittG_fremd s7 u hu,
      rufSchrittG_fremd s6 u hu, rufSchrittG_fremd s5 u hu, rufSchrittG_fremd s4 u hu,
      rufSchrittG_fremd s3 u hu, rufSchrittG_fremd s2 u hu, rufSchrittG_fremd s1 u hu, vM0_faden]
  obtain ⟨M13, s13, hZ13⟩ := w_locks (P := vP) (O := vO) (passes := 0) e12 ()
    (fun _ h => by cases h) (.cons vAx .nil) .nil (.ende (.ret .empty List.Perm.nil)) .nil rfl
    (vHg0 (vHoff_e e12 hoff12))
    (fun u hu h => by rw [hfremd12 u hu] at h; exact List.not_mem_nil h)
  have hoff13 : offen (M13.faeden 0).spur = [()] := by
    rw [hZ13.spur]
    show offen (Ereignis.nimmt () (offen (M12.weltVon 0).spur) :: (M12.weltVon 0).spur) = [()]
    simp only [offen]
    rw [vOffen_weltVon, hoff12]
    rfl
  have e13 := hZ13.1
  try dsimp only at e13
  obtain ⟨M14, s14, hZ14⟩ := w_dannBlatt (P := vP) (O := vO) (passes := 0) e13 vAx .nil
    _ .nil rfl rfl
    (vHgL (vHoff_e e13 hoff13)).heldIn _ _ rfl
    ((Erw.lese _ _ _).trans ((Erw.fragt _ _).trans (vO_erw _ .nil)))
  have hr14 : RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M14 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _
      (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1) s2) s3) s4) s5) s6) s7) s8) s9)
      s10) s11) s12) s13) s14
  have e14 := hZ14.1
  try dsimp only at e14
  refine ⟨M14, hr14, ?_, ?_, ?_, by rw [e14]; rfl, ?_, ?_⟩
  · rw [hZ14.2]
    rfl
  · rw [e14]
    exact ⟨_, _, _, _, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · rw [e14]
    exact ⟨_, _, _, _, List.mem_cons_self⟩
  · have hoff14 : offen (M14.faeden 0).spur = [()] := by
      rw [hZ14.spur]
      exact ((vO_erw ((M13.weltVon 0).lese vL []) .nil).offen).trans
        (((Erw.lese _ _ _).offen).trans hoff13)
    rw [hoff14]
    exact List.mem_cons_self
  · rw [rufSchrittG_fremd s14 1 (by decide), rufSchrittG_fremd s13 1 (by decide), hfremd12 1
      (by decide)]
    rfl

/-! ## 4. The witness -/

/-- **`ziel_ort_voll_zeuge`.** On the two-thread program `vP` (every thread
    starts in `haupt`), whose bodies use an indirect call (`haupt` calls
    `mid` through `&mid`), a `retry` loop left by `leave`, a reason return
    (`ferr`) caught by `let … else` (`mid`) and an axiom call writing the
    guarded table under its lock (`haupt`) -- a program OUTSIDE
    the fragment of `ziel_ort` -- every premise of `ziel_ort_voll` holds
    jointly: the hardware assumption for the writing oracle, the complete
    member list, both decidable checks, the user obligation `KoerperGutV`
    for all three functions, the start obligation and the exclusive start.
    On a machine reached by fourteen steps of thread 0, the axiom has
    changed memory (the slot from `false` to `true`), the reason return and
    `mid`'s normal return after catching it are logged, the loop is behind
    (thread 0 is in `haupt`, holding the lock after the axiom), thread 1 has
    not moved, and the contracts hold at every logged entry and return. -/
theorem ziel_ort_voll_zeuge :
    GutO vO ∧ (∀ g : vD.Fn, g ∈ vFs) ∧ programmImFragmentV vP vFs = true ∧
    programmImFragment vP vFs = false ∧ fussOrtB vP vFs = true ∧
    (∀ f : vD.Fn, KoerperGutV vP 0 f) ∧ StartGut vP vSp vInit ∧
    StartExklusiv (D := vD) vInit ∧
    ∃ M : RufMaschineG vD, RufErreichbarG vP vO 0 (RufStartG vP vSp vInit) M ∧
      vSp.slots () 0 () = false ∧ M.speicher.slots () 0 () = true ∧
      (∃ rho r s0 s1, RufEreignisF.why vErr rho r s0 s1 ∈ (M.faeden 0).log) ∧
      (∃ rho v s0 s1, RufEreignisF.rueck vMid rho v s0 s1 ∈ (M.faeden 0).log) ∧
      (M.faeden 0).kopf.f = vHaupt ∧ (() : vD.Lock) ∈ offen (M.faeden 0).spur ∧
      M.faeden 1 = (RufStartG vP vSp vInit).faeden 1 ∧
      VertragAmOrtG vP M := by
  obtain ⟨M, hr, hsp, hg, hru, hf, hL, h1⟩ := vLauf
  exact ⟨vO_gut, vFs_voll, vP_fragment, vP_nicht_alt, vP_fuss, vP_koerper, vP_start,
    vInit_exklusiv, M, hr, rfl, hsp, hg, hru, hf, hL, h1, vP_vertragAmOrt M hr⟩

/-! ## CUTS:

  What is proved: all premises of `ziel_ort_voll` hold jointly on `vP`
  (`vP_vertragAmOrt` is the instance), `vP` is outside the old fragment
  (`vP_nicht_alt`), and a reached run of fourteen steps of G through an
  indirect push (`rufCallInd`), a `let … else` push, a reason pop into the `else` block, a normal
  pop, the `retry` unfold, a failed bound, the `leave` exit, the `locks`
  take and the axiom leaf (`vLauf`), with the memory change done by the
  axiom (`ziel_ort_voll_zeuge`).

  What is NOT covered: the run moves thread 0 only (thread 1 is started
  in `haupt` and stays there); the contracts are `true`, so the witness
  shows the premises jointly satisfiable and the run real, not a
  contract whose proof needs the new obligation's frame reasoning.
-/

#print axioms Gabbro.Grammatik.vO_gut
#print axioms Gabbro.Grammatik.vP_koerper
#print axioms Gabbro.Grammatik.vP_vertragAmOrt
#print axioms Gabbro.Grammatik.vLauf
#print axioms Gabbro.Grammatik.ziel_ort_voll_zeuge

end Gabbro.Grammatik

namespace Gabbro.Grammatik

/-- A waiting caller and a callee returning the first reason. -/
def vGrundCaller : RufRahmenG vD :=
  ⟨vMid, .nil, vSp.welt [],
    ⟨false, [], nach vD vErr [], .nil,
      .wartetSonst (τ := .bool) (vD.gruende vErr) vErrBlock .nil
        (.ende (.ret .empty List.Perm.nil))⟩⟩

def vGrundM : RufMaschineG vD :=
  { RufStartG vP vSp vInit with
    faeden := fun _ => ⟨[vGrundCaller],
      ⟨vErr, .nil, vSp.welt [], ⟨false, [], [], .nil, .ende vRumpfErr⟩⟩,
      [], []⟩ }

/-- The generic faithful-reason theorem on an actual reason-pop step. -/
theorem rufG_grund_treu_zeuge :
    ∃ M' : RufMaschineG vD,
      RufSchrittG vP vO 0 vGrundM 0 M' ∧
      (M'.faeden 0).log =
        [RufEreignisF.why vErr .nil vR0 (vSp.welt []) (vGrundM.weltVon 0)] ∧
      (vGrundM.faeden 0).kopf.f = vErr ∧
      (∃ r' : Fin (vertragVon vD (vGrundM.faeden 0).kopf.f).gruende,
        (vGrundM.faeden 0).kopf.rest.2.2.2.2.grundJetzt = some r' ∧ HEq r' vR0) ∧
      (M'.faeden 0).stapel = [] := by
  have hs := RufSchrittG.rueckGrund (P := vP) (O := vO) (passes := 0)
    vGrundM 0 vR0 List.Perm.nil Env.nil rfl vGrundCaller [] rfl
    false [] [] [] .bool (vD.gruende vErr) vErrBlock .nil
    (.ende (.ret .empty List.Perm.nil)) .nil rfl
    (vHg0 (show offen (vGrundM.faeden 0).spur = [] from rfl)).heldIn
    vErr rfl .nil rfl (vSp.welt []) rfl vR0 rfl rfl
  have ht := rufG_grund_treu hs vErr .nil vR0 (vSp.welt [])
    (vGrundM.weltVon 0) (by simp only [rufUpdateG_self])
  exact ⟨_, hs, by simp only [rufUpdateG_self]; rfl,
    ht.1, ht.2.1, by simp only [rufUpdateG_self]⟩

end Gabbro.Grammatik
