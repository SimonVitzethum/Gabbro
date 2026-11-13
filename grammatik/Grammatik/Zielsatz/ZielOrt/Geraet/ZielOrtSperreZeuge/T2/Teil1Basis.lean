module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1

@[expose] public section



namespace Gabbro.Grammatik

theorem sHp : RufPasst sD (vertragVon sD sHaupt) (sD.signatur sSetze) sL where
  hw := fun _ _ => rfl
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl, List.Sublist.cons]⟩
  hh := RufPasst.hh_von (by
    intro L
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)
  hx := RufPasst.hx_von (by
    intro L
    cases L
    exact ⟨fun _ => List.mem_singleton.mpr rfl, fun _ => List.mem_singleton.mpr rfl⟩)

/-- The call `setze(x)` inside the lock. -/
def sRuf : Stmt sD (vertragVon sD sHaupt) false [.int 0 100] sL sL :=
  .call sSetze (.cons (.var .here) .nil) sHp rfl

/-- `haupt(x)`: `locks { setze(x) }; return`. -/
def sRumpfHaupt : Endblock sD (vertragVon sD sHaupt) false [.int 0 100] [] :=
  .cons (.locks () (fun _ h => nomatch h) (.cons sRuf .nil)) (.ret .empty List.Perm.nil)

/-- The two-writer program. -/
def sP : Programm sD where
  invariante := fun i => nomatch i
  requires
    | .setze => sReqSetze
    | .haupt => .tru
  ensures
    | .setze => sEnsSetze
    | .haupt => .tru
  rumpf
    | .setze => sRumpfSetze
    | .haupt => sRumpfHaupt

def sFs : List sD.Fn := [sSetze, sHaupt]

theorem sFs_voll : ∀ g : sD.Fn, g ∈ sFs := by
  intro g
  cases g
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- **The lock invariant `konto[0] == konto[1]`**, protecting `konto`. -/
def sS : SperrInv sD :=
  ⟨fun _ => [.inl ()], fun _ s => decide ((s.slots () 0 ()).n = (s.slots () 1 ()).n)⟩

theorem sS_ok : SperrInvOk sS := by
  refine ⟨fun L c hc => ?_, fun L s s' h => ?_⟩
  · cases L
    rw [List.mem_singleton.mp hc]
    exact List.mem_singleton.mpr rfl
  · have e : s.slots () = s'.slots () := h (.inl ()) List.mem_cons_self
    show decide ((s.slots () 0 ()).n = (s.slots () 1 ()).n) =
      decide ((s'.slots () 0 ()).n = (s'.slots () 1 ()).n)
    rw [e]

theorem sP_fussS : fussSperreB sP sS sFs = true := by decide

/-- The old check refuses the program: `haupt`'s callee contract reads the
    protected table outside any signature lock. -/
theorem sP_fussG_falsch : fussOrtGB sP sFs = false := by decide

theorem sP_fragmentG : programmImFragmentG sP sFs = true := by decide

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def sO : Orakel sD where
  wirktL := fun a => nomatch a
  regLiesL := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbarL := fun g => nomatch g

theorem sO_gut : GutO sO := fun a => nomatch a

theorem sO_lokal : RegLokal sO := ⟨(fun r _ _ _ => nomatch r), (fun g _ _ _ => nomatch g)⟩

/-- The start memory: `konto` all zero. -/
def sSp : Speicher sD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => nomatch g⟩

def sWert (n : Int) (h0 : 0 ≤ n) (h1 : n ≤ 100) : Env sD [.int 0 100] := .cons ⟨n, h0, h1⟩ .nil

/-- The argument of thread `t`: `30` for thread `0`, `70` for every other. -/
def sArg (t : Faden) : Env sD [.int 0 100] :=
  if t = 0 then sWert 30 (by decide) (by decide) else sWert 70 (by decide) (by decide)

/-- Thread `0` runs `haupt(30)`, every other thread `haupt(70)`: at least
    two threads write the same table under the same lock. -/
def sInit : Faden → Σ f : sD.Fn, Env sD (sD.params f) :=
  fun t => ⟨sHaupt, sArg t⟩

theorem sP_start : StartGut sP sSp sInit := fun _ => rfl

/-- `haupt` holds no lock by signature: the start is exclusive although
    every thread runs the same routine. -/
theorem sInit_exklusiv : StartExklusiv (D := sD) sInit :=
  fun _ _ _ _ h => nomatch h

theorem sS_start : ∀ L, sS.inv L sSp = true := fun _ => rfl

/-- `setze` meets its obligation: after the two writes both slots are `x`. -/
theorem sP_koerper_setze : KoerperGutS sP 0 (axWahr sD) sS sSetze := by
  have hr : sP.rumpf sSetze = sRumpfSetze := rfl
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v hrun => ?_, fun g hrun => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [sRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
    cases ρ with
    | cons x rest =>
      cases rest
      show wahr? (eval σ sEnsSetze _ (ergEnv (sD.erg sSetze) () (Env.cons x Env.nil))) = true
      simp only [wahr?, sEnsSetze, sGleich, sIdx0, sIdx1, World.lese, World.merke, World.schreibSlot,
  World.storeSlot, List.map_append, List.append_assoc, eval, Zahl.weiter, dite_eq_ite, List.cons_append,
  List.nil_append, ergEnv, Int.reduceEq, ↓reduceIte, ite_self, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨rfl, rfl⟩
  · rw [hr] at hrun
    simp only [sRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun
  · rw [hr] at hrun
    simp only [sRumpfSetze, execEndH, execStmtH] at hrun
    cases hrun

/-- The `requires` of `setze` IS the lock invariant at the call world. -/
theorem sReq_iff_inv (κ : World sD) (ρk : Env sD (sD.params sSetze)) :
    ReqAmEintritt sP sSetze κ ρk ↔ sS.inv () κ.speicher = true := Iff.rfl

/-- The `ensures` of `setze` gives the lock invariant back. -/
theorem sInv_of_ens {κ σ2 : World sD} {ρk : Env sD (sD.params sSetze)}
    {v : ErgVal sD (sD.erg sSetze)} (h : EnsAmRueck sP sSetze κ σ2 ρk v) :
    sS.inv () σ2.speicher = true := by
  have h' : (decide ((σ2.slots () 0 ()).n = (σ2.slots () 1 ()).n) &&
      decide ((σ2.slots () 0 ()).n = (ρk.get .here).n)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1

/-- **`haupt` meets its obligation -- using the lock invariant twice.** At
    the acquire the environment's move leaves `konto[0] == konto[1]`, which
    IS `setze`'s `requires` (the caller duty); at the release `setze`'s
    `ensures` gives the invariant back (the release check). -/
theorem sP_koerper_haupt : KoerperGutS sP 0 (axWahr sD) sS sHaupt := by
  have hr : sP.rumpf sHaupt = sRumpfHaupt := rfl
  refine ⟨fun O' _ _ _ U hU R hR hOV σ ρ _ => ⟨fun σ' v _ => rfl, fun g hrun => ?_⟩,
    fun O' _ _ _ U hU R hR hOL σ ρ _ e hrun => ?_⟩
  · rw [hr] at hrun
    simp only [sRumpfHaupt, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := sS) (O := O') (U := U) (passes := 0) (R := torRuf sP R)
      (l := false) (Γ := [.int 0 100]) sSetze (.cons (.var .here) .nil) sHp rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, _, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · cases hi : sS.inv () σ1.speicher with
      | true =>
          simp only [freiH, hi, if_true] at hrun
          cases hrun
      | false =>
          simp only [freiH, hi, Bool.false_eq_true, if_false] at hrun
          cases hrun
    · simp only [freiH] at hrun
      cases hrun
      have hreq : ReqAmEintritt sP sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .here) .nil) := (hU () σ).2.2
      have htor : torRuf sP R sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .here) .nil) =
          R sSetze (((U () σ).nimmt ()).lese sL []) (Env.cons (ρ.get .here) .nil) := if_pos hreq
      exact hOV _ _ _ _ (htor.symm.trans he1) g rfl
    · simp only [freiH] at hrun
      cases hrun
  · rw [hr] at hrun
    simp only [sRumpfHaupt, execEndH] at hrun
    erw [execStmtH_locks_eins] at hrun
    rcases execStmtH_call_fall (S := sS) (O := O') (U := U) (passes := 0) (R := R)
      (l := false) (Γ := [.int 0 100]) sSetze (.cons (.var .here) .nil) sHp rfl
      ((U () σ).nimmt ()) ρ with ⟨σ1, v1, hR1, h1⟩ | ⟨e1, he1, h1⟩ | ⟨e1, h1⟩ <;> erw [h1] at hrun
    · have hreq : ReqAmEintritt sP sSetze (((U () σ).nimmt ()).lese sL [])
          (Env.cons (ρ.get .here) .nil) := (hU () σ).2.2
      have hinv := sInv_of_ens (hR.1 _ _ _ hreq σ1 v1 hR1)
      simp only [freiH, hinv, if_true] at hrun
      cases hrun
    · simp only [freiH] at hrun
      cases hrun
      exact hOL _ _ _ _ he1
    · simp only [freiH] at hrun
      cases hrun

theorem sP_koerper : ∀ f : sD.Fn, KoerperGutS sP 0 (axWahr sD) sS f := by
  intro f
  cases f
  · exact sP_koerper_setze
  · exact sP_koerper_haupt

/-- **All premises of `ziel_ort_sperre` hold jointly on the two-writer
    program**, hence its conclusion on every reachable machine. -/
theorem sP_zertifiziert : ∀ M : RufMaschineG sD,
    RufErreichbarG sP sO 0 (RufStartG sP sSp sInit) M →
      VertragAmOrtG sP M ∧ SperrInvG sS M ∧ KeinLogikHaltG sO 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG sP sO 0 M t M' :=
  ziel_ort_sperre sP sO 0 (axWahr sD) sS sFs sSp sInit sO_gut sO_lokal (axVertragO_wahr sO)
    axEnsLokal_wahr sS_ok sFs_voll sP_fragmentG sP_fussS sP_koerper sP_start sS_start sInit_exklusiv

/-! ### The run: two critical sections on one table -/

/-- The start thread state of a thread running `haupt(x)`. -/
def sZ0 (ρ : Env sD [.int 0 100]) : RufFadenG sD :=
  ⟨[], ⟨sHaupt, ρ, sSp.welt [], ⟨false, [.int 0 100], [], ρ, .ende sRumpfHaupt⟩⟩, [],
    [RufEreignisF.eintritt sHaupt ρ (sSp.welt [])]⟩

theorem sM0_faden0 :
    (RufStartG sP sSp sInit).faeden 0 = sZ0 (sWert 30 (by decide) (by decide)) := by rfl

theorem sM0_faden (t : Faden) (ht : t ≠ 0) :
    (RufStartG sP sSp sInit).faeden t = sZ0 (sWert 70 (by decide) (by decide)) := by
  have e : sArg t = sWert 70 (by decide) (by decide) := if_neg ht
  show (⟨[], ⟨sHaupt, sArg t, sSp.welt [], ⟨false, sD.params sHaupt,
      Signatur.anfang sD (sD.signatur sHaupt), sArg t, .ende (sP.rumpf sHaupt)⟩⟩, startSpur sHaupt,
      [RufEreignisF.eintritt sHaupt (sArg t) (sSp.welt [])]⟩ : RufFadenG sD) = _
  rw [e]
  rfl

theorem sOffen_weltVon (M : RufMaschineG sD) (t : Faden) :
    offen (M.weltVon t).spur = offen (M.faeden t).spur := by rfl

theorem sM0_offen (t : Faden) : offen ((RufStartG sP sSp sInit).faeden t).spur = [] := by
  by_cases ht : t = 0
  · subst ht; rfl
  · rw [sM0_faden t ht]; rfl


end Gabbro.Grammatik
