module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T1
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperreZeuge.T2.Teil1

@[expose] public section

namespace Gabbro.Grammatik

/-- **`ziel_ort_sperre_ref104` -- `beispiele/104-referenz.gab` certified by
    the goal theorem with lock invariants** (the empty family: 104 takes its
    lock by signature): all premises jointly, the conclusion on every
    reachable machine, and on the reached run of `r4Lauf` the `ensures` of
    `einzahlen` at its logged return. -/
theorem ziel_ort_sperre_ref104 :
    fussSperreB r4P (SperrInv.leer r4D) r4Fs = true ∧
    (∀ f : r4D.Fn, KoerperGutS r4P 0 (axWahr r4D) (SperrInv.leer r4D) f) ∧
    (∀ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M →
      VertragAmOrtG r4P M ∧ SperrInvG (SperrInv.leer r4D) M ∧ KeinLogikHaltG r4O 0 M ∧
      ∀ t : Faden, HeldGenau (M.faeden t).kopf.rest.2.2.1 (offen (M.faeden t).spur) →
        AnPruefungG M t → ∃ M', RufSchrittG r4P r4O 0 M t M') ∧
    ∃ M : RufMaschineG r4D, RufErreichbarG r4P r4O 0 (RufStartG r4P r4Sp r4Init) M ∧
      (r4Sp.slots () 0 ()).n = 0 ∧ (M.speicher.slots () 0 ()).n = 100 ∧
      (∃ (rho : Env r4D (r4D.params r4Ein)) (s0 s1 : World r4D),
        RufEreignisF.rueck r4Ein rho () s0 s1 ∈ (M.faeden 0).log ∧
        EnsAmRueck r4P r4Ein s0 s1 rho ()) := by
  have hF := fussSperreB_of_G r4P (SperrInv.leer r4D) r4Fs r4P_fussG
  have hK : ∀ f : r4D.Fn, KoerperGutS r4P 0 (axWahr r4D) (SperrInv.leer r4D) f :=
    fun f => koerperGutS_leer (r4P_koerperZ f)
  have hZ := ziel_ort_sperre r4P r4O 0 (axWahr r4D) (SperrInv.leer r4D) r4Fs r4Sp r4Init
    r4O_gut r4O_lokal (axVertragO_wahr r4O) axEnsLokal_wahr sperrInvOk_leer r4Fs_voll
    r4P_fragmentG hF hK r4P_start (fun _ => rfl) r4Init_exklusiv
  obtain ⟨M, hr, hsp, ⟨rho, s0, s1, hlog⟩, _⟩ := r4Lauf
  exact ⟨hF, hK, hZ, M, hr, rfl, hsp, ⟨rho, s0, s1, hlog, ((hZ M hr).1 0 _ hlog).2 r4Ein rho () s0 s1 rfl⟩⟩

/-- **Probe A fails the new obligation too**, for every well-formed family
    whose invariants are satisfiable: the bodies of `paP` contain no
    `locks`, so the semantics with lock invariants runs them as `execEnd`
    does -- into `logik schleife`. -/
theorem paP_nicht_sperre (Q : AxEns zD) (S : SperrInv zD)
    (hS : ∀ L (s s' : Speicher zD), (∀ c ∈ S.orte L, TraegerGleich s s' c) →
      S.inv L s = S.inv L s') (s : Speicher zD)
    (hs : ∀ L, S.inv L s = true) (f : zD.Fn) : ¬ KoerperGutS paP 0 Q S f := by
  intro h
  have hl : (paP.rumpf f).ohneLocks = true := by cases f <;> rfl
  refine h.2 zO zO_rahmen zO_lokal (zO_vertrag Q) (fun L σ => mischU S L σ s)
    (havocOk_misch_lokal hS (fun _ _ => s) (fun L _ => hs L)) hwRuf (hwRuf_rahmen paP) hwRuf_ohneLogik
    (zSp.welt []) (by cases f <;> exact .nil) rfl .schleife ?_
  rw [Endblock.execH_ohne S zO _ 0 hwRuf _ hl]
  exact paP_lauf zO hwRuf f _ _

/-- **Probe A: the premise of the new goal theorem is refuted** (for the
    empty family, and for `zS`). -/
theorem paP_nicht_sperre_leer (Q : AxEns zD) :
    ¬ ∀ f : zD.Fn, KoerperGutS paP 0 Q (SperrInv.leer zD) f :=
  fun h => paP_nicht_sperre Q _ sperrInvOk_leer.2 zSp (fun _ => rfl) zHaupt (h zHaupt)

#print axioms Gabbro.Grammatik.zPB_zertifiziert
#print axioms Gabbro.Grammatik.zPB_lauf
#print axioms Gabbro.Grammatik.zPC_zertifiziert
#print axioms Gabbro.Grammatik.sP_zertifiziert
#print axioms Gabbro.Grammatik.ziel_ort_sperre_zeuge
#print axioms Gabbro.Grammatik.ziel_ort_sperre_ref104
#print axioms Gabbro.Grammatik.paP_nicht_sperre
#print axioms Gabbro.Grammatik.paP_nicht_sperre_leer


end Gabbro.Grammatik
