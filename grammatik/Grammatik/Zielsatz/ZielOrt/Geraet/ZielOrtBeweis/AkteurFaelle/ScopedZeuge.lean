module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtBeweis.AkteurFaelle.Scoped

@[expose] public section

namespace Gabbro.Grammatik

/-- A real lexical lock and a nonzero result, using the converse's declaration. -/
def scopedZExpr : ErgExpr adD [] adΛL (vertragVon adD adFn).erg :=
  .val (.widen (by decide) (by decide) (.lit 7))

def scopedZRumpf : Endblock adD (vertragVon adD adFn) false [] [] :=
  .cons (.locks () (fun _ h => absurd h List.not_mem_nil)
    (.cons (.retScoped scopedZExpr umkehrScopedR) .nil))
    (.ret (.val adSieben) List.Perm.nil)

def scopedZP : Programm adD :=
  { adP with rumpf := fun | true => scopedZRumpf | false => adCallerRumpf }

private theorem scopedZ_koerper : ∀ f, KoerperGut scopedZP adO 0 f := by
  intro f R _ _ σ ρ _
  cases f <;> refine ⟨?_, ?_⟩
  all_goals first
    | (intro σ' v h; rfl)
    | (intro g h; cases h)

def scopedZFaden : RufFadenG adD :=
  ⟨[], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], _, Env.nil,
    .aufraeumen ⟨.inl umkehrScopedWert, umkehrScopedVor⟩ [()]⟩⟩,
    umkehrScopedVor.spur, []⟩

def scopedZM : RufMaschineG adD :=
  ⟨adSp0, fun _ => scopedZFaden, [], adSp0.welt []⟩

def scopedZDone : RufFadenG adD :=
  ⟨[], ⟨adFn, Env.nil, adSp0.welt [], ⟨false, [], _, Env.nil,
    .zurueckgekehrt ⟨.inl umkehrScopedWert, umkehrScopedVor⟩⟩⟩,
    (umkehrScopedVor.gibt ()).spur, []⟩

def scopedZM' : RufMaschineG adD :=
  ⟨adSp0, rufUpdateG scopedZM.faeden 0 scopedZDone,
    [⟨0, .gibt ()⟩], adSp0.welt []⟩

private theorem scopedZ_replay :
    FadenOk scopedZP adO 0 (scopedZM.faeden 0) (scopedZM.weltVon 0) ∧
      LogOk scopedZP (scopedZM.faeden 0).log := by
  refine ⟨⟨⟨[], adSp0.welt [], rfl, funk_nil, vertraegeOk_nil _, kurzH_nil _,
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩, trivial, ?_⟩, trivial⟩, ?_⟩
  · intro R _
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · intro ev h
    exact (List.not_mem_nil h).elim

/-- Nonempty cleanup jointly satisfies the actor's replay and log premises,
    releases the actual lock, and completes the root with the saved value. -/
theorem akteur_gruppe7_zeuge :
    RufSchrittG7 scopedZP adO 0 scopedZM 0 scopedZM' ∧
    FadenOk scopedZP adO 0 (scopedZM.faeden 0) (scopedZM.weltVon 0) ∧
    LogOk scopedZP (scopedZM.faeden 0).log ∧
    FadenOk scopedZP adO 0 (scopedZM'.faeden 0) (scopedZM'.weltVon 0) ∧
    LogOk scopedZP (scopedZM'.faeden 0).log := by
  have hs : RufSchrittG7 scopedZP adO 0 scopedZM 0 scopedZM' :=
    .rueckFreigabeLetzte scopedZM 0 Env.nil
      ⟨.inl umkehrScopedWert, umkehrScopedVor⟩ () rfl scopedZDone rfl
  exact ⟨hs, scopedZ_replay.1, scopedZ_replay.2,
    akteur_gruppe7 scopedZ_koerper (.gibt ()) hs scopedZ_replay.1 scopedZ_replay.2⟩

#print axioms Gabbro.Grammatik.akteur_gruppe7
#print axioms Gabbro.Grammatik.akteur_gruppe7_zeuge

end Gabbro.Grammatik
