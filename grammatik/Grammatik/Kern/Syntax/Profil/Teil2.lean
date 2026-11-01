module

public import Grammatik.Kern.Semantik.Semantik
public import Grammatik.Kern.Syntax.Profil.Teil1

@[expose] public section

namespace Gabbro.Grammatik

def zeugeD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp only [Bool.false_eq_true] at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- The witness profile: arch = x86_64, fpKontraktion = aus. -/
def zeugeProfil : Profil zeugeD :=
  [ .modus "arch" "ziel" .arch zeugeArch,
    .modus "fp-kontraktion" "ziel" .fpKontraktion zeugeKontraktionAus ]

/-- The witness library: requires fpKontraktion = aus. -/
def zeugeBibliothek : Bibliothek zeugeD :=
  { name := "gpu"
    anforderungen := [.modus "fp-kontraktion" "ziel" .fpKontraktion zeugeKontraktionAus] }

/-- The witness profile is good: distinct keys, distinct names. -/
theorem zeugeProfil_gut : Profil.gut zeugeProfil := by
  constructor
  · intro a ha b hb k v w h1 h2
    simp only [zeugeProfil, List.mem_cons] at ha hb
    obtain ⟨na, ca, rfl⟩ := h1
    obtain ⟨nb, cb, rfl⟩ := h2
    -- Both sides are constructor equalities against the two profile
    -- entries; inject in all four cases.
    cases ha with
    | inl heq =>
        cases hb with
        | inl heq2 =>
            cases heq
            cases heq2
            rfl
        | inr heq2 =>
            cases heq2 with
            | inl heqA =>
                cases heq
                cases heqA
            | inr heqB =>
                simp only [List.not_mem_nil] at heqB
    | inr heq =>
        cases heq with
        | inl heqA =>
            cases hb with
            | inl heq2 =>
                cases heqA
                cases heq2
            | inr heqB =>
                cases heqB with
                | inl heqC =>
                    cases heqA
                    cases heqC
                    rfl
                | inr heqD =>
                    simp only [List.not_mem_nil] at heqD
        | inr heqB =>
            simp only [List.not_mem_nil] at heqB
  · intro a ha b hb hname
    simp only [zeugeProfil, List.mem_cons] at ha hb
    simp only [eintragName] at hname
    -- Four membership cases; the mixed ones contradict the name equality.
    cases ha with
    | inl heq =>
        cases hb with
        | inl heq2 =>
            rw [heq, heq2]
            simp only [namensGleichheit, namensGleichheitAux, and_self]
        | inr heq2 =>
            cases heq2 with
            | inl heqA =>
                rw [heq, heqA] at hname
                simp only [String.reduceEq] at hname
            | inr heqB =>
                simp only [List.not_mem_nil] at heqB
    | inr heq =>
        cases heq with
        | inl heqA =>
            cases hb with
            | inl heq2 =>
                rw [heqA, heq2] at hname
                simp only [String.reduceEq] at hname
            | inr heqB =>
                cases heqB with
                | inl heqC =>
                    rw [heqA, heqC]
                    simp only [namensGleichheit, namensGleichheitAux, and_self]
                | inr heqD =>
                    simp only [List.not_mem_nil] at heqD
        | inr heqB =>
            simp only [List.not_mem_nil] at heqB

/-- The witness profile holds only keyed entries. -/
theorem zeugeProfil_keyed : ∀ a ∈ zeugeProfil, ∃ k v, istModus a k v := by
  intro a ha
  simp only [zeugeProfil, List.mem_cons] at ha
  cases ha with
  | inl heq =>
      rw [heq]
      exact ⟨.arch, zeugeArch, "arch", "ziel", rfl⟩
  | inr heq =>
      cases heq with
      | inl heqA =>
          rw [heqA]
          exact ⟨.fpKontraktion, zeugeKontraktionAus, "fp-kontraktion", "ziel", rfl⟩
      | inr heqB =>
          simp only [List.not_mem_nil] at heqB

/-- The witness library binds: its one requirement is in the profile. -/
theorem zeugeBibliothek_bindet : Profil.bindet zeugeProfil zeugeBibliothek := by
  intro r hr
  simp only [zeugeBibliothek, List.mem_singleton] at hr
  subst hr
  refine ⟨AnnahmeEintrag.modus "fp-kontraktion" "ziel" .fpKontraktion
    zeugeKontraktionAus, ?_, ?_, ?_⟩
  · simp only [zeugeProfil, List.mem_cons, AnnahmeEintrag.modus.injEq, String.reduceEq, reduceCtorEq, false_and,
  and_false, and_self, List.not_mem_nil, or_false, or_true]
  · simp only [eintragName, anforderungName]
  · simp only [namensGleichheit, namensGleichheitAux, anforderungEintrag, and_self]

/-- ZEUGE for `profil_modell`: the witness profile is good and keyed, so the
    model exists -- instantiated jointly with `zeugeProfil_gut` and
    `zeugeProfil_keyed`. -/
theorem profil_modell_zeuge :
    ∃ m : ModusBelegung, Profil.gilt (D := zeugeD) zeugeProfil m :=
  profil_modell zeugeProfil zeugeProfil_gut zeugeProfil_keyed

/-- ZEUGE for `bindung_fuegt_nichts_hinzu`: the witness library binds, so the
    profile's conjunction implies the library's -- instantiated jointly with
    the profile model and `zeugeBibliothek_bindet`. -/
theorem bindung_fuegt_nichts_hinzu_zeuge (m : ModusBelegung)
    (hgilt : Profil.gilt (D := zeugeD) zeugeProfil m) :
    Bibliothek.gilt zeugeBibliothek m :=
  bindung_fuegt_nichts_hinzu zeugeProfil zeugeBibliothek m hgilt
    zeugeBibliothek_bindet

#print axioms Gabbro.Grammatik.profil_modell
#print axioms Gabbro.Grammatik.bindung_fuegt_nichts_hinzu
#print axioms Gabbro.Grammatik.widerspruch_abgelehnt
#print axioms Gabbro.Grammatik.profil_modell_zeuge
#print axioms Gabbro.Grammatik.bindung_fuegt_nichts_hinzu_zeuge

/- CUTS: what is not proved.
   - Decidable `Profil.gut` for free-prose entries: the boolean checker
     `pruefeSchluessel` decides only the keyed half (`einigung`, via
     `pruefeSchluessel_einigung`); same-name content agreement over `Prop`
     fields (`namensGleichheit` on `.frei`) is undecidable in general and
     stays a `Prop`. The task asks "Decidable for keyed entries" -- that is
     exactly the half delivered.
   - Same-name checking as `Bool`: no `pruefeName` boolean is provided, since
     content equality over prose `Prop`s is not computable; the name half of
     `Profil.gut` is only stated, not decided.
   - No wiring into the program theorem: `profil_modell` builds the mode
     assignment, but no goal theorem takes the profile as its assumption set
     yet -- that is the E6 remainder (library call syntax, translator
     declarations live in other lanes).
   - Free-prose assumptions carry no falsifier probe here: the entry stores
     the claim as a field, but the manifest/probe bookkeeping of §0c point 5
     is not modelled.
-/

end Gabbro.Grammatik
