module

public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetBeweis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraet.AkteurGFaelle.Tail.Teil18
import Mathlib.Tactic.Tauto

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurG_dannBindCallIndElse {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat)
  (p : Expr D Γ Λ (Ty.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
  (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.why (D.sigNr n).gruende :: Γ)
    (nachSig D (D.sigNr n) Λ))
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindCallIndElse p args he hp hr err rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D)
  (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden u).spur) :
  FadenG P O passes
      ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden u
              {
                stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden u
              {
                stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden u
              {
                stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden u).log := by
  subst hs0 hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  obtain ⟨hks, hss, _⟩ := kopfG_okG hF.1 hhead
  simp only [Block.gOk, Bool.and_eq_true] at hks
  have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1.1
  have hpa : p.orte ++ args.orte ⊆ fussOrteG P (M.faeden u).kopf.f := by
    intro x hx
    apply hss
    simp only [blockOrteP, List.mem_append] at hx ⊢
    tauto
  have hev : ∀ σ : World D, GleichAuf (fussOrteG P (M.faeden u).kopf.f) σ (M.weltVon u) →
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => hpa (List.mem_append_left _ h)) (hgσ.lese Λ Λ _ _) ρ]
    exact hv
  have hargs : args.orte ⊆ fussOrteG P (M.faeden u).kopf.f := by
    intro x hx
    apply hss
    simp only [blockOrteP, List.mem_append] at hx ⊢
    tauto
  obtain ⟨hFad, hReq⟩ := pushG_gen hO hRL hK hFrag hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args (fun _ h => hargs h) (hgσ.lese Λ Λ _ _) ρ])
    ρ (.wartetSonst (D.sigNr n).gruende err rest k)
    (fun hok => by
      obtain ⟨hks', hss', hk'⟩ := hok
      simp only [Block.gOk, Bool.and_eq_true] at hks'
      refine ⟨hks'.1.2, ?_, hks'.2, ?_, hk'⟩
      · intro x hx
        apply hss'
        simp only [blockOrteP, List.mem_append] at hx ⊢
        tauto
      · intro x hx
        apply hss'
        simp only [blockOrteP, List.mem_append] at hx ⊢
        tauto)
    (fun O' R σ e hgσ h => by
      rw [semV_dann]
      simp only [execBlock, indSonst, hev σ hgσ, h]
      exact weiterZ_logik O' passes R _ e)
    (fun O' R σ hgσ => by
      rw [semV_dann]
      simp only [execBlock, indSonst, hev σ hgσ]
      cases R g (σ.lese Λ (p.orte ++ args.orte))
          (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
            (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σa v =>
          refine ⟨fun hw => by simp only [RufRahmenG.wartend, GRest.wartend, Bool.true_eq_false] at hw,
            fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
          rcases hc with hc | ⟨_, _, hc⟩
          · cases hc
          · cases hc
            exact ZErg.folgt_refl _
      | why σa r =>
          intro _ _ _ _ _ _ _ _ _ _ hc hn
          cases hc
          rw [semV_alsBlock_schrumpf]
          simp only [grundSig_eq_cast hg hn r]
          exact ZErg.folgt_refl _
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

set_option maxHeartbeats 4000000 in
theorem akteurG_dannCallIndElse {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hRL : RegLokal O) (hK : ∀ (f : D.Fn), KoerperGutG P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (fussOrteG P f)) (P.rumpf f) = true)
  (e0 : Ereignis D) {M : RufMaschineG D} {u : Faden} (hF : FadenG P O passes (M.faeden u) (M.weltVon u))
  (hL : LogOk P (M.faeden u).log) (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat)
  (p : Expr D Γ Λ (Ty.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
  (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l (Ty.why (D.sigNr n).gruende :: Γ)
    (nachSig D (D.sigNr n) Λ))
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.callIndElse p args he hp hr err) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D)
  (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden u).spur) :
  FadenG P O passes
      ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden u
              {
                stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (τ := τ) (D.sigNr n).gruende err .nil
                                    (GRest.dann rest k))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden u
              {
                stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (τ := τ) (D.sigNr n).gruende err .nil
                                    (GRest.dann rest k))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := M.speicher,
          faeden :=
            rufUpdateG M.faeden u
              {
                stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨nachSig D (D.sigNr n) Λ,
                                  (ρ, GRest.wartetSonst (τ := τ) (D.sigNr n).gruende err .nil
                                    (GRest.dann rest k))⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D } ::
                    (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest :=
                      (⟨false,
                          (⟨D.params g,
                              (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                                (Λ : List (Res D)) ×
                                  Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden u).log := by
  subst hs0 hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  obtain ⟨hks, hss, _⟩ := kopfG_okG hF.1 hhead
  simp only [Block.gOk, Stmt.gOk, Bool.and_eq_true] at hks
  have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1.1
  have hpa : p.orte ++ args.orte ⊆ fussOrteG P (M.faeden u).kopf.f := by
    intro x hx
    apply hss
    simp only [blockOrteP, stmtOrteP, List.mem_append] at hx ⊢
    tauto
  have hev : ∀ σ : World D, GleichAuf (fussOrteG P (M.faeden u).kopf.f) σ (M.weltVon u) →
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => hpa (List.mem_append_left _ h)) (hgσ.lese Λ Λ _ _) ρ]
    exact hv
  have hargs : args.orte ⊆ fussOrteG P (M.faeden u).kopf.f := by
    intro x hx
    apply hss
    simp only [blockOrteP, stmtOrteP, List.mem_append] at hx ⊢
    tauto
  obtain ⟨hFad, hReq⟩ := pushG_gen hO hRL hK hFrag hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args (fun _ h => hargs h) (hgσ.lese Λ Λ _ _) ρ])
    ρ (.wartetSonst (τ := τ) (D.sigNr n).gruende err .nil (.dann rest k))
    (fun hok => by
      obtain ⟨hks', hss', hk'⟩ := hok
      simp only [Block.gOk, Stmt.gOk, Bool.and_eq_true] at hks'
      refine ⟨hks'.1.2, ?_, by simp only [Block.gOk], ?_, ⟨hks'.2, ?_, hk'⟩⟩
      · intro x hx
        apply hss'
        simp only [blockOrteP, stmtOrteP, List.mem_append] at hx ⊢
        tauto
      · intro x hx
        cases hx
      · intro x hx
        apply hss'
        simp only [blockOrteP, stmtOrteP, List.mem_append] at hx ⊢
        tauto)
    (fun O' R σ e hgσ h => by
      rw [semV_dann]
      simp only [execBlock, execStmt, indSonst, hev σ hgσ, h]
      exact weiterZ_logik O' passes R _ e)
    (fun O' R σ hgσ => by
      rw [semV_dann]
      simp only [execBlock, execStmt, indSonst, hev σ hgσ]
      cases R g (σ.lese Λ (p.orte ++ args.orte))
          (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
            (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σa v =>
          refine ⟨fun hw => by simp only [RufRahmenG.wartend, GRest.wartend, Bool.true_eq_false] at hw,
            fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
          rcases hc with hc | ⟨_, _, hc⟩
          · cases hc
          · cases hc
            simp only [semV_dann, execBlock]
            exact ZErg.folgt_refl _
      | why σa r =>
          intro _ _ _ _ _ _ _ _ _ _ hc hn
          cases hc
          rw [semV_alsBlock_schrumpf]
          simp only [grundSig_eq_cast hg hn r]
          exact ZErg.folgt_refl _
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

end Gabbro.Grammatik
