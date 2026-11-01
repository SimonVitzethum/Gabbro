module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVollBeweis
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Teil14

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurV_dannCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n))
  (args : Args D Γ Λ (D.sigNr n).params) (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ)
  (hr : (D.sigNr n).gruende = 0) (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ (nachSig D (D.sigNr n) Λ) Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.callInd p args hp hr) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden u).spur) :
  FadenV P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                {
                  stapel :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.dann rest k)⟩ :
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
                                  (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.dann rest k)⟩ :
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
                                    (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.dann rest k)⟩ :
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
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  subst hs0 hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  obtain ⟨hks, hss, _⟩ := okV_dann_cons (kopfV_okV hF.1 hhead)
  simp only [stmtOrteP, List.append_subset] at hss
  have hkand : KandOk P (fussOrte P (M.faeden u).kopf.f) n := kandP_ok hks
  have hev : ∀ σ : World D, GleichAuf (fussOrte P (M.faeden u).kopf.f) σ (M.weltVon u) →
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => hss.1 h) (hgσ.lese Λ Λ _ _) ρ]
    exact hv
  obtain ⟨hFad, hReq⟩ := pushV_gen hO hK hFrag hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args (fun _ h => hss.2 h) (hgσ.lese Λ Λ _ _) ρ])
    ρ (.dann rest k) (fun hok => (okV_dann_cons hok).2.2)
    (fun O' R σ e hgσ h => by
      rw [semV_dann_cons]
      simp only [execStmt, hev σ hgσ, h]
      exact weiterZ_logik O' passes R _ e)
    (fun O' R σ hgσ => by
      rw [semV_dann_cons]
      simp only [execStmt, hev σ hgσ]
      cases R g (σ.lese Λ (p.orte ++ args.orte))
          (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
            (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σa v =>
          exact ⟨fun _ => ZErg.folgt_refl _,
            fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
      | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

set_option maxHeartbeats 4000000 in
theorem akteurV_rufCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  (hO : GutO O) (hK : ∀ (f : D.Fn), KoerperGutV P passes f)
  (hFrag : ∀ (f : D.Fn), Endblock.vOk (kandP P (fussOrte P f)) (P.rumpf f) = true) (e0 : Ereignis D)
  {M : RufMaschineG D} {u : Faden} (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
  (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ (nachSig D (D.sigNr n) Λ)) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons (Stmt.callInd p args hp hr) rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden u).spur) :
  FadenV P O passes
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                {
                  stapel :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.ende rest)⟩ :
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
                                  (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.ende rest)⟩ :
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
                                    (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.ende rest)⟩ :
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
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  subst hs0 hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  obtain ⟨hks, hss, _⟩ := okV_ende_cons (kopfV_okV hF.1 hhead)
  simp only [stmtOrteP, List.append_subset] at hss
  have hkand : KandOk P (fussOrte P (M.faeden u).kopf.f) n := kandP_ok hks
  have hev : ∀ σ : World D, GleichAuf (fussOrte P (M.faeden u).kopf.f) σ (M.weltVon u) →
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => hss.1 h) (hgσ.lese Λ Λ _ _) ρ]
    exact hv
  obtain ⟨hFad, hReq⟩ := pushV_gen hO hK hFrag hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ)) (fun _ => hkand g hg)
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args (fun _ h => hss.2 h) (hgσ.lese Λ Λ _ _) ρ])
    ρ (.ende rest) (fun hok => (okV_ende_cons hok).2.2)
    (fun O' R σ e hgσ h => by
      rw [semV_ende_cons]
      simp only [execStmt, hev σ hgσ, h]
      rfl)
    (fun O' R σ hgσ => by
      rw [semV_ende_cons]
      simp only [execStmt, hev σ hgσ]
      cases R g (σ.lese Λ (p.orte ++ args.orte))
          (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
            (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σa v =>
          exact ⟨fun _ => ZErg.folgt_refl _,
            fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
      | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

end Gabbro.Grammatik
