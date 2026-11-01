module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtSperre.AkteurSFaelle.Teil14

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurS_dannCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
  (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutS P passes Q S f)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussS P S lok f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
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
  FadenS P O passes Q S lok
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
  obtain ⟨hks, hss, _⟩ := okS_dann_cons (kopfS_okS hF.1 hhead)
  simp only [stmtOrteP, List.append_subset] at hss
  have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
  have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ) σ (M.weltVon u) →
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => expr_stabil (hFS _) p (fun _ h' => hss.1 h') h)
      (hgσ.lese Λ Λ _ _) ρ]
    exact hv
  obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ))
    (fun _ => vertrag_stabil_ind (hFS _) g hg hp (hkand g hg))
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.2 h') h)
        (hgσ.lese Λ Λ _ _) ρ])
    ρ (.dann rest k) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_dann_cons hok).2.2)
    (fun O' U R σ e hgσ h => by
      rw [semH_dann_cons]
      simp only [execStmtH, hev σ hgσ, h]
      exact weiterH_logik S O' U passes R _ e)
    (fun O' U R σ hgσ => by
      rw [semH_dann_cons]
      simp only [execStmtH, hev σ hgσ]
      cases R g (σ.lese Λ (p.orte ++ args.orte))
          (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
            (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σa v =>
          exact ⟨fun _ => ZErgG.folgt_refl _,
            fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
      | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

set_option maxHeartbeats 4000000 in
theorem akteurS_rufCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
  (hlok : AxEnsLokal Q) (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutS P passes Q S f)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussS P S lok f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenS P O passes Q S lok (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
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
  FadenS P O passes Q S lok
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
  obtain ⟨hks, hss, _⟩ := okS_ende_cons (kopfS_okS hF.1 hhead)
  simp only [stmtOrteP, List.append_subset] at hss
  have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks
  have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ) σ (M.weltVon u) →
      eval (σ.lese Λ (p.orte ++ args.orte)) p (σ.lese Λ (p.orte ++ args.orte)) ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => expr_stabil (hFS _) p (fun _ h' => hss.1 h') h)
      (hgσ.lese Λ Λ _ _) ρ]
    exact hv
  obtain ⟨hFad, hReq⟩ := pushS_gen hO hRL hQ hS hsp hK hFragS hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ))
    (fun _ => vertrag_stabil_ind (hFS _) g hg hp (hkand g hg))
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args (fun _ h => args_stabil (hFS _) args (fun _ h' => hss.2 h') h)
        (hgσ.lese Λ Λ _ _) ρ])
    ρ (.ende rest) (fun L => held_nachSig_iff _ _ L) (fun hok => (okS_ende_cons hok).2.2)
    (fun O' U R σ e hgσ h => by
      rw [semH_ende_cons]
      simp only [execStmtH, hev σ hgσ, h]
      rfl)
    (fun O' U R σ hgσ => by
      rw [semH_ende_cons]
      simp only [execStmtH, hev σ hgσ]
      cases R g (σ.lese Λ (p.orte ++ args.orte))
          (umsig hg (evalArgs (σ.lese Λ (p.orte ++ args.orte)) args
            (σ.lese Λ (p.orte ++ args.orte)) ρ)) with
      | ok σa v =>
          exact ⟨fun _ => ZErgG.folgt_refl _,
            fun _ _ _ _ _ _ _ _ hc _ => by rcases hc with hc | ⟨_, _, hc⟩ <;> cases hc⟩
      | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

end Gabbro.Grammatik
