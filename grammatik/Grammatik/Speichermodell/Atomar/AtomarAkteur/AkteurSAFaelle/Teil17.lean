module

public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Teil16

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannBindCallInd {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n))
  (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ) (hr : (D.sigNr n).gruende = 0)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.bindCallInd p args he hp hr rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden u).spur) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                {
                  stapel :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.wartet rest k)⟩ :
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
                                  (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.wartet rest k)⟩ :
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
                                    (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.wartet rest k)⟩ :
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
  obtain ⟨hks, hss, _⟩ := kopfSA_okS hF.1 hhead
  simp only [Block.gOk, Bool.and_eq_true] at hks
  simp only [blockOrteP, List.append_subset] at hss
  have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1
  have hev : ∀ σ : World D, GleichAuf (stabilS P S lok (M.faeden u).kopf.f Λ ++
      (p.orte ++ args.orte)) σ ((M.weltVon u).lese Λ (p.orte ++ args.orte)) →
      eval σ p σ ρ = ⟨g, hg⟩ := by
    intro σ hgσ
    rw [eval_gleichAuf p (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) hgσ ρ]
    exact hv
  obtain ⟨hFad, hReq⟩ := pushSA_gen hO hRL hQ hS hsp hK hM hFragS hF hhead (p.orte ++ args.orte) g
    (fun κ => umsig hg (evalArgs κ args κ ρ))
    (fun _ c hc => by
      rcases List.mem_append.mp hc with hc | hc
      · exact expr_stabilX (hFS _) p hss.1.1.1.1 c hc
      · exact args_stabilX (hFS _) args hss.1.1.1.2 c hc)
    (fun _ => vertrag_stabilX_ind (hFS _) hTV g hg hp (hkand g hg))
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args
        (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) hgσ ρ])
    ρ (.wartet rest k) (fun L => held_nachSig_iff _ _ L)
    (fun hok => by
      obtain ⟨hks', hss', hk⟩ := hok
      simp only [Block.gOk, Bool.and_eq_true] at hks'
      simp only [blockOrteP, List.append_subset] at hss'
      exact ⟨hks'.2, hss'.2, hk⟩)
    (fun O' U A R σ κ e hgκ hκ h => by
      rw [semHA_dann]
      simp only [execBlockHA, hκ, hev κ hgκ, h]
      exact weiterHA_logik S O' U A passes R _ e)
    (fun O' U A R σ κ hgκ hκ => by
      rw [semHA_dann]
      simp only [execBlockHA, hκ, hev κ hgκ]
      cases R g κ (umsig hg (evalArgs κ args κ ρ)) with
      | ok σa v =>
          refine ⟨fun hw => by simp only [RufRahmenG.wartend, GRest.wartend, Bool.true_eq_false] at hw,
            fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
          rcases hc with hc | ⟨_, _, hc⟩
          · cases hc
            exact ZErgG.folgt_refl _
          · cases hc
      | why σa r => exact fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannRet {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ'' : List (Res D)) (e : ErgExpr D Γ Λ (vertragVon D (M.faeden u).kopf.f).erg)
  (hperm : Λ.Perm (Vertrag.ende D (vertragVon D (M.faeden u).kopf.f)))
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ'') (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'')
  (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons (Stmt.ret e hperm) rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden u).stapel = caller :: rst)
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon u).lese Λ e.orte) (g : D.Fn)
  (hfg : (M.faeden u).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden u).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden u).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden u).spur) (hnw : caller.wartend = false) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := s1.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := rst, kopf := caller, spur := s1.spur,
                  log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := s1.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := rst, kopf := caller, spur := s1.spur,
                  log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := s1.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := rst, kopf := caller, spur := s1.spur,
                    log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  subst hfg hs0 hs1 hv
  subst hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  have hok := okS_dann_cons (kopfSA_okS hF.1 hhead)
  have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
    (ens_stabilX (hFS _) hTV hperm)
    (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ)
  have hSt := hF.2
  rw [hpop] at hSt
  obtain ⟨hWc, hSt'⟩ := hSt
  have hRS' := hRS
  rw [hpop] at hRS'
  refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
    (fun hE => popSA_begr_ok hE hF.1 hhead e
      (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm rest k σ ρ))
    (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
    caller.rest.2.2.2.1 caller.rest.2.2.2.2 (fun _ h => h) id
    (fun R O' U A σa X h => h.1 hnw) _ ⟨rfl, rfl⟩, hSt'⟩,
    logOk_rueck hL hens⟩

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannRetBind {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (lk : Bool) (Γk : Ctx) (Λk Λk'' : List (Res D)) (e : ErgExpr D Γk Λk (vertragVon D (M.faeden u).kopf.f).erg)
  (hperm : Λk.Perm (Vertrag.ende D (vertragVon D (M.faeden u).kopf.f)))
  (restk : Block D (vertragVon D (M.faeden u).kopf.f) lk Γk Λk Λk'')
  (kk : GRest D (vertragVon D (M.faeden u).kopf.f) lk Γk Λk'') (ρ : Env D Γk)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨lk,
          (⟨Γk,
              (⟨Λk, (ρ, GRest.dann (Block.cons (Stmt.ret e hperm) restk) kk)⟩ :
                (Λ : List (Res D)) × Env D Γk × GRest D (vertragVon D (M.faeden u).kopf.f) lk Γk Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) lk Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (caller : RufRahmenG D) (rst : List (RufRahmenG D)) (hpop : (M.faeden u).stapel = caller :: rst) (l : Bool) (Γ : Ctx)
  (Λ Λ' : List (Res D)) (τ : Ty) (restb : Block D (vertragVon D caller.f) l (τ :: Γ) Λ Λ')
  (k : GRest D (vertragVon D caller.f) l Γ Λ') (ρc : Env D Γ)
  (hcaller :
    caller.rest =
        (⟨l,
            (⟨Γ,
                (⟨Λ, (ρc, GRest.wartet restb k)⟩ :
                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
          (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) ∨
      ∃ n err,
        caller.rest =
          (⟨l,
              (⟨Γ,
                  (⟨Λ, (ρc, GRest.wartetSonst n err restb k)⟩ :
                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
            (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ))
  (hΛ : HeldIn Λk (offen (M.faeden u).spur)) (s1 : World D) (hs1 : s1 = (M.weltVon u).lese Λk e.orte) (g : D.Fn)
  (hfg : (M.faeden u).kopf.f = g) (rho : Env D (D.params g)) (hrho : (M.faeden u).kopf.rho = Eq.symm hfg ▸ rho)
  (s0 : World D) (hs0 : (M.faeden u).kopf.s0 = s0) (v : ErgVal D (D.erg g)) (hv : v = hfg ▸ evalErg s1 e s1 ρ)
  (he : D.erg g = some τ) (neu : List (Ereignis D)) (hneu : s1.spur = neu ++ (M.faeden u).spur) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := s1.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := rst,
                  kopf :=
                    { f := caller.f, rho := caller.rho, s0 := caller.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                  (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := s1.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := rst,
                  kopf :=
                    { f := caller.f, rho := caller.rho, s0 := caller.s0,
                      rest :=
                        (⟨l,
                            (⟨τ :: Γ,
                                (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                  (Λ : List (Res D)) × Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := s1.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := rst,
                    kopf :=
                      { f := caller.f, rho := caller.rho, s0 := caller.s0,
                        rest :=
                          (⟨l,
                              (⟨τ :: Γ,
                                  (⟨Λ, (Env.cons (ergWert he v) ρc, GRest.dann restb k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (τ :: Γ) × GRest D (vertragVon D caller.f) l (τ :: Γ) Λ)⟩ :
                                (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D caller.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := s1.spur, log := RufEreignisF.rueck g rho v s0 s1 :: (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  subst hfg hs0 hs1 hv
  subst hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  have hok := okS_dann_cons (kopfSA_okS hF.1 hhead)
  have hens := popSA_ens hO hRL hQ hS hsp hK hF.1 hhead e (erg_stabilX (hFS _) e hok.2.1)
    (ens_stabilX (hFS _) hTV hperm)
    (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm restk kk σ ρ)
  have hSt := hF.2
  rw [hpop] at hSt
  obtain ⟨hWc, hSt'⟩ := hSt
  have hRS' := hRS
  rw [hpop] at hRS'
  refine ⟨⟨popSA_kopf hWc _ (fun σa => .ok σa _) (Or.inl ⟨_, fun _ => rfl, hens⟩)
    (fun hE => popSA_begr_ok hE hF.1 hhead e
      (fun O' R U A σ => semHA_dannRet S O' U A passes R e hperm restk kk σ ρ))
    (gleichOhne_of_stapelS hRS' _ ⟨rfl, rfl⟩)
    (.cons (ergWert he _) ρc) (.dann restb (.schrumpf k))
    (fun L h => by rcases hcaller with hc | ⟨n, err, hc⟩ <;> rw [hc] <;> exact h)
    (fun hokc => by
      rcases hcaller with hc | ⟨n, err, hc⟩
      · have h' := rest_okS hc hokc
        exact ⟨h'.1, h'.2.1, h'.2.2⟩
      · have h' := rest_okS hc hokc
        exact ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩)
    (fun R O' U A σa X h => h.2 l Γ Λ Λ' τ restb k ρc hcaller he) _ ⟨rfl, rfl⟩, hSt'⟩,
    logOk_rueck hL hens⟩

end Gabbro.Grammatik
