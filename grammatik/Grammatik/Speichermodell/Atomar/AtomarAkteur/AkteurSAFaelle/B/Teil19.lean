module

public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil18

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannRegLiesElseFalsch {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (r : D.Reg) (hk : (D.rklasse r).lesbar = true)
  (zusage : Expr D (D.rtyp r :: Γ) Λ Ty.bool) (sonst : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.rtyp r :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.regReadElse r hk zusage sonst rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (v : Wert D (D.rtyp r))
  (hv : einpassen O.zeiger (D.rtyp r) (O.regLies r ((M.weltVon u).fragt (Sum.inr (Sum.inl r)))) = some v) (σ₁ : World D)
  (hs₁ : σ₁ = ((M.weltVon u).fragt (Sum.inr (Sum.inl r))).lese Λ zusage.orte)
  (hw : wahr? (eval σ₁ zusage σ₁ (Env.cons v ρ)) = false) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := M.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨Λ, (ρ, GRest.dann sonst.alsBlock.snd k.abbruch)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  subst hs₁
  refine ⟨fadenSA_fragtLese hF hhead ρ (.dann sonst.alsBlock.2 (.abbruch k)) _ (.inr (.inl r)) Λ zusage.orte
    (fun hok => by
      obtain ⟨_, hss, _⟩ := hok
      simp only [blockOrteP, List.append_subset] at hss
      exact expr_stabilX (hFS _) zusage hss.1.1)
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrk⟩ := hok
  simp only [Block.gOk, Bool.and_eq_true] at hks
  simp only [blockOrteP, List.append_subset] at hss
  obtain ⟨⟨_, hsS⟩, _⟩ := hss
  have hw' : wahr? (eval σ zusage σ (.cons v ρ)) = false := by
    rw [eval_gleichAuf zusage (fun _ h => List.mem_append_right _ h) hg]; exact hw
  refine ⟨σ, ⟨Nat.le_refl _, Nat.le_refl _⟩, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
    okS_alsBlock sonst k rest.held_iff hks.2.1 hsS hrk, fun R O' U A σ0 hQ hg0 hσ0 => ?_⟩
  have hrl : O'.regLies r (σ0.fragt (.inr (.inl r))) = O.regLies r ((M.weltVon u).fragt (.inr (.inl r))) :=
    regLies_gleich (σ := σ0.fragt (.inr (.inl r))) (W := (M.weltVon u).fragt (.inr (.inl r))) hRL hQ r
      (regP_stabil (Λ := Λ) hks.1) hg0
  have h1 := semHA_regLiesElseFalsch S O' U A passes R r hk zusage sonst rest k σ0 ρ v
    (by rw [hrl, show O'.zeiger = O.zeiger from hQ.2.2]; exact hv) (by rw [hσ0]; exact hw')
  rw [hσ0] at h1
  exact h1

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannAwaits {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (g : D.Glob) (payload : List D.Glob) (hp : payload = D.nutzlast g)
  (hLg : gdarf D g Λ) (hat : D.atomar g = true)
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ Λ')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.awaits g payload hp hLg hat rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hvis : O.sichtbar g ((M.weltVon u).fragt (Sum.inr (Sum.inr g))) = true) (σ₁ : World D)
  (hs₁ : σ₁ = ((M.weltVon u).fragt (Sum.inr (Sum.inr g))).lese Λ [Sum.inr g]) (neu : List (Ereignis D))
  (hneu : σ₁.spur = neu ++ (M.faeden u).spur) (hΛ : HeldIn Λ (offen (M.faeden u).spur)) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.gtyp g :: Γ,
                                (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.gtyp g :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := M.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨D.gtyp g :: Γ,
                                (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                  (Λ : List (Res D)) ×
                                    Env D (D.gtyp g :: Γ) ×
                                      GRest D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := M.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨D.gtyp g :: Γ,
                                  (⟨Λ, (Env.cons (σ₁.globs g) ρ, GRest.dann rest k.schrumpf)⟩ :
                                    (Λ : List (Res D)) ×
                                      Env D (D.gtyp g :: Γ) ×
                                        GRest D (vertragVon D (M.faeden u).kopf.f) l (D.gtyp g :: Γ) Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ₁.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  subst hs₁
  refine ⟨fadenSA_fragtLese hF hhead _ (.dann rest (.schrumpf k)) _ (.inr (.inr g)) Λ [.inr g]
    (fun hok => by
      obtain ⟨_, hss, _⟩ := hok
      simp only [blockOrteP, List.cons_subset] at hss
      intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact stabil_of_fussX (hFS _) hss.1 fun L hB => bewacht_held (c := .inr g) hLg hB)
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := hok
  simp only [Block.gOk] at hks
  simp only [blockOrteP, List.cons_subset] at hss
  have hglob : σ.globs g = (((M.weltVon u).fragt (.inr (.inr g))).lese Λ [.inr g]).globs g :=
    hg.2 g (List.mem_append_right _ List.mem_cons_self)
  refine ⟨σ, ⟨Nat.le_refl _, Nat.le_refl _⟩, GleichAuf.mono (fun _ h => List.mem_append_left _ h) hg,
    ⟨hks, hss.2, hrest⟩, fun R O' U A σ0 hQ _ hσ0 => ?_⟩
  have hsv : O'.sichtbar g (leseA A (σ0.fragt (.inr (.inr g))) Λ [.inr g]) = true := by
    rw [hσ0, sichtbar_gleich hRL hQ g (List.mem_append_right _ List.mem_cons_self) hg,
      sichtbar_lese hRL.2]
    exact hvis
  have h1 := semHA_awaits S O' U A passes R g payload hp hLg hat rest k σ0 ρ hsv
  rw [hσ0, hglob] at h1
  exact ZErgG.folgt_of_eq h1

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannBindCallIndElse {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
    {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
    {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragOP (PreQ P) Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
    (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
    (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
    (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
    (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
    (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
    (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
    (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n))
    (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
    (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l (.why (D.sigNr n).gruende :: Γ)
      (nachSig D (D.sigNr n) Λ))
    (rest : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ) Λ')
    (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ)
    (hhead : (M.faeden u).kopf.rest = (⟨l, (⟨Γ, (⟨Λ, (ρ, GRest.dann
      (Block.bindCallIndElse p args he hp hr err rest) k)⟩ :
      (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
      (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
    (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D)
    (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
    (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
    (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
    (hneu : s0.spur = neu ++ (M.faeden u).spur)
    : FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := M.speicher,
          faeden := rufUpdateG M.faeden u
            { stapel :=
                { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                    rest := (⟨l, (⟨Γ, (⟨nachSig D (D.sigNr n) Λ,
                      (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                      (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                  RufRahmenG D } :: (M.faeden u).stapel,
              kopf :=
                { f := g, rho := rho, s0 := s0,
                  rest := (⟨false, (⟨D.params g, (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                    (Λ : List (Res D)) × Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                    (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                    (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                  RufRahmenG D },
              spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden u)
      ({ speicher := M.speicher,
          faeden := rufUpdateG M.faeden u
            { stapel :=
                { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                    rest := (⟨l, (⟨Γ, (⟨nachSig D (D.sigNr n) Λ,
                      (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                      (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                  RufRahmenG D } :: (M.faeden u).stapel,
              kopf :=
                { f := g, rho := rho, s0 := s0,
                  rest := (⟨false, (⟨D.params g, (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                    (Λ : List (Res D)) × Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                    (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                    (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                  RufRahmenG D },
              spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
          lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon u) ∧
      LogOk P
        ({ speicher := M.speicher,
            faeden := rufUpdateG M.faeden u
              { stapel :=
                  { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                    rest := (⟨l, (⟨Γ, (⟨nachSig D (D.sigNr n) Λ,
                      (ρ, GRest.wartetSonst (D.sigNr n).gruende err rest k)⟩ :
                      (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                    (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                    RufRahmenG D } :: (M.faeden u).stapel,
                kopf :=
                  { f := g, rho := rho, s0 := s0,
                    rest := (⟨false, (⟨D.params g, (⟨Signatur.anfang D (D.signatur g), (rho, GRest.ende (P.rumpf g))⟩ :
                      (Λ : List (Res D)) × Env D (D.params g) × GRest D (vertragVon D g) false (D.params g) Λ)⟩ :
                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                      (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                    RufRahmenG D },
                spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden u).log := by
  subst hs0 hrho
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  obtain ⟨hks, hss, _⟩ := kopfSA_okS hF.1 hhead
  simp only [Block.gOk, Bool.and_eq_true] at hks
  simp only [blockOrteP, List.append_subset] at hss
  have hkand : KandOk P (fussOrteG P (M.faeden u).kopf.f) n := kandP_ok hks.1.1
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
      · exact expr_stabilX (hFS _) p hss.1.1.1.1.1 c hc
      · exact args_stabilX (hFS _) args hss.1.1.1.1.2 c hc)
    (fun _ => vertrag_stabilX_ind (hFS _) hTV g hg hp (hkand g hg))
    (fun _ σ hgσ => by
      show umsig hg _ = umsig hg _
      rw [evalArgs_gleichAuf args
        (fun _ h => List.mem_append_right _ (List.mem_append_right _ h)) hgσ ρ])
    ρ (.wartetSonst (D.sigNr n).gruende err rest k) (fun L => held_nachSig_iff _ _ L)
    (fun hok => by
      obtain ⟨hks, hss, hk⟩ := hok
      simp only [Block.gOk, Bool.and_eq_true] at hks
      simp only [blockOrteP, List.append_subset] at hss
      exact ⟨hks.1.2, hss.1.2, hks.2, hss.2, hk⟩)
    (fun O' U A R σ κ e hgκ hκ h => by
      rw [semHA_dann]
      simp only [execBlockHA, indSonst, hκ, hev κ hgκ, h]
      exact weiterHA_logik S O' U A passes R _ e)
    (fun O' U A R σ κ hgκ hκ => by
      rw [semHA_dann]
      simp only [execBlockHA, indSonst, hκ, hev κ hgκ]
      cases R g κ (umsig hg (evalArgs κ args κ ρ)) with
      | ok σa v =>
          refine ⟨fun hw => by simp only [RufRahmenG.wartend, GRest.wartend, Bool.true_eq_false] at hw,
            fun _ _ _ _ _ _ _ _ hc he' => ?_⟩
          rcases hc with hc | ⟨_, _, hc⟩
          · cases hc
          · cases hc
            exact ZErgG.folgt_refl _
      | why σa r =>
          intro _ _ _ _ _ _ _ _ _ _ hc hn
          cases hc
          rw [semHA_alsBlock_schrumpf]
          simp only [grundSig_eq_cast hg hn r]
          exact ZErgG.folgt_refl _
      | logik e => trivial
      | hardware e => trivial)
  exact ⟨hFad, logOk_eintritt hL hReq⟩

end Gabbro.Grammatik
