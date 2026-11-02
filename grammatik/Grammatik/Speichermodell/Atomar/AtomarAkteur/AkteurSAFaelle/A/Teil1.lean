module

public import Grammatik.Speichermodell.Atomar.AtomarReplay
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Basis

@[expose] public section

namespace Gabbro.Grammatik

set_option maxHeartbeats 4000000 in
theorem akteurSA_blatt {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (s : Stmt D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ) (hleaf : s.istBlatt = true)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons s rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
  (hstep : execStmt O passes keinRuf s (M.weltVon u) ρ = Ausgang.ok σ' ρ') (hneu : σ'.spur = neu ++ (M.faeden u).spur)
  (hkein : ∀ (L : D.Lock) (h : List D.Lock), ¬Ereignis.nimmt L h ∈ neu) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := σ'.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ', (ρ', GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ'.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := σ'.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ', (ρ', GRest.ende rest)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ'.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := σ'.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨Λ', (ρ', GRest.ende rest)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ'.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenSA_blatt hO hQ hlok hFS hF hhead s (.ende rest)
    (fun O' R U A σ => semHA_ende_cons S O' U A passes R s rest σ ρ)
    (fun hok => by
      obtain ⟨_, hss, hrest⟩ := okS_ende_cons hok
      exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannBlatt {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (s : Stmt D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Block D (vertragVon D (M.faeden u).kopf.f) l Γ Λ' Λ'')
  (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ'') (ρ : Env D Γ) (hleaf : s.istBlatt = true)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann (Block.cons s rest) k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ))
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (σ' : World D) (ρ' : Env D Γ) (neu : List (Ereignis D))
  (hstep : execStmt O passes keinRuf s (M.weltVon u) ρ = Ausgang.ok σ' ρ') (hneu : σ'.spur = neu ++ (M.faeden u).spur)
  (hkein : ∀ (L : D.Lock) (h : List D.Lock), ¬Ereignis.nimmt L h ∈ neu) :
  FadenSA P O passes Q S lok Tg m zyk
      ({ speicher := σ'.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ', (ρ', GRest.dann rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ'.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
        u)
      ({ speicher := σ'.speicher,
            faeden :=
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf :=
                    { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                      rest :=
                        (⟨l,
                            (⟨Γ,
                                (⟨Λ', (ρ', GRest.dann rest k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := σ'.spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.weltVon
        u) ∧
    LogOk P
      ({ speicher := σ'.speicher,
              faeden :=
                rufUpdateG M.faeden u
                  { stapel := (M.faeden u).stapel,
                    kopf :=
                      { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                        rest :=
                          (⟨l,
                              (⟨Γ,
                                  (⟨Λ', (ρ', GRest.dann rest k)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := σ'.spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenSA_blatt hO hQ hlok hFS hF hhead s (.dann rest k)
    (fun O' R U A σ => semHA_dann_cons S O' U A passes R s rest k σ ρ)
    (fun hok => by
      obtain ⟨_, hss, hrest⟩ := okS_dann_cons hok
      exact ⟨hss, hrest⟩) hleaf σ' ρ' hstep, hL⟩

set_option maxHeartbeats 4000000 in
theorem akteurSA_endeEntf {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (s : Stmt D (vertragVon D (M.faeden u).kopf.f) l Γ Λ Λ')
  (rest : Endblock D (vertragVon D (M.faeden u).kopf.f) l Γ Λ') (ρ : Env D Γ) (hent : GEntfaltbar s = true)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.ende (Endblock.cons s rest))⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)) :
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
                                (⟨Λ, (ρ, GRest.dann (Block.cons s Block.nil) (GRest.ende rest))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
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
                                (⟨Λ, (ρ, GRest.dann (Block.cons s Block.nil) (GRest.ende rest))⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }.weltVon
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
                                  (⟨Λ, (ρ, GRest.dann (Block.cons s Block.nil) (GRest.ende rest))⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenSA_lokal hF hhead ρ (.dann (.cons s .nil) (.ende rest)) (M.faeden u).spur
    (fun σ hg hok => ?_), hL⟩
  obtain ⟨hks, hss, hrest⟩ := okS_ende_cons hok
  refine ⟨rfl, hg, ⟨by simp only [Block.gOk, hks, Bool.and_self], ?_, hrest⟩,
    fun R O' U A => ZErgG.folgt_of_eq (semHA_endeEntf S O' U A passes R s rest σ ρ)⟩
  simpa [blockOrteP] using hss

set_option maxHeartbeats 4000000 in
theorem akteurSA_dannLeer {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
  {Q : AxEns D} {S : SperrInv D} {lok : D.Tab ⊕ D.Glob → Bool} {Tg : D.Tab ⊕ D.Glob → Prop} {m : Mass D}
  {zyk : D.Fn → D.Fn → Bool} (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
  (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ (L : D.Lock), S.inv L sp = true)
  (hK : ∀ (f : D.Fn), KoerperGutSA P passes Q S Tg f) (hM : ∀ (f : D.Fn), MassPflicht P passes Q S Tg m zyk f)
  (hTV : ∀ (c : D.Tab ⊕ D.Glob), Tg c → VertragsFrei P c)
  (hFragS : ∀ (f : D.Fn), Endblock.gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) (P.rumpf f) = true)
  (hFS : ∀ (f : D.Fn), FussSX P S lok Tg f) {M : RufMaschineG D} {u : Faden}
  (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
  (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) (hSG : SperrInvG S M)
  (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ)
  (hhead :
    (M.faeden u).kopf.rest =
      (⟨l,
          (⟨Γ,
              (⟨Λ, (ρ, GRest.dann Block.nil k)⟩ :
                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
            (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
        (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)) :
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
                                (⟨Λ, (ρ, k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
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
                                (⟨Λ, (ρ, k)⟩ :
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (l : Bool) ×
                            (Γ : Ctx) ×
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                      RufRahmenG D },
                  spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
            lauf := M.lauf, start := M.start : RufMaschineG D }.weltVon
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
                                  (⟨Λ, (ρ, k)⟩ :
                                    (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                (Γ : Ctx) ×
                                  (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                            (l : Bool) ×
                              (Γ : Ctx) ×
                                (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
                        RufRahmenG D },
                    spur := (M.faeden u).spur, log := (M.faeden u).log : RufFadenG D },
              lauf := M.lauf, start := M.start : RufMaschineG D }.faeden
          u).log := by
  simp only [RufMaschineG.weltVon, rufUpdateG_self]
  refine ⟨fadenSA_lokal hF hhead ρ k (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
  exact ⟨rfl, hg, hok.2.2, fun R O' U A => ZErgG.folgt_refl _⟩

end Gabbro.Grammatik
