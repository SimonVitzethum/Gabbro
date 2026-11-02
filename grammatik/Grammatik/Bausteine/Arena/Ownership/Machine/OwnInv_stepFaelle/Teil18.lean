module

public import Grammatik.Bausteine.Arena.Ownership.Machine.Stack.Return
public import Grammatik.Bausteine.Arena.Ownership.Machine.OwnInv_stepFaelle.Teil17

@[expose] public section

namespace Gabbro.Grammatik.ArenaOwnership.Machine
open Source Body

set_option maxHeartbeats 4000000 in
theorem ownInv_step_dannCallIndElse {D : Deklaration} {P : Programm D}
  {A : FreiForm D} {I : Interfaces A} {O : Orakel D} {passes : Nat} (hO : GutO O) (hc : Checked P A I)
  {M : RufMaschineG D} {u : Faden} (s : State) (hag : s.agrees A (M.speicher.welt []))
  (hfo : A.FreiOk (M.speicher.welt [])) (hd : s.Disciplined (depthOf M))
  (hth : ∀ (t : Faden), ThreadOk A I s (M.speicher.welt []) t (M.faeden t))
  (hW : MetaSame A (M.speicher.welt []) (M.weltVon u)) (ha : s.agrees A (M.weltVon u)) (ho : A.FreiOk (M.weltVon u))
  (hH :
    Head A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) (M.faeden u).kopf.f
      (M.faeden u).kopf.rest)
  (fin :
    ∀ {M' : RufMaschineG D} {σ' : World D}
      {x' : (l : Bool) × (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ}
      {rho' : Env D (D.params (M.faeden u).kopf.f)} {s0' : World D} {spur' : List (Ereignis D)}
      {log' : List (RufEreignisF D)},
      Next A I { thread := u, activation := (M.faeden u).stapel.length : Frame } s (M.weltVon u) σ' (M.faeden u).kopf.f
          x' →
        M'.speicher = σ'.speicher →
          M'.faeden =
              rufUpdateG M.faeden u
                { stapel := (M.faeden u).stapel,
                  kopf := { f := (M.faeden u).kopf.f, rho := rho', s0 := s0', rest := x' : RufRahmenG D },
                  spur := spur', log := log' : RufFadenG D } →
            (∀ (t : Faden),
                t ≠ u →
                  ∀ (g : D.Glob),
                    pendWord A (M.faeden t).kopf.rest.snd.snd.snd.snd = some g →
                      M'.speicher.globs g = M.speicher.globs g) →
              OwnInv A I M')
  (l : Bool) (Γ : Ctx) (Λ Λ' Λ'' : List (Res D)) (τ : Ty) (n : Nat) (p : Expr D Γ Λ (Ty.fnptr n))
  (args : Args D Γ Λ (D.sigNr n).params) (he : (D.sigNr n).erg = some τ)
  (hp : RufPasst D (vertragVon D (M.faeden u).kopf.f) (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
  (err : Endblock D (vertragVon D (M.faeden u).kopf.f) l (.why (D.sigNr n).gruende :: Γ) (nachSig D (D.sigNr n) Λ))
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
  (hΛ : HeldIn Λ (offen (M.faeden u).spur)) (s0 : World D) (hs0 : s0 = (M.weltVon u).lese Λ (p.orte ++ args.orte))
  (g : D.Fn) (hg : D.passt g n = true) (hv : eval s0 p s0 ρ = (⟨g, hg⟩ : { f // D.passt f n = true }))
  (rho : Env D (D.params g)) (hrho : rho = umsig hg (evalArgs s0 args s0 ρ)) (neu : List (Ereignis D))
  (hneu : s0.spur = neu ++ (M.faeden u).spur)
  (hrely :
    ∀ (t : Faden),
      t ≠ u →
        ∀ (g_1 : D.Glob),
          pendWord A (M.faeden t).kopf.rest.snd.snd.snd.snd = some g_1 →
            { speicher := M.speicher,
                      faeden :=
                        rufUpdateG M.faeden u
                          {
                            stapel :=
                              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                                  rest :=
                                    (⟨l,
                                        (⟨Γ,
                                            (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.wartetSonst (D.sigNr n).gruende err
                                              .nil (GRest.dann rest k))⟩ :
                                              (Λ : List (Res D)) ×
                                                Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                          (Γ : Ctx) ×
                                            (Λ : List (Res D)) ×
                                              Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                                      (l : Bool) ×
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) ×
                                            Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
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
                                        (Γ : Ctx) ×
                                          (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) false Γ Λ)⟩ :
                                    (l : Bool) ×
                                      (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D g) l Γ Λ) :
                                RufRahmenG D },
                            spur := s0.spur, log := RufEreignisF.eintritt g rho s0 :: (M.faeden u).log : RufFadenG D },
                      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D }.speicher.globs
                g_1 =
              M.speicher.globs g_1) :
  OwnInv A I
    { speicher := M.speicher,
      faeden :=
        rufUpdateG M.faeden u
          {
            stapel :=
              { f := (M.faeden u).kopf.f, rho := (M.faeden u).kopf.rho, s0 := (M.faeden u).kopf.s0,
                  rest :=
                    (⟨l,
                        (⟨Γ,
                            (⟨nachSig D (D.sigNr n) Λ, (ρ, GRest.wartetSonst (D.sigNr n).gruende err
                              .nil (GRest.dann rest k))⟩ :
                              (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                          (Γ : Ctx) ×
                            (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ)⟩ :
                      (l : Bool) ×
                        (Γ : Ctx) × (Λ : List (Res D)) × Env D Γ × GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) :
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
      lauf := M.lauf ++ rufEigenG u neu, start := M.start : RufMaschineG D } := by
  rw [hhead] at hH
  obtain ⟨k0, c, gh, hk, hf, hor⟩ := head_run hH rfl
  obtain ⟨c2, hs, hcont⟩ := hor.stmt trivial
  obtain ⟨J, owner, hJ, _, _, hplan, herr, rfl⟩ := os_top hs
  subst hrho
  have hR : Realizes c gh A ⟨u, (M.faeden u).stapel.length⟩ s (M.speicher.welt []) ρ :=
    ⟨hag, hfo, hf.1, hf.2.1, hf.2.2.1⟩
  obtain ⟨hJm, hJo⟩ := hJ g hg
  have hdrop : (resultContextB (c.afterCall (modeList J) (originList c args)) owner).drop =
      dropContextB (c.afterCall (modeList J) (originList c args)) owner := by
    cases owner <;> simp [resultContextB, dropContextB, Context.drop, Context.bind, Context.bindFresh]
  have hrwait : OR A I (I (M.faeden u).kopf.f).output k
      (resultContextB (c.afterCall (modeList J) (originList c args)) owner)
      (.dann (.nil : Block D (vertragVon D (M.faeden u).kopf.f) l (τ :: Γ) (nachSig D (D.sigNr n) Λ)
        (nachSig D (D.sigNr n) Λ)) (.schrumpf (.dann rest k))) := by
    apply OR.of_cont (.nil)
    apply Cont.schrumpf hk
    rw [hdrop]
    exact hcont
  rw [← hJo] at hrwait
  exact ownInv_push hc hag hfo hd hth hf hplan hk (callee_ind hg hJm hd rfl hR hplan s0 s0)
    (.wartetSonst _ _ _ _ hrwait (OR.sonst herr (.schrumpf _ hk hcont.exits))) rfl rfl

end Gabbro.Grammatik.ArenaOwnership.Machine
