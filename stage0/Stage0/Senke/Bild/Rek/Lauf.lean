/-
  File:      stage0/Stage0/Senke/Bild/Rek/Lauf.lean
  Subject:   **Boundaries inside a callee, both sides** (package P4 of the closed calls of the image theorem, part 3).
             `randL_ruf_eintritt` joins the image side (`randIR_ruf_eintritt`) and machine G (`randGL_ruf_eintritt`)
             at the callee's first body boundary: from a caller's boundary `RandL` (frame `rumpfRahmen` at depth
             `k = j + 1`) in front of a plain call that ends normally, the image reaches a boundary `RandL` of the
             callee's body in its frame at depth `j`, machine G one `ruf` step further, with the caller frame waiting
             on the thread's stack. Inside the callee, P3's `korrespondenzL_lauf` runs at depth `j` with the callee's
             own decomposed prefix and its own call obligation `RufOkGleich (rufAt j)`: `korrespondenz_rek`. With the
             checker's facts, the goal legs hold at every machine reached inside the callee (`bild_ziel_rek`).

             The callee's decomposed prefix is a premise stated in a frame that fixes only what `Zerlegung` reads
             (`rufZRahmen`; `zerlegung_rahmen` moves it into the callee's real frame), so it names no image address.
             The conclusion has the shape of the premise one level down (`RandL` at a `rumpfRahmen` boundary, a
             machine `thr` reaches): at a boundary of the callee in front of a further call, the descent applies
             again, at depth `j - 1`. That is the recursion: every boundary on the way down, also of a callee that
             calls itself, corresponds -- the descent needs NO call obligation for the call it descends into. The
             return to the caller (stepping OVER a call inside the caller's prefix) needs the caller's
             `RufOkGleich`, which `rufOk_gleich_tief` supplies for the callees in `Tief` (`Rek/Tief.lean`).
-/
module
public import Stage0.Senke.Bild.Rek.Eintritt
public import Stage0.Senke.Bild.Ruf.ZielL
public import Stage0.Senke.Bild.Emitted
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-- **The frame in which a callee's decomposed prefix is stated**: `Zerlegung` reads only the oracle, the pass budget,
    the depth, the program and the function of a `rumpfRahmen` (`zerlegung_rahmen`); the rest is fixed. -/
abbrev rufZRahmen (Y : Lay D) (O : Orakel D) (passes : Nat) (P : Programm D) (A : D.Fn → Nat) (j : Nat)
    (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) : BodyFrame D :=
  rumpfRahmen Y O passes P A (fun _ => []) 0 j g 0 0 0 0 0 σ ρ [] ([], 0)

variable [Kern]

/-- **An image state inside a callee's body, one level down**: inside a decomposed step of the callee's body
    (`KorrespondenzL` in the callee's frame `B`, to a machine with `Z`), or behind the callee's decomposed prefix
    (`RandL` at its end `ebe`, at a machine with `Z`, the state reached from there by memory-only steps). -/
def ImRumpf (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D)) (rho : Env D (D.params B.f))
    (s0 : World D) (Agl : D.Lock → Prop) {Γe : Ctx} {Λe : List (Res D)}
    (ebe : Endblock D (vertragVon D B.f) false Γe Λe) (σe : World D) (ρe : Env D Γe)
    (Z : RufMaschineG D → Prop) (t : T) (m : Runner.Mem) : Prop :=
  (∃ M', KorrespondenzL B thr stapel rho s0 Agl false t m M' ∧ Z M') ∨
  (∃ (pce : Runner.W) (me : Runner.Mem) (Me : RufMaschineG D),
    RandL B thr stapel rho s0 Agl ebe pce me Me σe ρe ∧ Z Me ∧ ∃ k, StarM k ⟨pce, B.fp⟩ me t m)

/-- **Into the callee, both sides**: from a caller's boundary (frame `rumpfRahmen` at depth `k = j + 1`) in front of
    a plain call `g(args); rest` that ends normally under `rufAt k`, the image runs to the callee's first body
    boundary and thread `thr` takes the step `ruf`; there the callee's boundary corresponds (`RandL` in the callee's
    frame at depth `j`, which satisfies `BodyFrame.Ok`), the caller frame waiting on the thread's stack. -/
theorem randL_ruf_eintritt {Y : Lay D} {O : Orakel D} [TorOK Y O] [SichtOK O] {passes : Nat}
    {P : Programm D} {A : D.Fn → Nat} {C : D.Fn → List II} {Lm : Nat} (hc : BildCodes Y P passes A C Lm)
    {k j : Nat} (hkj : k = j + 1) (hk64 : k < 2 ^ 64) {f : D.Fn} {fp : Runner.W} {K Ks : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {H : List D.Lock} {ens : List II × Nat}
    (hB : (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens).Ok)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (h : RandL (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens) thr stapel rho s0 Agl
      (.cons (.call g args hp hr) rest) pc m M σ ρ)
    (hex : execStmt O passes (rufAt P O passes k)
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ1 ρ1) :
    ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (pcI : Runner.W) (mI : Runner.Mem)
      (M1 : RufMaschineG D) (σm : World D),
      Star ⟨pc, fp⟩ m ⟨pcI, fpc⟩ mI ∧ RufLaufG P O passes thr M M1 ∧
      WeltGleich (σ.lese Λ args.orte) σm ∧
      (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) H
        ensc).Ok ∧
      RandL (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
          (rufEnv g σ Λ args ρ) H ensc) thr (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm
        Agl (P.rumpf g) pcI mI M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) := by
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, hs, hOk, hR⟩ := randIR_ruf_eintritt hc hkj hk64 hB h.1 hex
  obtain ⟨M1, σm, hl, hw, hG⟩ := randGL_ruf_eintritt (P := P) (O := O) (passes := passes) h.2
  exact ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, hs, hl, hw, hOk, hR, hG⟩

/-- **THE CORRESPONDENCE INSIDE A CALLEE (T1 one level down, one thread).** From a caller's boundary in front of a
    plain call that ends normally, the image reaches the callee's first body boundary, which corresponds to a
    machine `thr` reaches; from there every memory-only prefix of the image run lies inside a decomposed step of the
    callee's body and corresponds to a machine `thr` reaches, or has passed the callee's decomposed prefix, whose end
    boundary corresponds to such a machine (`korrespondenzL_lauf` in the callee's frame at depth `j`, with the
    callee's own call obligation `hRufC` for `rufAt j`). -/
theorem korrespondenz_rek {Y : Lay D} {O : Orakel D} [TorOK Y O] [SichtOK O] [LeseblindOK O] {passes : Nat}
    {P : Programm D} {A : D.Fn → Nat} {C : D.Fn → List II} {Lm : Nat} (hc : BildCodes Y P passes A C Lm)
    {k j : Nat} (hkj : k = j + 1) (hk64 : k < 2 ^ 64) {f : D.Fn} {fp : Runner.W} {K Ks : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {H : List D.Lock} {ens : List II × Nat}
    (hB : (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens).Ok)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (h : RandL (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens) thr stapel rho s0 Agl
      (.cons (.call g args hp hr) rest) pc m M σ ρ)
    (hex : execStmt O passes (rufAt P O passes k)
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ1 ρ1)
    {CgC : D.Fn → Prop} (hRufC : RufOkGleich P O passes thr Agl (rufAt P O passes j) CgC)
    {ΓeC : Ctx} {ΛeC : List (Res D)} {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D}
    {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl CgC
      (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (pcI : Runner.W) (mI : Runner.Mem)
      (M1 : RufMaschineG D) (σm : World D),
      Star ⟨pc, fp⟩ m ⟨pcI, fpc⟩ mI ∧ RufLaufG P O passes thr M M1 ∧
      RandL (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
          (rufEnv g σ Λ args ρ) H ensc) thr (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm
        Agl (P.rumpf g) pcI mI M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ∧
      ∀ {n : Nat} {t : T} {m' : Runner.Mem}, StarM n ⟨pcI, fpc⟩ mI t m' →
        ImRumpf (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
            (rufEnv g σ Λ args ρ) H ensc) thr (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm
          Agl ebeC σeC ρeC (fun M' => RufLaufG P O passes thr M M') t m' := by
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, hs, hl, _, hOk, hR⟩ :=
    randL_ruf_eintritt (thr := thr) (stapel := stapel) (Agl := Agl) hc hkj hk64 hB h hex
  have hkC' : Zerlegung (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
      (rufEnv g σ Λ args ρ) H ensc) Agl CgC (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)
      ebeC σeC ρeC :=
    zerlegung_rahmen hkC
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, hs, hl, hR, ?_⟩
  intro n t m' hrun
  rcases korrespondenzL_lauf hOk hRufC hkC' hR hrun with ⟨M', hl', hK⟩ | ⟨pce, me, Me, hRe, hle, k', hk'⟩
  · exact Or.inl ⟨M', hK, hl.trans hl'⟩
  · exact Or.inr ⟨pce, me, Me, hRe, hl.trans hle, k', hk'⟩

/-- **THE GOAL LEGS INSIDE A CALLEE (T1 one level down, one thread).** `korrespondenz_rek` under the checker's facts
    (a′), the user's logic (b), the named hardware assumptions (c), an admissible start (d′) and a read-blind oracle:
    when the caller's boundary corresponds to a reachable machine, the callee's first body boundary corresponds to a
    reachable machine at which every leg of `Ziel` holds, and so does every machine an image state inside the
    callee's decomposed prefix corresponds to (`ImRumpf` with reachability and `Ziel`). -/
theorem bild_ziel_rek [DecidableEq D.Fn] {Y : Lay D} {O : Orakel D} [TorOK Y O] [SichtOK O] [LeseblindOK O]
    {passes : Nat} {P : Programm D} {A : D.Fn → Nat} {C : D.Fn → List II} {Lm : Nat}
    (hc : BildCodes Y P passes A C Lm) {S : SperrInv D} {Q : AxEns D} {fs : Aufzaehlung D.Fn}
    (ls : Aufzaehlung D.Lock) {ws : List D.Fn} {Acc : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec P S fs.1 ws Acc) (hN : LogikPflicht P S Q) (hH : HardwareAnnahmen O Q)
    {sp : Speicher D} {init : Faden → Σ g : D.Fn, Env D (D.params g)} (hZ : StartZulaessig P S fs.1 ws sp init)
    {k j : Nat} (hkj : k = j + 1) (hk64 : k < 2 ^ 64) {f : D.Fn} {fp : Runner.W} {K Ks : Nat}
    {rp cfp : Runner.W} {σ0 : World D} {ρ0 : Env D (D.params f)} {H : List D.Lock} {ens : List II × Nat}
    (hB : (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens).Ok)
    {thr : Faden} {stapel : List (RufRahmenG D)} {rho : Env D (D.params f)} {s0 : World D}
    {Agl : D.Lock → Prop} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {hp : RufPasst D (vertragVon D f) (D.signatur g) Λ} {hr : D.gruende g = 0}
    {rest : Endblock D (vertragVon D f) l Γ (nach D g Λ)} {pc : Runner.W} {m : Runner.Mem}
    {M : RufMaschineG D} {σ σ1 : World D} {ρ ρ1 : Env D Γ}
    (hM : RufErreichbarG P O passes (RufStartG P sp init) M)
    (h : RandL (rumpfRahmen Y O passes P A C Lm k f fp K Ks rp cfp σ0 ρ0 H ens) thr stapel rho s0 Agl
      (.cons (.call g args hp hr) rest) pc m M σ ρ)
    (hex : execStmt O passes (rufAt P O passes k)
      (.call g args hp hr : Stmt D (vertragVon D f) l Γ Λ (nach D g Λ)) σ ρ = .ok σ1 ρ1)
    {CgC : D.Fn → Prop} (hRufC : RufOkGleich P O passes thr Agl (rufAt P O passes j) CgC)
    {ΓeC : Ctx} {ΛeC : List (Res D)} {ebeC : Endblock D (vertragVon D g) false ΓeC ΛeC} {σeC : World D}
    {ρeC : Env D ΓeC}
    (hkC : Zerlegung (rufZRahmen Y O passes P A j g (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)) Agl CgC
      (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ebeC σeC ρeC) :
    ∃ (fpc rpc : Runner.W) (Kc Ksc : Nat) (ensc : List II × Nat) (pcI : Runner.W) (mI : Runner.Mem)
      (M1 : RufMaschineG D) (σm : World D),
      Star ⟨pc, fp⟩ m ⟨pcI, fpc⟩ mI ∧
      RandL (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
          (rufEnv g σ Λ args ρ) H ensc) thr (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm
        Agl (P.rumpf g) pcI mI M1 (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ) ∧
      RufErreichbarG P O passes (RufStartG P sp init) M1 ∧ Ziel P S O passes (RufStartG P sp init) M1 ∧
      ∀ {n : Nat} {t : T} {m' : Runner.Mem}, StarM n ⟨pcI, fpc⟩ mI t m' →
        ImRumpf (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
            (rufEnv g σ Λ args ρ) H ensc) thr (rufRahmenNach rho s0 ρ rest :: stapel) (rufEnv g σ Λ args ρ) σm
          Agl ebeC σeC ρeC
          (fun M' => RufErreichbarG P O passes (RufStartG P sp init) M' ∧
            Ziel P S O passes (RufStartG P sp init) M') t m' := by
  obtain ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, hs, hl, _, hOk, hR⟩ :=
    randL_ruf_eintritt (thr := thr) (stapel := stapel) (Agl := Agl) hc hkj hk64 hB h hex
  have hM1 := rufErreichbar_lauf hl hM
  have hkC' : Zerlegung (rumpfRahmen Y O passes P A C Lm j g fpc Kc Ksc rpc fp (rufWelt P g σ Λ args)
      (rufEnv g σ Λ args ρ) H ensc) Agl CgC (P.rumpf g) (rufWelt P g σ Λ args) (rufEnv g σ Λ args ρ)
      ebeC σeC ρeC :=
    zerlegung_rahmen hkC
  refine ⟨fpc, rpc, Kc, Ksc, ensc, pcI, mI, M1, σm, hs, hR, hM1,
    ziel_aus P S Q fs ls ws hA hN O hH passes sp init hZ M1 hM1, ?_⟩
  intro n t m' hrun
  rcases bild_ziel_seqL (ls := ls) hOk hA hN hH hZ hRufC hkC' hM1 hR hrun with
    ⟨M', hK, hr', hz'⟩ | ⟨pce, me, Me, hRe, hre, hze, k', hk'⟩
  · exact Or.inl ⟨M', hK, hr', hz'⟩
  · exact Or.inr ⟨pce, me, Me, hRe, ⟨hre, hze⟩, k', hk'⟩

#print axioms korrespondenz_rek
#print axioms bild_ziel_rek

end Gabbro.Stage0.Senke.BildLauf
