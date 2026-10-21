/- Part 5 of 10 of `RufAdaequatRufG` (split by instrumente/teile/lean-teilen.py; the umbrella `RufAdaequatRufG.lean` imports all parts). -/
import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T4

namespace Gabbro.Grammatik

variable {D : Deklaration}

section SimOk

variable (P : Programm D) (O : Orakel D) (passes : Nat) (f : Faden) (fn : D.Fn)
  (stapel : List (RufRahmenG D)) (rho : Env D (D.params fn)) (s0 : World D)
  (A : D.Lock → Prop) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  (C : D.Fn → Prop)

/-- Block simulation, normal completion: `dann b k` at `σ, ρ` runs (steps of
    `f` only) to `k` at the world and environment `execBlock` returns; the
    log grows by the events of the calls made on the way (`ext`). -/
def SimOkBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execBlock O passes R b σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldB (vertragVon D fn).boden Λ (offen σ.spur) →
    FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur

/-- Statement simulation, normal completion: `dann (s; rest) k` runs to
    `dann rest k`. -/
def SimOkSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
    execStmt O passes R s σ ρ = .ok σ' ρ' →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann rest k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- Block simulation, abrupt exit: `dann b k` at `σ, ρ`, inside a loop
    (`hl`), runs to the exit statement of the kind `execBlock` exits with,
    standing directly above `k` (every scaffolding layer the block built on
    the way is peeled, a `frei` layer releasing its lock), at the world and
    environment of the exit. -/
def SimAbbBR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (hl : l = true) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ) (w : Bool),
    (execBlock O passes R b σ ρ).abb? = some (w, σ', ρ') →
  ∀ (M : RufMaschineG D) (k : GRest D (vertragVon D fn) l Γ Λ'),
    ZustandG M f stapel fn rho s0 log ρ (.dann b k) σ → HeldB (vertragVon D fn).boden Λ (offen σ.spur) →
    FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
      (r : Block D (vertragVon D fn) l Γ Λx Λ'), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS hl w) r) k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- Statement simulation, abrupt exit: `dann (s; rest) k` runs to the exit
    statement directly above `k` (the `dann rest` layer is peeled too). -/
def SimAbbSR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ') : Prop :=
  ∀ (hl : l = true) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ) (w : Bool),
    (execStmt O passes R s σ ρ).abb? = some (w, σ', ρ') →
  ∀ (M : RufMaschineG D) {Λ'' : List (Res D)}
    (rest : Block D (vertragVon D fn) l Γ Λ' Λ'') (k : GRest D (vertragVon D fn) l Γ Λ''),
    ZustandG M f stapel fn rho s0 log ρ (.dann (.cons s rest) k) σ →
    HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
    ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
      (r : Block D (vertragVon D fn) l Γ Λx Λ''), RufLaufG P O passes f M M' ∧
      ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS hl w) r) k) σ' ∧
      offen σ'.spur = offen σ.spur

/-- A covered leaf: one `dannBlatt` step. -/
theorem blattOkR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimOkSR P O passes f fn stapel rho s0 A R s := by
  intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ _
  have hW := hZ.welt
  have herw := h.erw O passes R σ σ' ρ ρ' hex
  obtain ⟨M', hs, hZ'⟩ := w_dannBlatt (P := P) (O := O) (passes := passes) hZ.1 s rest k ρ
    h.istBlatt rfl hΛ.heldIn σ' ρ' (by rw [hW, ← h.exec_R O passes R]; exact hex) (by rw [hW]; exact herw)
  exact ⟨M', [], RufLaufG.einzeln hs, hZ', herw.offen⟩

/-- A covered leaf never exits abruptly. -/
theorem blattAbbR {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {s : Stmt D (vertragVon D fn) l Γ Λ Λ'} (h : BlattG s) :
    SimAbbSR P O passes f fn stapel rho s0 A R s := by
  intro _ log σ σ' ρ ρ' w hex
  rw [abb_none_of (h.ohneAbbruch O passes R σ ρ)] at hex
  cases hex

/-- A `schrumpf` layer after a sub-block: one `schrumpfVergiss` step. -/
theorem schrumpfOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {M : RufMaschineG D} {log : List (RufEreignisF D)} {k : GRest D (vertragVon D fn) l Γ Λ}
    {v : Wert D τ} {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log (.cons v ρ) (.schrumpf k) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧ ZustandG M' f stapel fn rho s0 log ρ k σ := by
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_schrumpf (P := P) (O := O) (passes := passes) hZ.1 k v ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

/-- An abrupt exit above a `dann` layer: one peel. -/
theorem peelDannR {l : Bool} {Γ : Ctx} {Λ Λ1 Λ2 : List (Res D)} {M : RufMaschineG D}
    {log : List (RufEreignisF D)} (hl : l = true) {w : Bool}
    {r : Block D (vertragVon D fn) l Γ Λ Λ1}
    {b : Block D (vertragVon D fn) l Γ Λ1 Λ2} {k : GRest D (vertragVon D fn) l Γ Λ2}
    {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) r) (.dann b k)) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) .nil) k) σ := by
  subst hl
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_peelDann (P := P) (O := O) (passes := passes) hZ.1 w r b k ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

/-- An abrupt exit above a `schrumpf` layer: one peel, the binding dropped. -/
theorem peelSchrumpfR {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {τ : Ty} {M : RufMaschineG D}
    {log : List (RufEreignisF D)} (hl : l = true) {w : Bool}
    {r : Block D (vertragVon D fn) l (τ :: Γ) Λ Λ1}
    {k : GRest D (vertragVon D fn) l Γ Λ1} {ρ : Env D (τ :: Γ)} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) r) (.schrumpf k)) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f stapel fn rho s0 log ρ.tail (.dann (.cons (abbS hl w) .nil) k) σ := by
  subst hl
  have hW := hZ.welt
  cases ρ with
  | cons v ρt =>
    obtain ⟨M', hs, hZ'⟩ := w_peelSchrumpf (P := P) (O := O) (passes := passes) hZ.1 w r k v ρt rfl
    rw [hW] at hZ'
    exact ⟨M', hs, hZ'⟩

/-- An abrupt exit above a `frei` layer: one peel, the lock released. -/
theorem peelFreiR {l : Bool} {Γ : Ctx} {Λ Λ1 : List (Res D)} {M : RufMaschineG D}
    {log : List (RufEreignisF D)} (hl : l = true) {w : Bool} {L : D.Lock}
    {r : Block D (vertragVon D fn) l Γ Λ (Res.held L :: Λ1)}
    {k : GRest D (vertragVon D fn) l Γ Λ1} {ρ : Env D Γ} {σ : World D}
    (hZ : ZustandG M f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) r) (.frei L k)) σ) :
    ∃ M', RufSchrittG P O passes M f M' ∧
      ZustandG M' f stapel fn rho s0 log ρ (.dann (.cons (abbS hl w) .nil) k) (σ.gibt L) := by
  subst hl
  have hW := hZ.welt
  obtain ⟨M', hs, hZ'⟩ := w_peelFrei (P := P) (O := O) (passes := passes) hZ.1 w L r k ρ rfl
  rw [hW] at hZ'
  exact ⟨M', hs, hZ'⟩

/-- **The loop of a `traverse`, normal completion.** From `trav t inv body ks
    k` the machine runs to `k` exactly as `traverseLauf` over `ks` ends
    normally: one invariant read (`travNext`) before each iteration, the
    body by its simulation -- normal completion (`travFort`), `next`
    (`dannNextTrav`, the next index) or `leave` (`dannLeaveTrav`, the
    invariant read, the loop left) -- and one read after the last
    iteration (`travDone`). -/
theorem travOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (inv : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true (.index (D.count t) :: Γ) Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (ks : List (Wert D (.index (D.count t)))) (log : List (RufEreignisF D))
      (σ σ' : World D) (ρ ρ' : Env D Γ),
      traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
          (σ.lese Λ inv.orte) ρ))) ks σ ρ = .ok σ' ρ' →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.trav t inv body ks k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur
  | [], log, σ, σ', ρ, ρ', hex, M, hZ, _, _ => by
      have hW := hZ.welt
      simp only [traverseLauf] at hex
      split at hex
      · rename_i hw
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_travDone (P := P) (O := O) (passes := passes) hZ.1
          t inv body k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, (Erw.lese _ _ _).offen⟩
      · cases hex
  | i :: is, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [traverseLauf] at hex
      split at hex
      · cases hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_travNext (P := P) (O := O) (passes := passes) hZ.1
          t inv body i is k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese inv.orte hΛ (Λ₀ := Λ)
        -- the loop continues at `trav … is k`
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρt : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρt (.trav t inv body is k) σ2 →
            offen σ2.spur = offen σ.spur →
            traverseLauf (l := l) (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
                (σ.lese Λ inv.orte) ρ))) is σ2 ρt = .ok σ' ρ' →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρt hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, hr4, hZ4, ho4⟩ := travOkR t inv body hbody hbodyA k is _ σ2 σ' ρt ρ'
            hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          cases ρ2 with
          | cons i2 ρt =>
            have hW2 := hZ2.welt
            obtain ⟨M3, hs3, hZ3⟩ := w_travFort (P := P) (O := O) (passes := passes) hZ2.1
              t inv body is k i2 ρt rfl
            rw [hW2] at hZ3
            exact weiter M3 e2 σ2 ρt (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
              hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          cases ρ2 with
          | cons i2 ρt =>
            have hW2 := hZ2.welt
            obtain ⟨M3, hs3, hZ3⟩ := w_nextTrav (P := P) (O := O) (passes := passes) hZ2.1
              t inv body is k r i2 ρt rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
            rw [hW2] at hZ3
            exact weiter M3 e2 σ2 ρt (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
              hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          split at hex
          · rename_i hw2
            simp only [Ausgang.ok.injEq] at hex
            obtain ⟨rfl, rfl⟩ := hex
            obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ true
              (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
            cases ρ2 with
            | cons i2 ρt =>
              have hW2 := hZ2.welt
              obtain ⟨M3, hs3, hZ3⟩ := w_leaveTrav (P := P) (O := O) (passes := passes) hZ2.1
                t inv body is k r i2 ρt rfl (by rw [hW2]; simpa [Env.tail] using hw2) (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
              rw [hW2] at hZ3
              exact ⟨M3, e2, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
                by rw [(Erw.lese _ _ _).offen, ho2, (Erw.lese _ _ _).offen]⟩
          · cases hex
        all_goals cases hex

/-- **The loop of a `retry`, normal completion.** From `wieder n bis body
    ueber k` the machine runs to `k` exactly as `retryLauf` with bound `n`
    ends normally: at bound `0` the check `if bis {} else { overflow }`
    (`wiederUeber`, then the `if` and the overflow block), a read
    of `bis` before each try (`wiederWeiter` on `true`, `wiederSchritt`
    into the body on `false`), the body to its normal end (`wiederFort`),
    to `next` (`dannNextWieder`, the next try) or to `leave`
    (`dannLeaveWieder`, the loop left). -/
theorem retryOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true Γ Λ Λ) (ueber : Block D (vertragVon D fn) l Γ Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (hueber : SimOkBR P O passes f fn stapel rho s0 A R ueber)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
      retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
          (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ = .ok σ' ρ' →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.wieder n bis body ueber k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur
  | 0, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_wiederUeber (P := P) (O := O) (passes := passes) hZ.1
        bis body ueber k ρ rfl
      rw [hW] at hZ1
      have hW1 := hZ1.welt
      have hA1 := hA.lauf (RufLaufG.einzeln hs1)
      split at hex
      · rename_i hw
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M2, hs2, hZ2⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ1.1
          bis .nil ueber .nil k ρ rfl (by rw [hW1]; simpa using hw)
        rw [hW1] at hZ2
        obtain ⟨M3, hs3, hZ3⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ2.1 _ ρ rfl
        rw [hZ2.welt] at hZ3
        obtain ⟨M4, hs4, hZ4⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ3.1 _ ρ rfl
        rw [hZ3.welt] at hZ4
        exact ⟨M4, [], RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (RufLaufG.schritt hs3
          (RufLaufG.einzeln hs4))), hZ4, (Erw.lese _ _ _).offen⟩
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M2, hs2, hZ2⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ1.1
          bis .nil ueber .nil k ρ rfl (by rw [hW1]; exact hw')
        rw [hW1] at hZ2
        obtain ⟨M3, e3, hr3, hZ3, ho3⟩ := hueber log _ _ _ _ hex M2 _ hZ2
          (heldB_lese bis.orte hΛ (Λ₀ := Λ)) (hA1.lauf (RufLaufG.einzeln hs2))
        obtain ⟨M4, hs4, hZ4⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ3.1 k ρ' rfl
        rw [hZ3.welt] at hZ4
        exact ⟨M4, e3, RufLaufG.schritt hs1 (RufLaufG.schritt hs2 (hr3.trans (RufLaufG.einzeln hs4))),
          hZ4, by rw [ho3, (Erw.lese _ _ _).offen]⟩
  | n + 1, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · rename_i hw
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederWeiter (P := P) (O := O) (passes := passes) hZ.1
          n bis body ueber k ρ rfl (by rw [hW]; exact hw)
        rw [hW] at hZ1
        exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, (Erw.lese _ _ _).offen⟩
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederSchritt (P := P) (O := O) (passes := passes) hZ.1
          n bis body ueber k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese bis.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρ2 : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρ2 (.wieder n bis body ueber k) σ2 →
            offen σ2.spur = offen σ.spur →
            retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
                (σ.lese Λ bis.orte) ρ)))
              (fun σ ρ => execBlock O passes R ueber σ ρ) n σ2 ρ2 = .ok σ' ρ' →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, hr4, hZ4, ho4⟩ := retryOkR bis body ueber hbody hbodyA hueber k n _ σ2
            σ' ρ2 ρ' hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_wiederFort (P := P) (O := O) (passes := passes) hZ2.1
            n bis body ueber k ρ2 rfl
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbWieder (P := P) (O := O) (passes := passes) hZ2.1
            false n bis body ueber k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          simp only [Ausgang.ok.injEq] at hex
          obtain ⟨hσ, hρ⟩ := hex
          subst hσ hρ
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ true
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbWieder (P := P) (O := O) (passes := passes) hZ2.1
            true n bis body ueber k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact ⟨M3, e2, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        all_goals cases hex

/-- **The loop of a `forever`, normal completion.** From `ewig a n inv body
    k` the machine runs to `k` exactly as `foreverLauf` with `n` passes left
    ends normally -- which it does only by `leave`: a read of the invariant
    before each pass (`ewigWeiter`, only on `true`), the body to its normal
    end (`ewigFort`) or to `next` (`dannNextEwig`), each spending one pass,
    and finally `leave` (`dannLeaveEwig`). -/
theorem foreverOkR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (a : D.Annahme)
    (inv : Expr D Γ Λ .bool) (body : Block D (vertragVon D fn) true Γ Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ),
      foreverLauf (l := l) a (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
          (σ.lese Λ inv.orte) ρ))) n σ ρ = .ok σ' ρ' →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.ewig a n inv body k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧ offen σ'.spur = offen σ.spur
  | 0, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      simp only [foreverLauf] at hex
      cases hex
  | n + 1, log, σ, σ', ρ, ρ', hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [foreverLauf] at hex
      split at hex
      · cases hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = true := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_ewigWeiter (P := P) (O := O) (passes := passes) hZ.1
          a n inv body k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese inv.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρ2 : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρ2 (.ewig a n inv body k) σ2 →
            offen σ2.spur = offen σ.spur →
            foreverLauf (l := l) a (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ inv.orte), wahr? (eval (σ.lese Λ inv.orte) inv
                (σ.lese Λ inv.orte) ρ))) n σ2 ρ2 = .ok σ' ρ' →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' k σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, hr4, hZ4, ho4⟩ := foreverOkR a inv body hbody hbodyA k n _ σ2 σ' ρ2 ρ'
            hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_ewigFort (P := P) (O := O) (passes := passes) hZ2.1
            a n inv body k ρ2 rfl
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbEwig (P := P) (O := O) (passes := passes) hZ2.1
            false a n inv body k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          simp only [Ausgang.ok.injEq] at hex
          obtain ⟨hσ, hρ⟩ := hex
          subst hσ hρ
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ true
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbEwig (P := P) (O := O) (passes := passes) hZ2.1
            true a n inv body k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact ⟨M3, e2, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        all_goals cases hex

/-- **A `retry` exits abruptly only through its overflow block.** Inside an
    outer loop, `retryLauf` ends in `leave`/`next` only where the overflow
    block does (the body's own exits are consumed); the machine runs the
    tries as `retryOkR` does and then the overflow block to its exit. -/
theorem retryAbbR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (hl : l = true)
    (bis : Expr D Γ Λ .bool)
    (body : Block D (vertragVon D fn) true Γ Λ Λ) (ueber : Block D (vertragVon D fn) l Γ Λ Λ)
    (hbody : SimOkBR P O passes f fn stapel rho s0 A R body)
    (hbodyA : SimAbbBR P O passes f fn stapel rho s0 A R body)
    (hueberA : SimAbbBR P O passes f fn stapel rho s0 A R ueber)
    (k : GRest D (vertragVon D fn) l Γ Λ) :
    ∀ (n : Nat) (log : List (RufEreignisF D)) (σ σ' : World D) (ρ ρ' : Env D Γ) (w : Bool),
      (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
          (σ.lese Λ bis.orte) ρ)))
        (fun σ ρ => execBlock O passes R ueber σ ρ) n σ ρ).abb? = some (w, σ', ρ') →
      ∀ (M : RufMaschineG D), ZustandG M f stapel fn rho s0 log ρ (.wieder n bis body ueber k) σ →
        HeldB (vertragVon D fn).boden Λ (offen σ.spur) → FreiA A M f →
        ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
          (r : Block D (vertragVon D fn) l Γ Λx Λ), RufLaufG P O passes f M M' ∧
          ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS hl w) r) k) σ' ∧
          offen σ'.spur = offen σ.spur
  | 0, log, σ, σ', ρ, ρ', w, hex, M, hZ, hΛ, hA => by
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · simp [Ausgang.abb?] at hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederUeber (P := P) (O := O) (passes := passes) hZ.1
          bis body ueber k ρ rfl
        rw [hW] at hZ1
        have hW1 := hZ1.welt
        obtain ⟨M2, hs2, hZ2⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ1.1
          bis .nil ueber .nil k ρ rfl (by rw [hW1]; exact hw')
        rw [hW1] at hZ2
        obtain ⟨M3, e3, Λx, r, hr3, hZ3, ho3⟩ := hueberA hl log _ _ _ _ w hex M2 _ hZ2
          (heldB_lese bis.orte hΛ (Λ₀ := Λ))
          ((hA.lauf (RufLaufG.einzeln hs1)).lauf (RufLaufG.einzeln hs2))
        obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
        exact ⟨M4, e3, Λ, .nil, RufLaufG.schritt hs1 (RufLaufG.schritt hs2
          (hr3.trans (RufLaufG.einzeln hs4))), hZ4, by rw [ho3, (Erw.lese _ _ _).offen]⟩
  | n + 1, log, σ, σ', ρ, ρ', w, hex, M, hZ, hΛ, hA => by
      subst hl
      have hW := hZ.welt
      simp only [retryLauf] at hex
      split at hex
      · simp [Ausgang.abb?] at hex
      · rename_i hw
        have hw' : wahr? (eval (σ.lese Λ bis.orte) bis (σ.lese Λ bis.orte) ρ) = false := by
          simpa using hw
        obtain ⟨M1, hs1, hZ1⟩ := w_wiederSchritt (P := P) (O := O) (passes := passes) hZ.1
          n bis body ueber k ρ rfl (by rw [hW]; exact hw')
        rw [hW] at hZ1
        have hA1 := hA.lauf (RufLaufG.einzeln hs1)
        have hΛ1 := heldB_lese bis.orte hΛ (Λ₀ := Λ)
        have weiter : ∀ (M3 : RufMaschineG D) (e3 : List (RufEreignisF D)) (σ2 : World D)
            (ρ2 : Env D Γ), RufLaufG P O passes f M M3 →
            ZustandG M3 f stapel fn rho s0 (e3 ++ log) ρ2 (.wieder n bis body ueber k) σ2 →
            offen σ2.spur = offen σ.spur →
            (retryLauf (fun σ ρ => execBlock O passes R body σ ρ)
              (fun σ ρ => ((σ.lese Λ bis.orte), wahr? (eval (σ.lese Λ bis.orte) bis
                (σ.lese Λ bis.orte) ρ)))
              (fun σ ρ => execBlock O passes R ueber σ ρ) n σ2 ρ2).abb? = some (w, σ', ρ') →
            ∃ (M' : RufMaschineG D) (ext : List (RufEreignisF D)) (Λx : List (Res D))
              (r : Block D (vertragVon D fn) true Γ Λx Λ), RufLaufG P O passes f M M' ∧
              ZustandG M' f stapel fn rho s0 (ext ++ log) ρ' (.dann (.cons (abbS rfl w) r) k) σ' ∧
              offen σ'.spur = offen σ.spur := by
          intro M3 e3 σ2 ρ2 hl3 hZ3 ho3 hex3
          have hΛ3 : HeldB (vertragVon D fn).boden Λ (offen σ2.spur) := by rw [ho3]; exact hΛ
          obtain ⟨M4, e4, Λx, r, hr4, hZ4, ho4⟩ := retryAbbR rfl bis body ueber hbody hbodyA hueberA
            k n _ σ2 σ' ρ2 ρ' w hex3 M3 hZ3 hΛ3 (hA.lauf hl3)
          exact ⟨M4, e4 ++ e3, Λx, r, hl3.trans hr4, by rw [List.append_assoc]; exact hZ4,
            by rw [ho4, ho3]⟩
        split at hex
        · rename_i σ2 ρ2 hb2
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hbody log _ _ _ _ hb2 M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_wiederFort (P := P) (O := O) (passes := passes) hZ2.1
            n bis body ueber k ρ2 rfl
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · rename_i h2 σ2 ρ2 hb2
          obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hbodyA rfl log _ _ _ _ false
            (by rw [hb2]; rfl) M1 _ hZ1 hΛ1 hA1
          have hW2 := hZ2.welt
          obtain ⟨M3, hs3, hZ3⟩ := w_abbWieder (P := P) (O := O) (passes := passes) hZ2.1
            false n bis body ueber k r ρ2 rfl (show HeldIn _ (offen σ2.spur) from (heldB_block r (by rw [ho2]; exact hΛ1)).heldIn)
          rw [hW2] at hZ3
          exact weiter M3 e2 σ2 ρ2 (RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)))
            hZ3 (by rw [ho2, (Erw.lese _ _ _).offen]) hex
        · simp [Ausgang.abb?] at hex
        all_goals simp [Ausgang.abb?] at hex


variable (hRuf : RufOk P O passes f A R C)
include hRuf

-- `hRuf` discharges the calls in `stmtOkR`/`blockOkR`; `armsOkR`/`grundOkR`
-- need it only through their recursive `blockOkR` calls, which the linter
-- does not count as a use.
set_option linter.unusedSectionVars false in
mutual

theorem stmtOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C mr s →
    SimOkSR P O passes f fn stapel rho s0 A R s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattOkR P O passes f fn stapel rho s0 A R (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR t ht _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR e he _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onOption o p a, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR p hp _ _ _ _ _ hw M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hv
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR a ha _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, Λ₀, _, .onTag v arms, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsOkR arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = w
        at hex hsim
      obtain ⟨c, b, nutz⟩ := w
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨w', hw'⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := hsim _ _ _ _ _ hw' M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onWhy r arms, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes R arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := grundOkR arms ha _ _ _ _ _ _ hex M1 _ hZ1
        (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .call g args hp hr, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hC := hs.call_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i σ2 v hR2
        simp only [Ausgang.ok.injEq] at hex
        obtain ⟨rfl, rfl⟩ := hex
        obtain ⟨M1, hs1, hZ1⟩ := w_rufDann (P := P) (O := O) (passes := passes) hZ.1
          g args hp hr rest k ρ rfl hΛ.heldIn
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _ (PopArt.wie rfl)
          (heldB_eintritt hp hΛ _ _) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hl2, gepoppt_zustand hG2 rfl,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .locks L hr body, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hAL, hb, hbo⟩ := hs.locks_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨σ1, hb1, rfl⟩ := mapWelt_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_locksB (P := P) (O := O) (passes := passes) hZ.1
        L hr body rest k ρ rfl hΛ hbo (hA L hAL)
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR body hb _ _ _ _ _ hb1 M1 _ hZ1
        (heldB_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      have hW2 := hZ2.welt
      obtain ⟨M3, hs3, hZ3⟩ := w_freiGib (P := P) (O := O) (passes := passes) hZ2.1
        L (.dann rest k) ρ' rfl
      rw [hW2] at hZ3
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        offen_gibt_nimmt σ σ1 L ho2⟩
  | _, _, _, _, _, .breaking i body, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR body hb _ _ _ _ _ hex M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .traverse t inv body, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hb := hs.traverse_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannTrav (P := P) (O := O) (passes := passes) hZ.1
        t inv body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := travOkR P O passes f fn stapel rho s0 A R t inv body
        (blockOkR body hb) (blockAbbR body hb) (.dann rest k) _ log σ σ' ρ ρ'
        hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .retry n bis body ueber, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      obtain ⟨hb, hu⟩ := hs.retry_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannRetry (P := P) (O := O) (passes := passes) hZ.1
        n bis body ueber rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := retryOkR P O passes f fn stapel rho s0 A R bis body
        ueber (blockOkR body hb) (blockAbbR body hb) (blockOkR ueber hu)
        (.dann rest k) n log σ σ' ρ ρ' hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .forever a inv body, hs => by
      intro log σ σ' ρ ρ' hex M _ rest k hZ hΛ hA
      have hb := hs.forever_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannForever (P := P) (O := O) (passes := passes) hZ.1
        a inv body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := foreverOkR P O passes f fn stapel rho s0 A R a inv body
        (blockOkR body hb) (blockAbbR body hb) (.dann rest k) passes log σ σ' ρ ρ'
        hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1))
      exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, ho2⟩
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .ret .., _ => by
      intro log σ σ' ρ ρ' hex
      simp [execStmt] at hex
  | _, _, _, _, _, .retWhy .., _ => by
      intro log σ σ' ρ ρ' hex
      simp [execStmt] at hex
  | _, _, _, _, _, .leave .., _ => by
      intro log σ σ' ρ ρ' hex
      simp [execStmt] at hex
  | _, _, _, _, _, .next .., _ => by
      intro log σ σ' ρ ρ' hex
      simp [execStmt] at hex

theorem blockOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C mr b →
    SimOkBR P O passes f fn stapel rho s0 A R b
  | _, _, _, _, _, .nil, _ => by
      intro log σ σ' ρ ρ' hex M k hZ _ _
      simp only [execBlock, Ausgang.ok.injEq] at hex
      obtain ⟨rfl, rfl⟩ := hex
      have hW := hZ.welt
      obtain ⟨M1, hs1, hZ1⟩ := w_dannLeer (P := P) (O := O) (passes := passes) hZ.1 k ρ rfl
      rw [hW] at hZ1
      exact ⟨M1, [], RufLaufG.einzeln hs1, hZ1, rfl⟩
  | _, _, _, _, _, .cons s rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      obtain ⟨σ1, ρ1, hs1, hr1⟩ := execBlock_cons_ok O passes R s rest hex
      obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR s hs _ _ _ _ _ hs1 M rest k hZ hΛ hA
      have hΛ1 := heldB_iff (s.held_iff) hΛ
      rw [← ho1] at hΛ1
      obtain ⟨M2, e2, hl2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hr1 M1 k hZ1 hΛ1 (hA.lauf hl1)
      exact ⟨M2, e2 ++ e1, hl1.trans hl2, by rw [List.append_assoc]; exact hZ2,
        by rw [ho2, ho1]⟩
  | _, _, _, _, _, .bind e rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
        (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i σ2 v hR2
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
          g args he hp hr rest k ρ rfl hΛ.heldIn
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _
          (PopArt.bind rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
          heldB_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        obtain ⟨M3, e3, hl3, hZ3, ho3⟩ := blockOkR rest hrest _ _ _ _ _ hw M2 _ hZ2 hΛ2
          (hA.lauf hl12)
        obtain ⟨M4, hs4, hZ4⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ3
        exact ⟨M4, e3 ++ _, hl12.trans (hl3.trans (RufLaufG.einzeln hs4)),
          by rw [List.append_assoc]; exact hZ4,
          by rw [ho3, ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · cases hex
      · cases hex
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse g args he hp hr err rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      obtain ⟨hC, _, hrest, _, _⟩ := hb.bindCallElse_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i σ2 v hR2
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_bindCallElse (P := P) (O := O) (passes := passes) hZ.1
          g args he hp hr err rest k ρ rfl hΛ.heldIn
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _
          (PopArt.bindSonst _ err rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
          heldB_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        obtain ⟨M3, e3, hl3, hZ3, ho3⟩ := blockOkR rest hrest _ _ _ _ _ hw M2 _ hZ2 hΛ2
          (hA.lauf hl12)
        obtain ⟨M4, hs4, hZ4⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ3
        exact ⟨M4, e3 ++ _, hl12.trans (hl3.trans (RufLaufG.einzeln hs4)),
          by rw [List.append_assoc]; exact hZ4,
          by rw [ho3, ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (EndeW.zuAusgang_ne_ok _ _ _)
      · cases hex
      · cases hex
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .regRead r hk rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hzs
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
          rw [hW] at hZ1
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
            hΛ (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
          exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
        · cases hex
      · cases hex
  | _, _, _, _, _, .regReadElse r hk zusage sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.regLiesElse_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hw0
          obtain ⟨w, hw⟩ := schrumpf_ok hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLiesElseWahr (P := P) (O := O) (passes := passes)
            hZ.1 r hk zusage sonst rest k ρ rfl v (by rw [hW]; exact hv)
            (by rw [hW]; exact hw0)
          rw [hW] at hZ1
          obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
            (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
          exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            by rw [ho2, (Erw.lese _ _ _).offen]⟩
        · exact absurd hex (zuAusgang_ne_ok _ _ _)
      · cases hex
  | _, _, _, _, _, .awaits g payload hp hL hat rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨w, hw'⟩ := schrumpf_ok hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw' M1 _ hZ1
        (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
      exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, herw.offen]⟩
  | _, _, _, _, _, .narrow e lo' hi' sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.narrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hin
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_narrowOk (P := P) (O := O) (passes := passes) hZ.1
          lo' hi' e sonst rest k ρ rfl hW hin
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .check c sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.pruefung_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_pruefWahr (P := P) (O := O) (passes := passes) hZ.1
          c sonst rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        exact ⟨M2, _, RufLaufG.schritt hs1 hr2, hZ2, by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)
  | _, _, _, _, _, .float op a b lo hi rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .floatLit q lo hi rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl v hv
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          hΛ (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
      · cases hex
  | _, _, _, _, _, .floatOf e lo hi rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · cases hex
  | _, _, _, _, _, .floatNarrow e lo hi sonst rest, hb => by
      intro log σ σ' ρ ρ' hex M k hZ hΛ hA
      have hr := hb.gleitNarrow_inv.2.1
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨w, hw⟩ := schrumpf_ok hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitNarrowOk (P := P) (O := O) (passes := passes)
          hZ.1 e lo hi sonst rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, hr2, hZ2, ho2⟩ := blockOkR rest hr _ _ _ _ _ hw M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := schrumpfOkR P O passes f fn stapel rho s0 hZ2
        exact ⟨M3, _, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · exact absurd hex (zuAusgang_ne_ok _ _ _)

theorem armsOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C mr arms → ∀ (v : Wert D (.sum cs)),
    SimOkBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockOkR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsOkR rest ha.cons_inv.2 _

theorem grundOkR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C mr arms →
    ∀ (r : Fin n), SimOkBR P O passes f fn stapel rho s0 A R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockOkR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundOkR rest ha.cons_inv.2 _


theorem stmtAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D (vertragVon D fn) l Γ Λ Λ'), StmtR A C mr s →
    SimAbbSR P O passes f fn stapel rho s0 A R s
  | _, _, _, _, _, .assignSlot t f' i e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignSlot t f' i e hw hL)
  | _, _, _, _, _, .assignThru p t ht f' i e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignThru _ p t ht f' i e hw hL)
  | _, _, _, _, _, .assignGlob g e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignGlob g e hw hL)
  | _, _, _, _, _, .putBytes t f' hf n i hlo hhi e hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.putBytes t f' hf n i hlo hhi e hw hL)
  | _, _, _, _, _, .assignVar x e, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.assignVar x e)
  | _, _, _, _, _, .shift t f' hτ i von nach hn he hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.shift t f' hτ i von nach hn he hw hL)
  | _, _, _, _, _, .regWrite r hk e, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.regWrite r hk e)
  | _, _, _, _, _, .transition r hk m hm hl maske bits, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.transition r hk m hm hl maske bits)
  | _, _, _, _, _, .publish g e payload hp hw hL, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.publish g e payload hp hw hL)
  | _, _, _, _, _, .advances m a h hs, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.advances m a h hs)
  | _, _, _, _, _, .retires m s h a, _ =>
      blattAbbR P O passes f fn stapel rho s0 A R (.retires m s h a)
  | _, _, _, _, _, .ite c t e, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      obtain ⟨ht, he⟩ := hs.ite_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteWahr (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; exact hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR t ht hl _ _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hc
        obtain ⟨M1, hs1, hZ1⟩ := w_iteFalsch (P := P) (O := O) (passes := passes) hZ.1
          c t e rest k ρ rfl (by rw [hW]; simpa using hc)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR e he hl _ _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onOption o p a, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      obtain ⟨hp, ha⟩ := hs.onOption_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      split at hex
      · rename_i v hv
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_optSome (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR p hp hl _ _ _ _ _ _ h1 M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
        obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
        exact ⟨M4, e2, _, .nil,
          RufLaufG.schritt hs1 (hr2.trans (RufLaufG.schritt hs3 (RufLaufG.einzeln hs4))), hZ4,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · rename_i hv
        obtain ⟨M1, hs1, hZ1⟩ := w_optNone (P := P) (O := O) (passes := passes) hZ.1
          o p a rest k ρ rfl (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR a ha hl _ _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, Λ₀, _, .onTag v arms, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      have ha := hs.onTag_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execArms_wahl] at hex
      have hsim := armsAbbR arms ha (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ)
      generalize hwahl : armWahlG arms (eval (σ.lese Λ₀ v.orte) v (σ.lese Λ₀ v.orte) ρ) = x
        at hex hsim
      obtain ⟨c, b, nutz⟩ := x
      cases c with
      | none =>
        obtain ⟨M1, hs1, hZ1⟩ := w_tagNone (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hsim hl _ _ _ _ _ _ hex M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      | some lh =>
        obtain ⟨lo, hi⟩ := lh
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_tagSome (P := P) (O := O) (passes := passes) hZ.1
          v arms rest k ρ rfl lo hi b nutz (by rw [hW]; exact hwahl)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := hsim hl _ _ _ _ _ _ h1 M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
        obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
        exact ⟨M4, e2, _, .nil,
          RufLaufG.schritt hs1 (hr2.trans (RufLaufG.schritt hs3 (RufLaufG.einzeln hs4))), hZ4,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .onWhy r arms, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      have ha := hs.onGrund_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      rw [execGrund_wahlW O passes R arms] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_grund (P := P) (O := O) (passes := passes) hZ.1
        r arms rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, Λx, r', hr2, hZ2, ho2⟩ := grundAbbR arms ha _ hl _ _ _ _ _ _ hex M1 _ hZ1
        (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
      exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .call g args hp hr, _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp only [execStmt] at hex
      split at hex
      · simp [Ausgang.abb?] at hex
      · exact (Fin.cast hr ‹_›).elim0
      · simp [Ausgang.abb?] at hex
      · simp [Ausgang.abb?] at hex
  | _, _, _, _, _, .callInd .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .locks L hr body, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      obtain ⟨hAL, hb, hbo⟩ := hs.locks_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨σ1, hb1, rfl⟩ := abb_mapWelt _ hex
      obtain ⟨M1, hs1, hZ1⟩ := w_locksB (P := P) (O := O) (passes := passes) hZ.1
        L hr body rest k ρ rfl hΛ hbo (hA L hAL)
      rw [hW] at hZ1
      obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR body hb hl _ _ _ _ _ _ hb1 M1 _ hZ1
        (heldB_locks L hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelFreiR P O passes f fn stapel rho s0 hl hZ2
      obtain ⟨M4, hs4, hZ4⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ3
      exact ⟨M4, e2, _, .nil,
        RufLaufG.schritt hs1 (hr2.trans (RufLaufG.schritt hs3 (RufLaufG.einzeln hs4))), hZ4,
        offen_gibt_nimmt σ σ1 L ho2⟩
  | _, _, _, _, _, .breaking i body, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      have hb := hs.breaking_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_breaking (P := P) (O := O) (passes := passes) hZ.1
        i body rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR body hb hl _ _ _ _ _ _ hex M1 _ hZ1
        hΛ (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
      exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  | _, l0, _, _, _, .traverse t inv body, _ => by
      intro hl log σ σ' ρ ρ' w hex
      have h0 : (execStmt O passes R (Stmt.traverse (V := vertragVon D fn) (l := l0) t inv body)
          σ ρ).ohneAbbruch := by simp only [execStmt]; exact traverseLauf_ohneAbbruch _ _ _ _ _
      rw [abb_none_of h0] at hex
      cases hex
  | _, _, _, _, _, .retry n bis body ueber, hs => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      obtain ⟨hb, hu⟩ := hs.retry_inv
      have hW := hZ.welt
      simp only [execStmt] at hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannRetry (P := P) (O := O) (passes := passes) hZ.1
        n bis body ueber rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := retryAbbR P O passes f fn stapel rho s0 A R hl bis body
        ueber (blockOkR body hb) (blockAbbR body hb) (blockAbbR ueber hu) (.dann rest k) n log
        σ σ' ρ ρ' w hex M1 hZ1 hΛ (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelDannR P O passes f fn stapel rho s0 hl hZ2
      exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3, ho2⟩
  | _, l0, _, _, _, .forever a inv body, _ => by
      intro hl log σ σ' ρ ρ' w hex
      have h0 : (execStmt O passes R (Stmt.forever (V := vertragVon D fn) (l := l0) a inv body)
          σ ρ).ohneAbbruch := by simp only [execStmt]; exact foreverLauf_ohneAbbruch _ _ _ _ _ _
      rw [abb_none_of h0] at hex
      cases hex
  | _, _, _, _, _, .axiomCall .., hs => by exact absurd hs.art (by simp [Stmt.rArt, Stmt.blattArt])
  | _, _, _, _, _, .ret .., _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp [execStmt, Ausgang.abb?] at hex
  | _, _, _, _, _, .retWhy .., _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp [execStmt, Ausgang.abb?] at hex
  | _, _, _, _, _, .leave h, _ => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      simp only [execStmt, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at hex
      obtain ⟨rfl, rfl, rfl⟩ := hex
      exact ⟨M, [], _, rest, RufLaufG.refl M, hZ, rfl⟩
  | _, _, _, _, _, .next h, _ => by
      intro hl log σ σ' ρ ρ' w hex M _ rest k hZ hΛ hA
      simp only [execStmt, Ausgang.abb?, Option.some.injEq, Prod.mk.injEq] at hex
      obtain ⟨rfl, rfl, rfl⟩ := hex
      exact ⟨M, [], _, rest, RufLaufG.refl M, hZ, rfl⟩

theorem blockAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D fn) l Γ Λ Λ'), BlockR A C mr b →
    SimAbbBR P O passes f fn stapel rho s0 A R b
  | _, _, _, _, _, .nil, _ => by
      intro hl log σ σ' ρ ρ' w hex
      simp [execBlock, Ausgang.abb?] at hex
  | _, _, _, _, _, .cons s rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      obtain ⟨hs, hr⟩ := hb.cons_inv
      rcases execBlock_cons_abb O passes R s rest hex with h | ⟨σ1, ρ1, h1, h2⟩
      · exact stmtAbbR s hs hl _ _ _ _ _ _ h M rest k hZ hΛ hA
      · obtain ⟨M1, e1, hl1, hZ1, ho1⟩ := stmtOkR s hs _ _ _ _ _ h1 M rest k hZ hΛ hA
        have hΛ1 := heldB_iff (s.held_iff) hΛ
        rw [← ho1] at hΛ1
        obtain ⟨M2, e2, Λx, r, hl2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h2 M1 k hZ1
          hΛ1 (hA.lauf hl1)
        exact ⟨M2, e2 ++ e1, Λx, r, hl1.trans hl2, by rw [List.append_assoc]; exact hZ2,
          by rw [ho2, ho1]⟩
  | _, _, _, _, _, .bind e rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.bind_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
      obtain ⟨M1, hs1, hZ1⟩ := w_dannBind (P := P) (O := O) (passes := passes) hZ.1
        e rest k ρ rfl
      rw [hW] at hZ1
      obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
        (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
      exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, (Erw.lese _ _ _).offen]⟩
  | _, _, _, _, _, .bindCall g args he hp hr rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      obtain ⟨hC, hrest⟩ := hb.bindCall_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i σ2 v hR2
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_bindCall (P := P) (O := O) (passes := passes) hZ.1
          g args he hp hr rest k ρ rfl hΛ.heldIn
        rw [hW] at hZ1
        obtain ⟨M2, e2, hl2, hG2, ho2⟩ := hRuf.1 g hC _ _ _ _ hR2 M1 _ stapel _ hZ1 _
          (PopArt.bind rest k ρ rfl he) (heldB_eintritt hp hΛ _ _)
          (hA.lauf (RufLaufG.einzeln hs1))
        have hZ2 := gepoppt_zustand hG2 rfl
        have hΛ2 : HeldB (vertragVon D fn).boden (nach D g _) (offen σ2.spur) :=
          heldB_iff (fun L => held_nachSig_iff _ _ L)
            (by rw [ho2, (Erw.lese _ _ _).offen]; exact hΛ)
        have hl12 := RufLaufG.schritt hs1 hl2
        obtain ⟨M3, e3, Λx, r, hl3, hZ3, ho3⟩ := blockAbbR rest hrest hl _ _ _ _ _ _ h1 M2 _ hZ2
          hΛ2 (hA.lauf hl12)
        obtain ⟨M4, hs4, hZ4⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ3
        exact ⟨M4, e3 ++ _, _, .nil, hl12.trans (hl3.trans (RufLaufG.einzeln hs4)),
          by rw [List.append_assoc]; exact hZ4,
          by rw [ho3, ho2, (Erw.lese _ _ _).offen]⟩
      · exact (Fin.cast hr ‹_›).elim0
      · simp [Ausgang.abb?] at hex
      · simp [Ausgang.abb?] at hex
  | _, _, _, _, _, .bindCallInd .., hb => by cases hb
  | _, _, _, _, _, .bindCallElse .., hb => by
      intro hl
      have h0 := hb.bindCallElse_inv.2.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .bindAxiom .., hb => by cases hb
  | _, _, _, _, _, .bindAxiomElse .., hb => by cases hb
  | _, _, _, _, _, .regRead r hk rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.regLies_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        split at hex
        · rename_i hzs
          obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
          obtain ⟨M1, hs1, hZ1⟩ := w_regLies (P := P) (O := O) (passes := passes) hZ.1
            r hk rest k ρ rfl v (by rw [hW]; exact hv) hzs
          rw [hW] at hZ1
          obtain ⟨M2, e2, Λx, r', hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
            hΛ (hA.lauf (RufLaufG.einzeln hs1))
          obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
          exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
            ho2⟩
        · simp [Ausgang.abb?] at hex
      · simp [Ausgang.abb?] at hex
  | _, _, _, _, _, .regReadElse .., hb => by
      intro hl
      have h0 := hb.regLiesElse_inv.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .awaits g payload hp hL hat rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.awaits_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i hvis
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_awaits (P := P) (O := O) (passes := passes) hZ.1
          g payload hp hL hat rest k ρ rfl (by rw [hW]; exact hvis)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · simp [Ausgang.abb?] at hex
  | _, _, _, Λ₀, _, .exchange g neuE hw hL rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.exchange_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
      obtain ⟨M1, hs1, hZ1⟩ := w_exchange (P := P) (O := O) (passes := passes) hZ.1
        g neuE hw hL rest k ρ rfl
      rw [hW] at hZ1
      have herw := (Erw.lese σ Λ₀ (.inr g :: neuE.orte)).trans
        (Erw.schreibGlob _ g Λ₀ (eval (σ.lese Λ₀ (.inr g :: neuE.orte)) neuE
          (σ.lese Λ₀ (.inr g :: neuE.orte))
          (.cons ((σ.lese Λ₀ (.inr g :: neuE.orte)).globs g) ρ)))
      obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
        (by rw [herw.offen]; exact hΛ) (hA.lauf (RufLaufG.einzeln hs1))
      obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
      exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
        by rw [ho2, herw.offen]⟩
  | _, _, _, _, _, .narrow .., hb => by
      intro hl
      have h0 := hb.narrow_inv.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .check .., hb => by
      intro hl
      have h0 := hb.pruefung_inv.2.2.2
      subst h0
      cases hl
  | _, _, _, _, _, .float op a b lo hi rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.gleit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleit (P := P) (O := O) (passes := passes) hZ.1
          op a b lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · simp [Ausgang.abb?] at hex
  | _, _, _, _, _, .floatLit q lo hi rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.gleitLit_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitLit (P := P) (O := O) (passes := passes) hZ.1
          q lo hi rest k ρ rfl v hv
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
          hΛ (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          ho2⟩
      · simp [Ausgang.abb?] at hex
  | _, _, _, _, _, .floatOf e lo hi rest, hb => by
      intro hl log σ σ' ρ ρ' w hex M k hZ hΛ hA
      have hr := hb.gleitVon_inv
      have hW := hZ.welt
      simp only [execBlock] at hex
      split at hex
      · rename_i v hv
        obtain ⟨ρ1, h1, rfl⟩ := abb_schrumpf hex
        obtain ⟨M1, hs1, hZ1⟩ := w_gleitVon (P := P) (O := O) (passes := passes) hZ.1
          e lo hi rest k ρ rfl v (by rw [hW]; exact hv)
        rw [hW] at hZ1
        obtain ⟨M2, e2, Λx, r, hr2, hZ2, ho2⟩ := blockAbbR rest hr hl _ _ _ _ _ _ h1 M1 _ hZ1
          (heldB_lese _ hΛ) (hA.lauf (RufLaufG.einzeln hs1))
        obtain ⟨M3, hs3, hZ3⟩ := peelSchrumpfR P O passes f fn stapel rho s0 hl hZ2
        exact ⟨M3, e2, _, .nil, RufLaufG.schritt hs1 (hr2.trans (RufLaufG.einzeln hs3)), hZ3,
          by rw [ho2, (Erw.lese _ _ _).offen]⟩
      · simp [Ausgang.abb?] at hex
  | _, _, _, _, _, .floatNarrow .., hb => by
      intro hl
      have h0 := hb.gleitNarrow_inv.2.2.2
      subst h0
      cases hl

theorem armsAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} (arms : Arms D (vertragVon D fn) l Γ Λ Λ' cs),
    ArmsR A C mr arms → ∀ (v : Wert D (.sum cs)),
    SimAbbBR P O passes f fn stapel rho s0 A R (armWahlG arms v).2.1
  | _, _, _, _, _, _, .nil, _, ⟨⟨k, hk⟩, _⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨⟨0, _⟩, _⟩ => by
      exact blockAbbR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨⟨n + 1, _⟩, _⟩ => by
      exact armsAbbR rest ha.cons_inv.2 _

theorem grundAbbR : ∀ {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    (arms : GrundArms D (vertragVon D fn) l Γ Λ Λ' n), GrundArmsR A C mr arms →
    ∀ (r : Fin n), SimAbbBR P O passes f fn stapel rho s0 A R (grundWahlG arms r)
  | _, _, _, _, _, _, .nil, _, ⟨k, hk⟩ => (Nat.not_lt_zero k hk).elim
  | _, _, _, _, _, _, .cons b _, ha, ⟨0, _⟩ => by
      exact blockAbbR b ha.cons_inv.1
  | _, _, _, _, _, _, .cons _ rest, ha, ⟨k + 1, _⟩ => by
      exact grundAbbR rest ha.cons_inv.2 _


end

end SimOk

end Gabbro.Grammatik
