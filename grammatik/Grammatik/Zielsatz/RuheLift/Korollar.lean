/-
  File:      Grammatik/Zielsatz/RuheLift/Korollar.lean
  Subject:   **The goal theorem at the boundaries of one thread's call-free run** (the idle-root lift, part 2). From
             the premises of `gabbro_ziel` in ITS OWN form -- (a) a checker `C : PrueferX` accepting the unit, (b)
             `NutzerPflichtA E`, (c) `HardwareAnnahmen O E.Q` -- and a declared start `⟨f, rho⟩` of `E` holding no
             lock by signature, the start `initEin thr f rho` of `E.P.mitRuhe` meets (d) `Laufzeit`
             (`laufzeit_initEin`); for every decomposed call-free prefix of `f`'s body (`Zerlegt`) the machine of
             `E.P.mitRuhe` reaches, by steps of `thr` alone, the translated boundary behind it (`RandRuhe`), and
             `gabbro_ziel` (through `gabbro_ziel_gx`) gives every leg of `ZielX` there (`ruheLift_zielX`); without
             `atomic` globals every leg of `Ziel` (`ruheLift_ziel`). No idle function of `E.P` is a premise.
             Transferred back to the world `σ` of the boundary: every lock invariant of a lock thread `thr` does not
             hold holds on `σ.speicher` (`sperrInv_zurueck`, `ruheLift_sperrInv`).
-/
module
public import Grammatik.Zielsatz.RuheLift.Grenze
public import Grammatik.Zielsatz.Atomar.BeweisAtomar
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **(d) for one running declared start**: the runtime's start with thread `thr` running the declared start
    `⟨f, rho⟩` and the idle root on every other thread is admissible (`Laufzeit`). -/
theorem laufzeit_initEin {E : Einheit D} (thr : Faden) {f : D.Fn} {rho : Env D (D.params f)}
    (ha : (⟨f, rho⟩ : Σ g : D.Fn, Env D (D.params g)) ∈ E.starts ++ E.gestartet) :
    Laufzeit E (speicherR E.sp0) (initEin thr f rho) where
  lader := rfl
  start t := by
    by_cases h : t = thr
    · exact Or.inr ⟨⟨f, rho⟩, ha, initEin_gleich h⟩
    · exact Or.inl (initEin_sonst h)
  einmal t u htu he := by
    by_cases h : t = thr
    · have hu : u ≠ thr := fun e => htu (h.trans e.symm)
      rw [initEin_gleich h, initEin_sonst hu] at he
      have he' : (some f : D.mitRuhe.Fn) = none := he
      exact absurd he' (Option.some_ne_none f)
    · exact Or.inl (congrArg Sigma.fst (initEin_sonst h))

/-- No `atomic` global, no admitted shared atomic. -/
theorem geteiltV_ohne_atomar [DecidableEq D.Fn] {P : Programm D} {ws : List D.Fn}
    (h : ∀ g, D.atomar g = false) (c : D.Tab ⊕ D.Glob) : ¬ GeteiltV P ws c := by
  rintro ⟨⟨⟨g, _, hg⟩, _, _⟩, _⟩
  rw [h g] at hg
  exact Bool.false_ne_true hg

/-- **The lock invariants, back on the world of the boundary**: at a translated boundary every other thread holds no
    lock, so the lock-invariant leg of the goal (`SperrInvG` of `S.mitRuhe`) at the machine of `P.mitRuhe` says that
    every lock thread `thr` does not hold has its invariant on the memory of the world `σ`. -/
theorem sperrInv_zurueck {S : SperrInv D} {thr : Faden} {f : D.Fn} {rho : Env D (D.params f)} {s0 : World D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {eb : Endblock D (vertragVon D f) l Γ Λ}
    {M : RufMaschineG D.mitRuhe} {σ : World D} {ρ : Env D Γ} (hR : RandRuhe thr f rho s0 eb M σ ρ)
    (hS : SperrInvG S.mitRuhe M) (L : D.Lock) (hL : L ∉ offen σ.spur) : S.inv L σ.speicher = true := by
  obtain ⟨⟨_, hZ⟩, _, hO⟩ := hR
  have hfrei : ∀ t, L ∉ offen (M.faeden t).spur := by
    intro t
    by_cases e : t = thr
    · rw [e, hZ.spur]
      show L ∉ offen (σ.spur.map evR)
      rw [offen_map_evR]
      exact hL
    · rw [hO t e]
      exact List.not_mem_nil
  have h : S.inv L (speicherZ (worldR σ).speicher) = true := by
    have h0 := hS L hfrei
    rw [hZ.2] at h0
    exact h0
  rw [show (worldR σ).speicher = speicherR σ.speicher from rfl, speicherZ_speicherR] at h
  exact h

section Korollar

variable [DecidableEq D.Fn]

/-- **The goal theorem at the end of a decomposed call-free prefix of a declared start, with the atomic rely.**
    Premises exactly those of `gabbro_ziel` for (a), (b), (c); (d) is met by `initEin thr f rho`. Then the machine of
    `E.P.mitRuhe` reached from that start by steps of `thr` alone stands at the translated boundary behind the
    prefix, and every leg of `ZielX` holds there. -/
theorem ruheLift_zielX (C : PrueferX) (E : Einheit D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) (thr : Faden) (f : D.Fn)
    (rho : Env D (D.params f)) (ha : (⟨f, rho⟩ : Σ g : D.Fn, Env D (D.params g)) ∈ E.starts ++ E.gestartet)
    (hf : D.haelt f = []) {Agl : D.Lock → Prop} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D f) false (D.params f) Λe} {σe : World D} {ρe : Env D (D.params f)}
    (hk : Zerlegt O passes R Agl (E.P.rumpf f) (E.sp0.welt []) rho ebe σe ρe) :
    ∃ Me : RufMaschineG D.mitRuhe,
      RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe (speicherR E.sp0) (initEin thr f rho))
        Me ∧
      RandRuhe thr f rho (E.sp0.welt []) ebe Me σe ρe ∧
      ZielX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
        (RufStartG E.P.mitRuhe (speicherR E.sp0) (initEin thr f rho)) Me := by
  obtain ⟨Me, hl, hR⟩ := randRuhe_zerlegt E.P O passes R hk (randRuhe_start E.P E.sp0 thr rho hf)
  have hr : RufErreichbarG E.P.mitRuhe O.mitRuhe passes
      (RufStartG E.P.mitRuhe (speicherR E.sp0) (initEin thr f rho)) Me :=
    rufErreichbarG_von_lauf hl RufErreichbarG.start
  exact ⟨Me, hr, hR, gabbro_ziel_gx C D E fs ls cs hC hN O hH passes (speicherR E.sp0) (initEin thr f rho)
    (laufzeit_initEin thr ha) Me (gx_aus_g_lauf hr)⟩

/-- **The goal theorem at the end of a decomposed call-free prefix, without `atomic` globals**: every leg of `Ziel`
    at the machine of `E.P.mitRuhe` that the boundary behind the prefix translates to. -/
theorem ruheLift_ziel (C : PrueferX) (E : Einheit D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) (thr : Faden) (f : D.Fn)
    (rho : Env D (D.params f)) (ha : (⟨f, rho⟩ : Σ g : D.Fn, Env D (D.params g)) ∈ E.starts ++ E.gestartet)
    (hf : D.haelt f = []) (hAt : ∀ g, D.atomar g = false) {Agl : D.Lock → Prop} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D f) false (D.params f) Λe} {σe : World D} {ρe : Env D (D.params f)}
    (hk : Zerlegt O passes R Agl (E.P.rumpf f) (E.sp0.welt []) rho ebe σe ρe) :
    ∃ Me : RufMaschineG D.mitRuhe,
      RufErreichbarG E.P.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe (speicherR E.sp0) (initEin thr f rho))
        Me ∧
      RandRuhe thr f rho (E.sp0.welt []) ebe Me σe ρe ∧
      Ziel E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes
        (RufStartG E.P.mitRuhe (speicherR E.sp0) (initEin thr f rho)) Me := by
  obtain ⟨Me, hr, hR, hX⟩ := ruheLift_zielX C E fs ls cs hC hN O hH passes R thr f rho ha hf hk
  exact ⟨Me, hr, hR, ziel_of_X (D := D.mitRuhe) (Tg := GeteiltV (D := D) E.P E.ws)
    (fun c => geteiltV_ohne_atomar hAt c) hX⟩

/-- **The lock invariants on the world behind the prefix**, from the premises of `gabbro_ziel`: every lock thread
    `thr` does not hold there has its invariant on the memory the sequential run of the prefix ends in. -/
theorem ruheLift_sperrInv (C : PrueferX) (E : Einheit D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat)
    (R : ∀ g : D.Fn, World D → Env D (D.params g) → RufAusgang g) (thr : Faden) (f : D.Fn)
    (rho : Env D (D.params f)) (ha : (⟨f, rho⟩ : Σ g : D.Fn, Env D (D.params g)) ∈ E.starts ++ E.gestartet)
    (hf : D.haelt f = []) {Agl : D.Lock → Prop} {Λe : List (Res D)}
    {ebe : Endblock D (vertragVon D f) false (D.params f) Λe} {σe : World D} {ρe : Env D (D.params f)}
    (hk : Zerlegt O passes R Agl (E.P.rumpf f) (E.sp0.welt []) rho ebe σe ρe) :
    ∀ L : D.Lock, L ∉ offen σe.spur → E.S.inv L σe.speicher = true := by
  obtain ⟨_, _, hR, hX⟩ := ruheLift_zielX C E fs ls cs hC hN O hH passes R thr f rho ha hf hk
  exact sperrInv_zurueck hR hX.sperrInv

end Korollar

end Gabbro.Grammatik.Zielsatz
