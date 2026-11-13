/-
  File:      Grammatik/Logik/Fortschritt/Halten/Invariante.lean
  Subject:   THE SECTION INVARIANT `SekInv`: while thread `u` holds `L`, its stack is
             `oben ++ r :: unten`, where `r` is the frame whose residue holds `L` (its static holdings name
             `L`, its function's signature end does not), the frames `oben` above it are callees entered
             from the section, each costed as in `KInv` (`Seg`), and the section's own part of `r` is
             measured by `potSek L ep` at the return-predicate price `ep` its body was checked with (C05).
             `sekInv_schritt`: every step keeps it while `L` stays held, and an own
             step of `u` lowers the measure by one -- the `kinv_schritt` engine of KostenG with the bottom
             frame cut at the release marker of `L`. A pop of `r` itself is impossible while `L` stays held:
             `r` names `L` beyond its end signature (`schrittRang`).
-/
module
public import Grammatik.Logik.Fortschritt.Halten.SchrittSek2
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- **The section invariant** of thread state `z` for lock `L`, at measure `Φ`. -/
def SekInv {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (pa : Nat) (L : D.Lock)
    (z : RufFadenG D) (Φ : Nat) : Prop :=
  ∃ (oben : List (RufRahmenG D)) (r : RufRahmenG D) (unten : List (RufRahmenG D)) (i : ι)
    (ep Φo : Nat),
    z.kopf :: z.stapel = oben ++ r :: unten ∧
    Seg T S pa oben Φo ∧
    rufeV L (S i) (fun _ => false) true r.rest.2.2.2.2 = true ∧
    Res.held L ∈ r.rest.2.2.1 ∧ Res.held L ∉ (vertragVon D r.f).ende ∧
    Φo + potSek L ep (T i) pa r.rest.2.2.2.2 ≤ Φ

/-! ## Stack shapes that exclude each other -/

theorem stapel_nicht_AB {α : Type} {s s' : List α} {c : α} (h1 : s' = s) (h2 : s' = c :: s) :
    False := by
  have h := congrArg List.length (h1.symm.trans h2)
  rw [List.length_cons] at h
  omega

theorem stapel_nicht_AC {α : Type} {s s' rst : List α} {c : α} (h1 : s' = s) (h2 : s = c :: rst)
    (h3 : s' = rst) : False := by
  have h := congrArg List.length (h3.symm.trans (h1.trans h2))
  rw [List.length_cons] at h
  omega

theorem stapel_nicht_BC {α : Type} {s s' rst : List α} {c c' : α} (h1 : s' = c' :: s)
    (h2 : s = c :: rst) (h3 : s' = rst) : False := by
  have h := congrArg List.length (h3.symm.trans (h1.trans (congrArg (List.cons c') h2)))
  rw [List.length_cons, List.length_cons] at h
  omega

section Motor

variable {ι : Type} (T : ι → D.Fn → Nat) (S : ι → D.Fn → Bool) (nx : ι → D.Fn → ι)
  {P : Programm D} {O : Orakel D} {pa : Nat} (L : D.Lock)

/-- **A thread that steps while it holds `L` has a positive measure.** -/
theorem sekInv_pos {M M' : RufMaschineG D} {u : Faden} (hs : RufSchrittG P O pa M u M') {Φ : Nat}
    (hI : SekInv T S pa L (M.faeden u) Φ) : 1 ≤ Φ := by
  obtain ⟨oben, r, unten, i, ep, Φo, hst, hseg, -, -, -, hΦ⟩ := hI
  have harb := rufSchrittG_arbeitsfaehig hs
  cases oben with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hst
    rw [hst.1] at harb
    have := potSek_pos L ep (T i) pa r.rest.2.2.2.2 harb
    omega
  | cons o oben' =>
    simp only [List.cons_append, List.cons.injEq] at hst
    rw [hst.1] at harb
    cases hseg with
    | cons _ j _ p epj hok hb hrest =>
      have := potRest_pos epj (T j) pa o.rest.2.2.2.2 harb
      omega

/-- The section frame is the head: `schrittSek` measures the step, `schrittRang` keeps the marker
    (the frame names `L`, its end signature does not) and excludes the frame's pop. -/
theorem sekInv_kopf (hO : GutO O)
    (hS1 : ∀ i g, S i g = true → kostenEnd (kostenEpilog P g) (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    {M M' : RufMaschineG D} {g : Faden} (hs : RufSchrittG P O pa M g M') {i : ι} (ep : Nat)
    (hrv : rufeV L (S i) (fun _ => false) true (M.faeden g).kopf.rest.2.2.2.2 = true)
    (hΛL : Res.held L ∈ (M.faeden g).kopf.rest.2.2.1)
    (hende : Res.held L ∉ (vertragVon D (M.faeden g).kopf.f).ende)
    (hL : L ∈ offen (M.faeden g).spur) (hL' : L ∈ offen (M'.faeden g).spur)
    (hnd : (offen (M.faeden g).spur).Nodup) (hbal : FadenScopeBalanceG (M.faeden g))
    (A : Merkmal D) (hmR : (M.faeden g).kopf.rest.2.2.2.2.mR A) :
    ∃ Φ', SekInv T S pa L (M'.faeden g) Φ' ∧
      Φ' + 1 ≤ potSek L ep (T i) pa (M.faeden g).kopf.rest.2.2.2.2 := by
  rcases schrittRang hO hs A hmR with
    ⟨hstR, hfR, hΛR⟩ | ⟨gR, cR, hstR, hcfR, hgfR, hgΛR, hcΛR, hoR, hpR⟩ |
    ⟨cR, rstR, relR, hpopR, hstR, hfR, hΛR, hoR, hpermR⟩
  · rcases schrittSek L hs hbal.1 hL hL' hnd ep (T i) (S i) (fun _ => false) true with
      ⟨hst', hA⟩ | ⟨g', cl', rho, s0, hst', hk', hB'⟩ | ⟨cl, rst, hpop, hst', hC⟩
    · obtain ⟨hrv', hpot⟩ := hA hrv
      refine ⟨potSek L ep (T i) pa (M'.faeden g).kopf.rest.2.2.2.2,
        ⟨[], (M'.faeden g).kopf, (M'.faeden g).stapel, i, ep, 0, rfl, Seg.nil, hrv', ?_, ?_,
          by omega⟩, hpot⟩
      · rcases hΛR with ⟨-, hsub⟩ | ⟨L₁, -, -, -, -, hΛ'⟩ | ⟨L₁, ho, hsub⟩
        · exact hsub L hΛL
        · rw [hΛ']; exact List.mem_cons_of_mem _ hΛL
        · by_cases hLL : L = L₁
          · exfalso
            rw [ho, ← hLL] at hL'
            exact hnd.not_mem_erase hL'
          · exact hsub L hLL hΛL
      · rw [hfR]; exact hende
    · exact (stapel_nicht_AB hstR hst').elim
    · exact (stapel_nicht_AC hstR hpop hst').elim
  · rcases schrittSek L hs hbal.1 hL hL' hnd ep (T i) (S i) (fun _ => false) true with
      ⟨hst', hA⟩ | ⟨g', cl', rho, s0, hst', hk', hB'⟩ | ⟨cl, rst, hpop, hst', hC⟩
    · exact (stapel_nicht_AB hst' hstR).elim
    · have e : cl' = cR := (List.cons.inj (hst'.symm.trans hstR)).1
      obtain ⟨hrvc, hdir⟩ := hB' hrv
      obtain ⟨hZ, hpot⟩ := hdir.resolve_right (fun ⟨_, hn, _⟩ => Bool.false_ne_true hn)
      have hep : potRest (kostenEpilog P g') (T (nx i g')) pa (M'.faeden g).kopf.rest.2.2.2.2 =
          kostenEnd (kostenEpilog P g') (T (nx i g')) pa (P.rumpf g') := by rw [hk']; rfl
      have h1 := hS1 i g' hZ
      refine ⟨kostenEnd (kostenEpilog P g') (T (nx i g')) pa (P.rumpf g') + potSek L ep (T i) pa cl'.rest.2.2.2.2,
        ⟨[(M'.faeden g).kopf], cl', (M.faeden g).stapel, i, ep,
          potRest (kostenEpilog P g') (T (nx i g')) pa (M'.faeden g).kopf.rest.2.2.2.2 + 0,
          by rw [hst']; try rfl, ?_, hrvc, ?_, ?_, by omega⟩, by omega⟩
      · exact Seg.cons _ (nx i g') [] 0 (kostenEpilog P g') (by rw [hk']; exact hS2 i g' hZ)
          (by rw [hk']; exact GRest.scopeChain_eintritt (P := P) g') Seg.nil
      · rw [e]; exact hcΛR L hΛL
      · rw [e, hcfR]; exact hende
    · exact (stapel_nicht_BC hstR hpop hst').elim
  · exfalso
    cases relR with
    | none =>
      try dsimp only at hpermR
      exact hende ((List.Perm.mem_iff hpermR).mp hΛL)
    | some L₁ =>
      try dsimp only at hoR hpermR
      by_cases hLL : L = L₁
      · rw [hoR, ← hLL] at hL'
        exact hnd.not_mem_erase hL'
      · exact hende ((List.Perm.mem_iff hpermR).mp
          ((List.mem_erase_of_ne (fun e => hLL (Res.held.inj e))).mpr hΛL))

/-- A frame above the section frame is the head: `schrittArt` measures it as in `kinv_schritt`; when it
    returns into the section frame, `schrittSek` resumes the section potential. -/
theorem sekInv_oben (hO : GutO O)
    (hS1 : ∀ i g, S i g = true → kostenEnd (kostenEpilog P g) (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    {M M' : RufMaschineG D} {g : Faden} (hs : RufSchrittG P O pa M g M') {i : ι}
    {oben unten : List (RufRahmenG D)} {r : RufRahmenG D} {ep Φo Φ : Nat}
    (hst : (M.faeden g).stapel = oben ++ r :: unten)
    (hseg : Seg T S pa ((M.faeden g).kopf :: oben) Φo)
    (hrv : rufeV L (S i) (fun _ => false) true r.rest.2.2.2.2 = true)
    (hΛL : Res.held L ∈ r.rest.2.2.1) (hende : Res.held L ∉ (vertragVon D r.f).ende)
    (hΦ : Φo + potSek L ep (T i) pa r.rest.2.2.2.2 ≤ Φ)
    (hL : L ∈ offen (M.faeden g).spur) (hL' : L ∈ offen (M'.faeden g).spur)
    (hnd : (offen (M.faeden g).spur).Nodup)
    (A : Merkmal D) (hmR : (M.faeden g).kopf.rest.2.2.2.2.mR A) :
    ∃ Φ', SekInv T S pa L (M'.faeden g) Φ' ∧ Φ' + 1 ≤ Φ := by
  cases hseg with
  | cons _ j _ p epj hokj hbj hrest =>
    have hpos := potRest_pos epj (T j) pa (M.faeden g).kopf.rest.2.2.2.2 (rufSchrittG_arbeitsfaehig hs)
    rcases schrittArt hs hbj epj (T j) (S j) (fun _ => false) true with
      ⟨hst', hA⟩ | ⟨g', cl', rho, s0, hst', hk', hB'⟩ | ⟨cl, rst, hpop, hst', hC⟩
    · obtain ⟨hok', hpot⟩ := hA hokj
      refine ⟨potRest epj (T j) pa (M'.faeden g).kopf.rest.2.2.2.2 + p + potSek L ep (T i) pa r.rest.2.2.2.2,
        ⟨(M'.faeden g).kopf :: oben, r, unten, i, ep, potRest epj (T j) pa (M'.faeden g).kopf.rest.2.2.2.2 + p,
          by rw [hst', hst]; try rfl,
          Seg.cons _ j oben p epj hok' ((rufSchrittG_scopeMove hs).same hst' hbj) hrest,
          hrv, hΛL, hende, Nat.le_refl _⟩, by omega⟩
    · obtain ⟨hokc, hdir⟩ := hB' hokj
      obtain ⟨hZ, hpot⟩ := hdir.resolve_right (fun ⟨_, hn, _⟩ => Bool.false_ne_true hn)
      have hep : potRest (kostenEpilog P g') (T (nx j g')) pa (M'.faeden g).kopf.rest.2.2.2.2 =
          kostenEnd (kostenEpilog P g') (T (nx j g')) pa (P.rumpf g') := by rw [hk']; rfl
      have h1 := hS1 j g' hZ
      refine ⟨kostenEnd (kostenEpilog P g') (T (nx j g')) pa (P.rumpf g') + (potRest epj (T j) pa cl'.rest.2.2.2.2 + p) +
          potSek L ep (T i) pa r.rest.2.2.2.2,
        ⟨(M'.faeden g).kopf :: cl' :: oben, r, unten, i, ep,
          potRest (kostenEpilog P g') (T (nx j g')) pa (M'.faeden g).kopf.rest.2.2.2.2 + (potRest epj (T j) pa cl'.rest.2.2.2.2 + p),
          by rw [hst', hst]; try rfl, ?_, hrv, hΛL, hende, by omega⟩, by omega⟩
      exact Seg.cons _ (nx j g') _ _ (kostenEpilog P g') (by rw [hk']; exact hS2 j g' hZ)
        (by rw [hk']; exact GRest.scopeChain_eintritt (P := P) g')
        (Seg.cons _ j oben p epj hokc ((rufSchrittG_scopeMove hs).push cl' hst' hbj) hrest)
    · cases oben with
      | nil =>
        simp only [List.nil_append] at hst
        rcases schrittSek L hs hbj hL hL' hnd ep (T i) (S i) (fun _ => false) true with
          ⟨hst2, -⟩ | ⟨_, cl2, _, _, hst2, -, -⟩ | ⟨cl2, rst2, hpop2, hst2, hC2⟩
        · exact (stapel_nicht_AC hst2 hpop hst').elim
        · exact (stapel_nicht_BC hst2 hpop hst').elim
        · have e3 : cl2 = r := (List.cons.inj (hpop2.symm.trans hst)).1
          obtain ⟨hrv2, hpot2⟩ := hC2 ep (T i) (S i) (fun _ => false) true
          rw [e3] at hrv2 hpot2
          rcases schrittRang hO hs A hmR with ⟨hstR, -, -⟩ | ⟨_, _, hstR, -⟩ |
              ⟨cR, rstR, relR, hpopR, hstR, hfR, hΛR, -, -⟩
          · exact (stapel_nicht_AC hstR hpop hst').elim
          · exact (stapel_nicht_BC hstR hpop hst').elim
          · have e4 : cR = r := (List.cons.inj (hpopR.symm.trans hst)).1
            refine ⟨potSek L ep (T i) pa (M'.faeden g).kopf.rest.2.2.2.2,
              ⟨[], (M'.faeden g).kopf, (M'.faeden g).stapel, i, ep, 0, rfl, Seg.nil, hrv2 hrv, ?_, ?_,
                by omega⟩, by omega⟩
            · rw [hΛR, e4]; exact hΛL
            · rw [hfR, e4]; exact hende
      | cons o' oben' =>
        simp only [List.cons_append] at hst
        obtain ⟨rfl, rfl⟩ := List.cons.inj (hpop.symm.trans hst)
        cases hrest with
        | cons _ j' _ p' epj' hokj' hbj' hrest' =>
          obtain ⟨hokc, hpotc⟩ := hC epj' (T j') (S j') (fun _ => false) true
          refine ⟨potRest epj' (T j') pa (M'.faeden g).kopf.rest.2.2.2.2 + p' + potSek L ep (T i) pa r.rest.2.2.2.2,
            ⟨(M'.faeden g).kopf :: oben', r, unten, i, ep, potRest epj' (T j') pa (M'.faeden g).kopf.rest.2.2.2.2 + p',
              by rw [hst']; try rfl,
              Seg.cons _ j' oben' p' epj' (hokc hokj') ((rufSchrittG_scopeMove hs).pop _ _ hpop hst' hbj')
                hrest',
              hrv, hΛL, hende, Nat.le_refl _⟩, by omega⟩

/-- **An own step of the holder lowers the measure by one** and keeps the section invariant while `L`
    stays held. -/
theorem sekInv_eigen (hO : GutO O)
    (hS1 : ∀ i g, S i g = true → kostenEnd (kostenEpilog P g) (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    {M M' : RufMaschineG D} {g : Faden} (hs : RufSchrittG P O pa M g M') {Φ : Nat}
    (hI : SekInv T S pa L (M.faeden g) Φ)
    (hL : L ∈ offen (M.faeden g).spur) (hL' : L ∈ offen (M'.faeden g).spur)
    (hnd : (offen (M.faeden g).spur).Nodup) (hbal : FadenScopeBalanceG (M.faeden g))
    (A : Merkmal D) (hmR : (M.faeden g).kopf.rest.2.2.2.2.mR A) :
    ∃ Φ', SekInv T S pa L (M'.faeden g) Φ' ∧ Φ' + 1 ≤ Φ := by
  obtain ⟨oben, r, unten, i, ep, Φo, hst, hseg, hrv, hΛL, hende, hΦ⟩ := hI
  cases oben with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hst
    obtain ⟨hkr, hsu⟩ := hst
    subst hkr
    cases hseg
    obtain ⟨Φ', hI', hle⟩ := sekInv_kopf T S nx L hO hS1 hS2 hs ep hrv hΛL hende hL hL' hnd hbal A hmR
    exact ⟨Φ', hI', by omega⟩
  | cons o oben' =>
    simp only [List.cons_append, List.cons.injEq] at hst
    obtain ⟨hko, hsu⟩ := hst
    subst hko
    exact sekInv_oben T S nx L hO hS1 hS2 hs hsu hseg hrv hΛL hende hΦ hL hL' hnd A hmR

/-- **The engine step of a section.** Any step keeps the section invariant while `L` stays held; a
    foreign step changes nothing, an own step lowers the measure by at least one. -/
theorem sekInv_schritt (hO : GutO O)
    (hS1 : ∀ i g, S i g = true → kostenEnd (kostenEpilog P g) (T (nx i g)) pa (P.rumpf g) ≤ T i g)
    (hS2 : ∀ i g, S i g = true → rufeE (S (nx i g)) (fun _ => false) true (P.rumpf g) = true)
    {M M' : RufMaschineG D} {g u : Faden} (hs : RufSchrittG P O pa M g M') {Φ : Nat}
    (hI : SekInv T S pa L (M.faeden u) Φ)
    (hL : L ∈ offen (M.faeden u).spur) (hL' : L ∈ offen (M'.faeden u).spur)
    (hnd : (offen (M.faeden u).spur).Nodup) (hbal : FadenScopeBalanceG (M.faeden u))
    (A : Merkmal D) (hmR : (M.faeden u).kopf.rest.2.2.2.2.mR A) :
    ∃ Φ', SekInv T S pa L (M'.faeden u) Φ' ∧ Φ' ≤ Φ := by
  by_cases hgu : g = u
  · subst hgu
    obtain ⟨Φ', hI', hle⟩ := sekInv_eigen T S nx L hO hS1 hS2 hs hI hL hL' hnd hbal A hmR
    exact ⟨Φ', hI', by omega⟩
  · refine ⟨Φ, ?_, Nat.le_refl Φ⟩
    rw [rufSchrittG_fremd hs u (Ne.symm hgu)]
    exact hI

end Motor

end Gabbro.Grammatik
