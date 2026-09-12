/-
  File:      Grammatik/KetteVoll.lean
  Subject:   **THE CHAIN FROM A MACHINE RUN, N THREADS** -- every `PCReach`
              run carries a joint chain with the same worlds and step threads.

  Lane 104 (D4): iterate the witnessed step (`kette_mit_zeugen`,
  `Ziel.lean`) over a whole `PCReach` run for any number of threads.
  The chain runs with an empty recorded run (`J.l = []`), so `Gesittet`
  and `BeschraenkteVerschraenkung` close vacuously; entry is built to
  fit the code (`eintrittOf`); debt holds for every function by U003
  (`schuldnerHaelt_gilt`); the invariant sight follows from the entry
  (`heldIn_invarianten` bridge); each step frame comes from the fired
  step -- honest leaves via their own contract (widened by the
  signature coincidence), locks by unchanged memory. No premise
  quantifies over program syntax.
-/
import Grammatik.Maschine
import Grammatik.Extraktion

namespace Gabbro.Grammatik

namespace KetteVoll

variable {D : Deklaration}

/-- The permissive pair set: every thread pair is co-declared, so the
    pair leg (`hPaar`) and the bounded interleaving over the empty run
    close by construction. -/
def ketteNb : Nebeneinander := fun _ _ => True

/-- A trace holding exactly the locks named by `Λ`: one `nimmt` per
    held lock (marks are dropped; `offen` ignores the snapshots). -/
def spurFuer (Λ : List (Res D)) : List (Ereignis D) :=
  (Λ.filterMap fun r => match r with
    | .held L => some L
    | _ => none).map fun L => Ereignis.nimmt L []

/-- The entry world for thread `g`: start memory with a trace holding
    exactly the locks its code declares at entry (`Signatur.anfang`). -/
def eintrittOf (sp : Speicher D) (code : Faden → D.Fn) (g : Faden) : World D :=
  sp.welt (spurFuer (Signatur.anfang D (D.signatur (code g))))

/-- `offen` of the built trace is the lock list it was built from. -/
theorem offen_spurFuer (ls : List D.Lock) :
    offen ((ls.map fun L => Ereignis.nimmt L []) : List (Ereignis D)) = ls := by
  induction ls with
  | nil => rfl
  | cons L rest ih => simp [offen, ih]

/-- Membership in the built trace is membership of the held locks in `Λ`. -/
theorem mem_offen_spurFuer (Λ : List (Res D)) (L : D.Lock) :
    L ∈ offen (spurFuer Λ) ↔ Res.held L ∈ Λ := by
  unfold spurFuer
  rw [offen_spurFuer]
  constructor
  · intro hmem
    obtain ⟨r, hr, hfr⟩ := List.mem_filterMap.mp hmem
    cases r with
    | held L' =>
      simp at hfr
      subst hfr
      exact hr
    | marke _ _ => simp at hfr
  · intro hmem
    exact List.mem_filterMap.mpr ⟨Res.held L, hmem, rfl⟩

/-- The built entry world holds exactly the declared entry locks. -/
theorem eintrittOf_passt (sp : Speicher D) (code : Faden → D.Fn) (g : Faden) :
    EintrittPasst (code g) (eintrittOf sp code g) := by
  intro L
  show Res.held L ∈ Signatur.anfang D (D.signatur (code g)) ↔
    L ∈ offen (eintrittOf sp code g).spur
  unfold eintrittOf
  have hspur : (sp.welt (spurFuer (Signatur.anfang D (D.signatur (code g))))).spur =
      spurFuer (Signatur.anfang D (D.signatur (code g))) := rfl
  rw [hspur]
  exact (mem_offen_spurFuer _ L).symm

/-- The invariant sight follows from the entry: no separate sight premise
    is owed (`heldIn_invarianten` over the two-sided entry set). -/
theorem sicht_aus_eintritt (P : Programm D) (fn : D.Fn) (σ : World D)
    (hE : EintrittPasst (D := D) fn σ) : InvSichtHaelt (D := D) fn σ :=
  fun i hi => heldIn_invarianten P fn (eintrittHeldIn_aus_Passt hE) i hi

/-- Every spur has one step per thread entry: the world history counts steps. -/
theorem spurLaenge (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
    (hspur : PCSpur P O passes prog (GenStart sp) Mx pcx trx) :
    Mx.welten.length = trx.length + 1 := by
  induction hspur with
  | leer => simp [GenStart]
  | schritt M M' pc pc' g _hs hs _trx _htr ih =>
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩ <;>
      simp_all

/-- The last recorded world carries the live memory: every step appends
    its post-world and installs its memory. -/
theorem letzteSpeicher (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand)
    (h : PCReach P O passes prog (GenStart sp) Mx pcx) :
    ∀ w : World D, Mx.welten.getLast? = some w → w.speicher = Mx.speicher := by
  induction h with
  | start =>
    intro w hw
    simp [GenStart] at hw ⊢
    subst hw
    rfl
  | step M M' pc pc' g _hmid hs _ih =>
    intro w hw
    rcases hs with ⟨V, l, Γ, Λ, Λ', s, ρ, hleaf, hΛ, σ', neu, hstep, hneu, hkn, Λa, cs, hpc, hΛa, hmark, hcar⟩ |
      ⟨L, hself, hrang, hfrei, hpc⟩ | ⟨L, hhaelt, hpc⟩
    · simp_all
    · simp only [List.getLast?_append] at hw
      simp at hw
      subst hw
      exact speicher_welt_speicher _ _
    · simp only [List.getLast?_append] at hw
      simp at hw
      subst hw
      exact speicher_welt_speicher _ _

/-- The empty run is disciplined: every leg closes vacuously. -/
theorem gesittet_nil : Gesittet ([] : Lauf D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f j
    have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
    rw [hsp]
    exact konsistent_nil
  · intro f j e he
    have hsp : Lauf.spur ([] : Lauf D) f j = [] := by simp [Lauf.spur]
    rw [hsp] at he
    simp at he
  · intro j f L h hi g hne
    simp at hi
  · intro i j f g m s s' ei ej hi hj hm hm'
    simp at hi
  · intro i j f g o ei ej hi hj ht1 ht2 hu
    simp at hi

/-- The empty run interleaves only declared pairs: vacuous. -/
theorem beschraenkt_nil (Nb : Nebeneinander) :
    BeschraenkteVerschraenkung (D := D) Nb [] := by
  intro i j f g ei ej hi hj hne
  simp at hi

/-- A `vertragVon` contract IS its signature: the write maps coincide
    by computation. This is the typing step of the frame wiring: an
    honest firing's contract writes are its function's writes. -/
theorem vertragVon_schreibt (f : D.Fn) :
    (vertragVon D f).schreibt = D.schreibt f := rfl

/-- Global analogue of `vertragVon_schreibt`. -/
theorem vertragVon_gschreibt (f : D.Fn) :
    (vertragVon D f).gschreibt = D.gschreibt f := rfl

/-- Honest derivations, indexed by the `PCReach` derivation they track:
    lock steps as in `PCSchritt`, and every fired leaf carries its
    thread's own contract (`hV`). The machine does not enforce this --
    a leaf with another contract and the same footprint would fire just
    as well -- so it travels as the per-run firing discipline
    (`hHonest` of the main theorem), in the same role as the witness
    duties of `kette_mit_zeugen`. No premise below quantifies over
    program syntax: the contract identity is constructor data. -/
inductive EhrlichAbleitung (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D) (code : Faden → D.Fn) :
    (Mx : GenMaschine D) → (pcx : PCStand) →
    PCReach P O passes prog (GenStart sp) Mx pcx → List Faden → Prop where
  | leer : EhrlichAbleitung P O passes prog sp code (GenStart sp) (fun _ => 0)
      PCReach.start []
  | schrittNehmen (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
      (g : Faden) (L : D.Lock) (hself : L ∉ offen (Mx.spuren g))
      (hrang : ∀ K ∈ offen (Mx.spuren g), D.rang K < D.rang L)
      (hfrei : GenFrei Mx g L)
      (hpc : (prog g)[pcx g]? = some (PCAtom.take L))
      (hmid : PCReach P O passes prog (GenStart sp) Mx pcx)
      (hE : EhrlichAbleitung P O passes prog sp code Mx pcx hmid trx) :
      EhrlichAbleitung P O passes prog sp code
        ⟨Mx.speicher, genUpdate Mx.spuren g (Ereignis.nimmt L (offen (Mx.spuren g)) :: Mx.spuren g),
         Mx.lauf ++ genEigen g [Ereignis.nimmt L (offen (Mx.spuren g))], Mx.start,
         Mx.welten ++ [Mx.speicher.welt (Ereignis.nimmt L (offen (Mx.spuren g)) :: Mx.spuren g)], Mx.tiefe + 1⟩
        (pcAdvance pcx g)
        (PCReach.step Mx _ pcx _ g hmid
          (PCSchritt.take Mx pcx g L hself hrang hfrei hpc))
        (trx ++ [g])
  | schrittGeben (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
      (g : Faden) (L : D.Lock) (hhaelt : L ∈ offen (Mx.spuren g))
      (hpc : (prog g)[pcx g]? = some (PCAtom.rel L))
      (hmid : PCReach P O passes prog (GenStart sp) Mx pcx)
      (hE : EhrlichAbleitung P O passes prog sp code Mx pcx hmid trx) :
      EhrlichAbleitung P O passes prog sp code
        ⟨Mx.speicher, genUpdate Mx.spuren g (Ereignis.gibt L :: Mx.spuren g),
         Mx.lauf ++ genEigen g [Ereignis.gibt L], Mx.start,
         Mx.welten ++ [Mx.speicher.welt (Ereignis.gibt L :: Mx.spuren g)], Mx.tiefe + 1⟩
        (pcAdvance pcx g)
        (PCReach.step Mx _ pcx _ g hmid
          (PCSchritt.rel Mx pcx g L hhaelt hpc))
        (trx ++ [g])
  | schrittBlatt (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
      (g : Faden) (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (hleaf : s.istBlatt = true)
      (hΛ : HeldGenau Λ (offen (Mx.spuren g)))
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (Mx.weltVon g) ρ).welt = some σ')
      (hneu : σ'.spur = neu ++ Mx.spuren g)
      (hkn : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu)
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog g)[pcx g]? = some (PCAtom.leaf Λa cs))
      (hΛa : Λa = Λ)
      (hmark : ∀ e ∈ neu, ∀ (m : D.Marke) (st : Nat),
        Res.marke m st ∈ e.lambda → m ∈ PCAtom.marks (PCAtom.leaf Λa cs))
      (hcar : ∀ e ∈ neu, ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf Λa cs))
      (hV : V = vertragVon D (code g))
      (hmid : PCReach P O passes prog (GenStart sp) Mx pcx)
      (hE : EhrlichAbleitung P O passes prog sp code Mx pcx hmid trx) :
      EhrlichAbleitung P O passes prog sp code
        ⟨σ'.speicher, genUpdate Mx.spuren g σ'.spur,
         Mx.lauf ++ genEigen g neu, Mx.start, Mx.welten ++ [σ'], Mx.tiefe + 1⟩
        (pcAdvance pcx g)
        (PCReach.step Mx _ pcx _ g hmid
          (PCSchritt.leaf Mx pcx g V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu
            hkn Λa cs hpc hΛa hmark hcar))
        (trx ++ [g])

/-- The code frame of an honest fired step: the contract frame widened
    to the thread's code frame through the honesty identity plus the
    signature coincidence (`vertragVon_schreibt`/`_gschreibt`), then
    transported from the acting thread's world to the chain worlds
    through memory equalities. Every premise is load-bearing: the firing
    data feeds `blatt_rahmen_vertrag`, `hV` plus the signature lemmas
    feed the widening, `hvor` the transport. -/
theorem blattRahmenEhrlich (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (g : Faden)
    (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hΛ : HeldGenau Λ (offen (M.spuren g)))
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon g) ρ).welt = some σ')
    (code : Faden → D.Fn)
    (hV : V = vertragVon D (code g))
    (vor : World D) (hvor : vor.speicher = M.speicher) :
    Rahmen (D.schreibt (code g)) (D.gschreibt (code g)) vor σ' := by
  have hR0 := blatt_rahmen_vertrag O passes hO M g V l Γ Λ Λ' s ρ hΛ σ' hstep
  have hW : ∀ t, V.schreibt t = true → D.schreibt (code g) t = true := by
    intro t ht
    rw [hV, vertragVon_schreibt] at ht
    exact ht
  have hG : ∀ x, V.gschreibt x = true → D.gschreibt (code g) x = true := by
    intro x hx
    rw [hV, vertragVon_gschreibt] at hx
    exact hx
  have hR1 := hR0.weiter hW hG
  refine ⟨?_, ?_⟩
  · intro t ht k2 f2
    have h1 := hR1.1 t ht k2 f2
    have h3 : (vor.speicher.welt vor.spur).slots t k2 f2 = vor.speicher.slots t k2 f2 := rfl
    rw [Speicher.welt_speicher, hvor] at h3
    have h4 : (M.weltVon g).slots t k2 f2 = M.speicher.slots t k2 f2 := rfl
    rw [h4] at h1
    rw [h3]
    exact h1
  · intro x hx
    have h1 := hR1.2 x hx
    have h3 : (vor.speicher.welt vor.spur).globs x = vor.speicher.globs x := rfl
    rw [Speicher.welt_speicher, hvor] at h3
    have h4 : (M.weltVon g).globs x = M.speicher.globs x := rfl
    rw [h4] at h1
    rw [h3]
    exact h1

/-- The prefix last world carries the prefix memory, from the length
    equation plus the reachability invariant. -/
theorem KetteVorSpeicher (P : Programm D) (O : Orakel D) (passes : Nat)
    (prog : PCProg D) (sp : Speicher D)
    (Mx : GenMaschine D) (pcx : PCStand) (trx : List Faden)
    (hLen : Mx.welten.length = trx.length + 1)
    (hmid : PCReach P O passes prog (GenStart sp) Mx pcx) :
    ∀ vor : World D, Mx.welten[trx.length]? = some vor → vor.speicher = Mx.speicher := by
  intro vor hvor
  have hget : Mx.welten.getLast? = some vor := by
    have e : Mx.welten.getLast? = Mx.welten[Mx.welten.length - 1]? :=
      List.getLast?_eq_getElem?
    have hn : Mx.welten.length - 1 = trx.length := by omega
    rw [e, hn]
    exact hvor
  exact letzteSpeicher P O passes prog sp Mx pcx hmid vor hget

/-- One chain step: old positions ride the prefix chain, the new position
    closes by the supplied frame. Every premise is load-bearing: `hJw`/
    `hJsf`/`hJcode` feed the old transport, `hLen` the index arithmetic,
    `w`/`hNeu` the new step, `P`/`sp`/`code` the record fields. -/
theorem kette_schritt_rahmen2 (P : Programm D) (sp : Speicher D) (code : Faden → D.Fn)
    (M : GenMaschine D) (tr : List Faden) (g : Faden)
    (J : GemeinsamerLauf (D := D) ketteNb)
    (hJw : J.welten = M.welten) (hJsf : J.schrittFaden = tr) (hJcode : J.code = code)
    (hLen : M.welten.length = tr.length + 1)
    (w : World D)
    (hNeu : ∀ vor : World D, M.welten[tr.length]? = some vor →
      Rahmen (D.schreibt (code g)) (D.gschreibt (code g)) vor w) :
    ∃ J' : GemeinsamerLauf (D := D) ketteNb,
      J'.welten = M.welten ++ [w] ∧ J'.schrittFaden = tr ++ [g] ∧ J'.code = code := by
  have hSchrittJ : ∀ (k : Nat) (g0 : Faden) (vor nach : World D), (tr ++ [g])[k]? = some g0 → (M.welten ++ [w])[k]? = some vor → (M.welten ++ [w])[k + 1]? = some nach → g0 ∈ g :: J.faeden ∧ Rahmen (D.schreibt (code g0)) (D.gschreibt (code g0)) vor nach := by
    intro k g0 vor nach hk hkv hkn
    by_cases hlt : k < tr.length
    · have e1 : (tr ++ [g])[k]? = tr[k]? := List.getElem?_append_left hlt
      rw [e1] at hk
      have hltM : k < M.welten.length := by omega
      have e2 : (M.welten ++ [w])[k]? = M.welten[k]? := List.getElem?_append_left hltM
      rw [e2] at hkv
      have hJkv : J.welten[k]? = some vor := by rw [hJw]; exact hkv
      have hltM1 : k + 1 < M.welten.length := by omega
      have e3 : (M.welten ++ [w])[k + 1]? = M.welten[k + 1]? := List.getElem?_append_left hltM1
      rw [e3] at hkn
      have hJkn : J.welten[k + 1]? = some nach := by rw [hJw]; exact hkn
      have hkJ : J.schrittFaden[k]? = some g0 := by rw [hJsf]; exact hk
      obtain ⟨hmem, hR⟩ := J.hSchritt k g0 vor nach hkJ hJkv hJkn
      refine ⟨List.mem_cons_of_mem g hmem, ?_⟩
      have hc : J.code g0 = code g0 := by rw [hJcode]
      rw [hc] at hR
      exact hR
    · by_cases heq : k = tr.length
      · subst heq
        have eNew : (tr ++ [g])[tr.length]? = some g := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [eNew] at hk
        have hg0 : g0 = g := (Option.some_inj.mp hk).symm
        rw [hg0]
        have eW : (M.welten ++ [w])[tr.length]? = M.welten[tr.length]? := List.getElem?_append_left (by omega)
        rw [eW] at hkv
        have hle2 : M.welten.length ≤ tr.length + 1 := by omega
        have eW2 : (M.welten ++ [w])[tr.length + 1]? = some w := by
          rw [List.getElem?_append_right hle2]
          have hsub : tr.length + 1 - M.welten.length = 0 := by omega
          rw [hsub]
          rfl
        rw [eW2] at hkn
        have hnach : w = nach := Option.some_inj.mp hkn
        subst hnach
        refine ⟨List.mem_cons.mpr (Or.inl rfl), hNeu vor hkv⟩
      · have hle : tr.length ≤ k := by omega
        have eNone : (tr ++ [g])[k]? = none := by
          rw [List.getElem?_append_right hle, List.getElem?_eq_none_iff,
            List.length_singleton]
          omega
        rw [eNone] at hk
        simp at hk
  refine ⟨{ faeden := g :: J.faeden, code := code,
            eintritt := eintrittOf sp code,
            welten := M.welten ++ [w], schrittFaden := tr ++ [g], l := ([] : Lauf D),
            hKette := by simp [hLen],
            hSchritt := hSchrittJ,
              hPaar := by intro f hf g' hg' hne; exact trivial,
              hGesittet := gesittet_nil, hBeschraenkt := beschraenkt_nil ketteNb,
              hEintritt := by intro f hf; exact eintrittOf_passt sp code f,
              hSchuld := by intro f hf; exact schuldnerHaelt_gilt (code f),
              hInvSicht := by intro f hf; exact sicht_aus_eintritt P (code f) _ (eintrittOf_passt sp code f) },
            rfl, rfl, rfl⟩

/-- The chain from an honest derivation: worlds and step threads by
    construction, for any number of threads, with the `PCSpur` rebuilt
    alongside. The recorded run stays empty (discipline vacuous); entry
    is built to fit; debt holds by U003; sight follows from entry; leaf
    frames come from the honest firing, lock frames from unchanged
    memory. Every premise is load-bearing: `hO` feeds the leaf frame,
    `hE` the induction. -/
theorem kette_aus_ehrlich (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (prog : PCProg D) (code : Faden → D.Fn)
    (Mx : GenMaschine D) (pcx : PCStand)
    (h : PCReach P O passes prog (GenStart sp) Mx pcx) (trx : List Faden)
    (hE : EhrlichAbleitung P O passes prog sp code Mx pcx h trx) :
    ∃ J : GemeinsamerLauf (D := D) ketteNb,
      PCSpur P O passes prog (GenStart sp) Mx pcx trx ∧
      J.welten = Mx.welten ∧ J.schrittFaden = trx ∧ J.code = code := by
  induction hE with
  | leer =>
    refine ⟨{ faeden := [], code := code, eintritt := eintrittOf sp code,
              welten := (GenStart sp).welten, schrittFaden := ([] : List Faden),
              l := ([] : Lauf D),
              hKette := by simp [GenStart],
              hSchritt := by intro k f vor nach hk _ _; simp at hk,
              hPaar := by intro f hf g hg hne; simp at hf,
              hGesittet := gesittet_nil, hBeschraenkt := beschraenkt_nil ketteNb,
              hEintritt := by intro f hf; simp at hf,
              hSchuld := by intro f hf; simp at hf,
              hInvSicht := by intro f hf; simp at hf },
            PCSpur.leer, rfl, rfl, rfl⟩
  | schrittNehmen Mx pcx trx g L hself hrang hfrei hpc hmid _hE ih =>
    obtain ⟨J, hspurP, hJw, hJsf, hJcode⟩ := ih
    have hLen : Mx.welten.length = trx.length + 1 := spurLaenge P O passes prog sp Mx pcx trx hspurP
    have hLast := KetteVorSpeicher P O passes prog sp Mx pcx trx hLen hmid
    have hNeu : ∀ vor : World D, Mx.welten[trx.length]? = some vor → Rahmen (D.schreibt (code g)) (D.gschreibt (code g)) vor (Mx.speicher.welt (Ereignis.nimmt L (offen (Mx.spuren g)) :: Mx.spuren g)) := by
      intro vor hkv
      have hvor : vor.speicher = Mx.speicher := hLast vor hkv
      refine ⟨?_, ?_⟩
      · intro t ht k2 f2
        have h3 : (vor.speicher.welt vor.spur).slots t k2 f2 = vor.speicher.slots t k2 f2 := rfl
        rw [Speicher.welt_speicher, hvor] at h3
        have h4 : (Mx.speicher.welt (Ereignis.nimmt L (offen (Mx.spuren g)) :: Mx.spuren g)).slots t k2 f2 = Mx.speicher.slots t k2 f2 := rfl
        rw [h4, h3]
      · intro x hx
        have h3 : (vor.speicher.welt vor.spur).globs x = vor.speicher.globs x := rfl
        rw [Speicher.welt_speicher, hvor] at h3
        have h4 : (Mx.speicher.welt (Ereignis.nimmt L (offen (Mx.spuren g)) :: Mx.spuren g)).globs x = Mx.speicher.globs x := rfl
        rw [h4, h3]
    obtain ⟨J', hJw', hJsf', hJcode'⟩ :=
      kette_schritt_rahmen2 P sp code Mx trx g J hJw hJsf hJcode hLen (Mx.speicher.welt (Ereignis.nimmt L (offen (Mx.spuren g)) :: Mx.spuren g)) hNeu
    refine ⟨J', PCSpur.schritt Mx _ pcx _ g hmid (PCSchritt.take Mx pcx g L hself hrang hfrei hpc) trx hspurP, hJw', hJsf', hJcode'⟩
  | schrittGeben Mx pcx trx g L hhaelt hpc hmid _hE ih =>
    obtain ⟨J, hspurP, hJw, hJsf, hJcode⟩ := ih
    have hLen : Mx.welten.length = trx.length + 1 := spurLaenge P O passes prog sp Mx pcx trx hspurP
    have hLast := KetteVorSpeicher P O passes prog sp Mx pcx trx hLen hmid
    have hNeu : ∀ vor : World D, Mx.welten[trx.length]? = some vor → Rahmen (D.schreibt (code g)) (D.gschreibt (code g)) vor (Mx.speicher.welt (Ereignis.gibt L :: Mx.spuren g)) := by
      intro vor hkv
      have hvor : vor.speicher = Mx.speicher := hLast vor hkv
      refine ⟨?_, ?_⟩
      · intro t ht k2 f2
        have h3 : (vor.speicher.welt vor.spur).slots t k2 f2 = vor.speicher.slots t k2 f2 := rfl
        rw [Speicher.welt_speicher, hvor] at h3
        have h4 : (Mx.speicher.welt (Ereignis.gibt L :: Mx.spuren g)).slots t k2 f2 = Mx.speicher.slots t k2 f2 := rfl
        rw [h4, h3]
      · intro x hx
        have h3 : (vor.speicher.welt vor.spur).globs x = vor.speicher.globs x := rfl
        rw [Speicher.welt_speicher, hvor] at h3
        have h4 : (Mx.speicher.welt (Ereignis.gibt L :: Mx.spuren g)).globs x = Mx.speicher.globs x := rfl
        rw [h4, h3]
    obtain ⟨J', hJw', hJsf', hJcode'⟩ :=
      kette_schritt_rahmen2 P sp code Mx trx g J hJw hJsf hJcode hLen (Mx.speicher.welt (Ereignis.gibt L :: Mx.spuren g)) hNeu
    refine ⟨J', PCSpur.schritt Mx _ pcx _ g hmid (PCSchritt.rel Mx pcx g L hhaelt hpc) trx hspurP, hJw', hJsf', hJcode'⟩
  | schrittBlatt Mx pcx trx g V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar hV hmid _hE ih =>
    obtain ⟨J, hspurP, hJw, hJsf, hJcode⟩ := ih
    have hLen : Mx.welten.length = trx.length + 1 := spurLaenge P O passes prog sp Mx pcx trx hspurP
    have hLast := KetteVorSpeicher P O passes prog sp Mx pcx trx hLen hmid
    have hNeu : ∀ vor : World D, Mx.welten[trx.length]? = some vor → Rahmen (D.schreibt (code g)) (D.gschreibt (code g)) vor σ' := by
      intro vor hkv
      exact blattRahmenEhrlich O passes hO Mx g V l Γ Λ Λ' s ρ hΛ σ' hstep code hV vor (hLast vor hkv)
    obtain ⟨J', hJw', hJsf', hJcode'⟩ :=
      kette_schritt_rahmen2 P sp code Mx trx g J hJw hJsf hJcode hLen σ' hNeu
    refine ⟨J', PCSpur.schritt Mx _ pcx _ g hmid (PCSchritt.leaf Mx pcx g V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar) trx hspurP, hJw', hJsf', hJcode'⟩

/-- **The chain from a machine run, N threads.** Every `PCReach` run
    over the extracted program whose steps fire their threads' own
    contracts carries a joint chain with the same worlds and step
    threads, for any number of threads and any interleaving. The code
    map doubles as the extraction map; honesty (`hHonest`) is the
    per-run firing discipline the machine does not enforce. No premise
    quantifies over program syntax. -/
theorem kette_aus_lauf_voll (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (code : Faden → D.Fn) (tabs : List D.Tab) (globs : List D.Glob)
    (M : GenMaschine D) (pc : PCStand)
    (h : PCReach P O passes (Extraktion.progAus P code tabs globs) (GenStart sp) M pc)
    (hHonest : ∃ trx : List Faden,
      EhrlichAbleitung P O passes (Extraktion.progAus P code tabs globs) sp code M pc h trx) :
    ∃ (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (tr : List Faden),
      PCSpur P O passes (Extraktion.progAus P code tabs globs) (GenStart sp) M pc tr ∧
        J.welten = M.welten ∧ J.schrittFaden = tr := by
  obtain ⟨trx, hE⟩ := hHonest
  obtain ⟨J, hspur, hJw, hJsf, _hJcode⟩ :=
    kette_aus_ehrlich P O passes hO sp (Extraktion.progAus P code tabs globs) code M pc h trx hE
  exact ⟨_, J, trx, hspur, hJw, hJsf⟩

/-- Writer signature: nothing held, writes the table, no result. -/
def writerSig2 : Signatur Unit Empty Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Reader signature: nothing held, writes nothing, returns a boolean. -/
def readerSig2 : Signatur Unit Empty Empty Empty where
  params := []
  erg := some .bool
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- Two-function lock-free declaration: one table with one boolean slot,
    no locks, no guards. `true` writes the table, `false` only reads it
    (same writer/reader split as `refP`'s `einzahlen`/`lies`, but with
    empty holdings so a leaf can fire straight from `GenStart`). -/
def D2 : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .bool
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun _ => false
  ggeteilt := fun e => nomatch e
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Bool
  sig := fun | true => 0 | false => 1
  sigNr := fun | 0 => writerSig2 | _ => readerSig2
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g => nomatch g

/-- Index `0` into the single-slot table, at empty holdings. -/
def idx2 : Expr D2 [] [] (.index (D2.count ())) :=
  .weiter (by decide) (by decide) (.lit 0)

/-- Constant `true`, at empty holdings. -/
def wahr2 : Expr D2 [] [] .bool :=
  .wahr

/-- The writer leaf `konto[0] := true`, typed over the writer's own
    contract (so honesty below holds by `rfl`). -/
def writeLeaf2 : Stmt D2 (vertragVon D2 true) false [] [] [] :=
  .assignSlot () () idx2 wahr2 rfl (fun w => nomatch w)

/-- The writer leaf is a leaf. -/
theorem writeLeaf2_blatt : writeLeaf2.istBlatt = true := rfl

/-- The writer body: write, then return. -/
def rumpfSchreibt2 : Endblock D2 (vertragVon D2 true) false [] [] :=
  .cons writeLeaf2 (.ret .keine (by rfl))

/-- The slot read for the reader's return value. -/
def liesSlot2 : Expr D2 [] [] .bool :=
  .slot () () idx2 (fun w => nomatch w)

/-- The reader body: return the slot (reads only). -/
def rumpfLiest2 : Endblock D2 (vertragVon D2 false) false [] [] :=
  .ret (.wert liesSlot2) (by rfl)

/-- The program: trivial contracts, writer/reader bodies. -/
def P2 : Programm D2 where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := fun | true => rumpfSchreibt2 | false => rumpfLiest2

/-- The witness oracle: no axioms, no registers, nothing visible. -/
def O2 : Orakel D2 where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g => nomatch g

/-- The oracle is good. -/
theorem O2_gut : GutO O2 := by
  intro a σ ρ
  exact nomatch a

/-- The start memory: the slot reads `false`. -/
def sp2 : Speicher D2 :=
  ⟨fun _ _ _ => false, fun g => nomatch g⟩

/-- Thread map: thread 0 reads, all others write. -/
def code2 : Faden → D2.Fn
  | 0 => false
  | _ => true

/-- The extracted thread program thread 1 runs. -/
def prog2X : PCProg D2 :=
  Extraktion.progAus P2 code2 [()] []
/-- The post-write world: the slot read through the read hull, then
    written `true`. Stated symbolically so the firing equation closes
    by `rfl`. -/
def sigma2' : World D2 :=
  (((GenStart sp2).weltVon 1).lese [] (idx2.orte ++ wahr2.orte)).schreibSlot ()
    [] 0 () true

/-- The new events: the single write (the read hull is empty). -/
def neu2 : List (Ereignis D2) :=
  [Ereignis.zugriff () true []
    (((GenStart sp2).weltVon 1).lese [] (idx2.orte ++ wahr2.orte)).haelt]

/-- The atom carriers thread 1 points at. -/
def cs2 : List (D2.Tab ⊕ D2.Glob) :=
  Extraktion.stmtTraeger [()] [] writeLeaf2 ++ Extraktion.stmtOrte writeLeaf2

/-- Firing the writer leaf from the start world writes `true`. -/
theorem hstep2 :
    (execStmt O2 0 keinRuf writeLeaf2 ((GenStart sp2).weltVon 1) Env.nil).welt =
      some sigma2' := rfl

/-- The new trace is exactly the write event. -/
theorem hneu2 : sigma2'.spur = neu2 ++ ((GenStart sp2).spuren 1) := rfl

/-- No lock-taking hides in the write event. -/
theorem hkn2 :
    ∀ (L : D2.Lock) (h : List D2.Lock), Ereignis.nimmt L h ∉ neu2 := by
  intro L h hm
  simp [neu2] at hm

/-- Empty holdings hold exactly: nothing is held at the start. -/
theorem hLambda2 :
    HeldGenau ([] : List (Res D2)) (offen ((GenStart sp2).spuren 1)) := by
  have e : ((GenStart sp2).spuren 1 : List (Ereignis D2)) = [] := rfl
  have e2 : offen ([] : List (Ereignis D2)) = [] := rfl
  rw [e, e2]
  intro L
  constructor <;> intro h <;> simp at h

/-- Thread 1 points at the writer leaf at counter zero. -/
theorem hpc2 :
    (prog2X 1)[((fun _ => 0) 1)]? =
      some (PCAtom.leaf ([] : List (Res D2)) cs2) := rfl

/-- The step is no oracle call. -/
theorem hax2 :
    match writeLeaf2 with
    | .axiomCall _ _ _ _ _ _ _ => False
    | _ => True := by
  unfold writeLeaf2
  trivial

/-- Event footprints of the firing, from the execution link. -/
theorem hEreignis2 :
    (∀ e ∈ neu2, e.lambda = ([] : List (Res D2))) ∧
    (∀ e ∈ neu2, ∀ o, e.traeger = some o → o ∈ cs2) :=
  Extraktion.execEreignis_aus_blatt_ohne_axiomCall O2 0 writeLeaf2
    writeLeaf2_blatt hax2 [()] [] ((GenStart sp2).weltVon 1) Env.nil
    sigma2' neu2 hstep2 hneu2

/-- Mark cover for the pointed-to atom (no marks anywhere). -/
theorem hmark2 : ∀ e ∈ neu2, ∀ (m : D2.Marke) (st : Nat),
    Res.marke m st ∈ e.lambda → m ∈ PCAtom.marks (PCAtom.leaf [] cs2) := by
  intro e he m st hm
  rw [hEreignis2.1 e he] at hm
  simp at hm

/-- Carrier cover for the pointed-to atom. -/
theorem hcar2 : ∀ e ∈ neu2, ∀ o, e.traeger = some o →
    o ∈ PCAtom.carriers (PCAtom.leaf [] cs2) := by
  intro e he o ho
  have hmem := hEreignis2.2 e he o ho
  simp only [PCAtom.carriers]
  exact hmem

/-- The reached machine after the writing leaf. -/
def M2 : GenMaschine D2 :=
  ⟨sigma2'.speicher, genUpdate ((GenStart sp2).spuren) 1 sigma2'.spur,
   (GenStart sp2).lauf ++ genEigen 1 neu2, (GenStart sp2).start,
   (GenStart sp2).welten ++ [sigma2'], (GenStart sp2).tiefe + 1⟩

/-- The counter after the writing leaf. -/
def pc2 : PCStand :=
  pcAdvance (fun _ => 0) 1

/-- The writing leaf fires as a PC step over the extracted program. -/
theorem hs2 : PCSchritt P2 O2 0 prog2X (GenStart sp2) (fun _ => 0) 1 M2 pc2 :=
  PCSchritt.leaf (GenStart sp2) (fun _ => 0) 1 (vertragVon D2 true) false [] [] []
    writeLeaf2 Env.nil writeLeaf2_blatt hLambda2 sigma2' neu2 hstep2 hneu2 hkn2
    [] cs2 hpc2 rfl hmark2 hcar2

/-- The one-step writing run from `GenStart`. -/
theorem h2B : PCReach P2 O2 0 prog2X (GenStart sp2) M2 pc2 :=
  PCReach.step _ _ _ _ 1 PCReach.start hs2

/-- The firing is honest: it carries the writer's own contract. -/
theorem hV2 : vertragVon D2 true = vertragVon D2 (code2 1) := rfl

/-- The honest derivation for the witness run. -/
theorem hHon2B : EhrlichAbleitung P2 O2 0 prog2X sp2 code2 M2 pc2 h2B [1] :=
  EhrlichAbleitung.schrittBlatt (GenStart sp2) (fun _ => 0) [] 1
    (vertragVon D2 true) false [] [] [] writeLeaf2 Env.nil writeLeaf2_blatt
    hLambda2 sigma2' neu2 hstep2 hneu2 hkn2 [] cs2 hpc2 rfl hmark2 hcar2 hV2
    PCReach.start EhrlichAbleitung.leer

/-- The final memory carries `true` at the slot. -/
theorem slotTrue2 : M2.speicher.slots () 0 () = true :=
  storeSlot_hit (D := D2)
    (((GenStart sp2).weltVon 1).lese [] (idx2.orte ++ wahr2.orte)) () 0 () true

/-- Memory really moved: `true` at the end, `false` at the start. -/
theorem neSchreibt2 : M2.speicher.slots () 0 () ≠ sp2.slots () 0 () := by
  rw [slotTrue2]
  intro hcon
  have h0 : sp2.slots () 0 () = false := rfl
  rw [h0] at hcon
  exact Bool.false_ne_true hcon.symm
/-- Witness for `kette_aus_lauf_voll` on the two-function program: all
    premises instantiated jointly -- `code2` maps thread 0 to the
    reader and thread 1 to the writer, the run is the one-step writing
    leaf `h2B` with its honest derivation `hHon2B`. Non-degenerate: the
    writer writes the table and memory moves (`false` to `true`). -/
theorem kette_aus_lauf_voll_zeuge :
    ∃ (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D2) Nb) (tr : List Faden),
      GutO O2 ∧
      PCReach P2 O2 0 prog2X (GenStart sp2) M2 pc2 ∧
      (∃ trx : List Faden, EhrlichAbleitung P2 O2 0 prog2X sp2 code2 M2 pc2 h2B trx) ∧
      PCSpur P2 O2 0 prog2X (GenStart sp2) M2 pc2 tr ∧
      J.welten = M2.welten ∧ J.schrittFaden = tr ∧
      (∃ t, (vertragVon D2 true).schreibt t = true) ∧
      M2.speicher.slots () 0 () ≠ sp2.slots () 0 () := by
  obtain ⟨_Nb, J, tr, hspur, hJw, hJsf⟩ :=
    kette_aus_lauf_voll P2 O2 0 O2_gut sp2 code2 [()] [] M2 pc2 h2B ⟨[1], hHon2B⟩
  exact ⟨_, J, tr, O2_gut, h2B, ⟨[1], hHon2B⟩, hspur, hJw, hJsf,
    ⟨(), rfl⟩, neSchreibt2⟩

/-- The old full-rights premise is false on the two-function setup:
    the reader (`code2 0`) writes nothing, so no code map that runs it
    can write every table. This is exactly where lanes 35-37 sank. -/
theorem hVollT_falsch2 :
    ¬ ∀ (g : Faden) (t : D2.Tab), D2.schreibt (code2 g) t = true := by
  intro hAll
  have h0 := hAll 0 ()
  have e : D2.schreibt (code2 0) () = false := rfl
  rw [e] at h0
  exact Bool.false_ne_true h0

/-! ## CUTS:
  - Name: `MaschinenKette.lean:322` already proves
    `Gabbro.Grammatik.kette_aus_lauf_voll` (single-thread lock-only,
    concluding a guarded `SerialLink`, no thread trace). To keep that
    theorem and the whole-project build intact, the N-thread theorem
    here lives in namespace `KetteVoll` as
    `Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll`, and so does its
    witness. No existing file was touched.
  - Restriction vs the bare target: the proved theorem runs over the
    extracted program `Extraktion.progAus P code tabs globs` (the code
    map doubles as the extraction map, as in `ziel_nutzer_last_aus_pc`)
    and takes honesty `hHonest` (an `EhrlichAbleitung` about the run's
    own derivation `h`). Both shape the run class, neither quantifies
    over program syntax. `progAus` alone does NOT pin a fired leaf's
    contract -- a leaf with another contract and the same footprint
    would fire just as well, and a writing one would break the frame
    outside its rights -- so honesty is load-bearing firing discipline
    (same status as the witness duties of `kette_mit_zeugen`), not
    bureaucracy. What typing contributes: an honest firing's contract
    IS its function's (`hV`), whose writes are the signature's
    (`vertragVon_schreibt`/`_gschreibt`); the frame itself is derived
    from the fired step (`blatt_rahmen_vertrag` via `hO`), never
    posited. The bare premise-free shape is false already for empty
    `D.Fn` (runs exist, no chain does).
  - The recorded run of the built chain is empty (`J.l = []`): the goal
    needs only worlds and step threads, so `Gesittet`/`hBeschraenkt`
    close vacuously instead of via mark/carrier separation. A chain
    with `J.l = M.lauf` would additionally owe `PCMarkSep`/`PCUnsharedSep`.
  - Entry worlds are built to fit (`eintrittOf`); debt holds for every
    function by U003 (`schuldnerHaelt_gilt`); sight follows from entry
    (`sicht_aus_eintritt` via `heldIn_invarianten`).
  - Witness program: `refP` cannot serve -- its signatures hold the
    lock, so no `progAus` leaf can fire from `GenStart` (and no `locks`
    statement can open at its holdings: rank `0 < 0` fails). `D2` keeps
    the writer/reader split with empty holdings instead.
-/

#print axioms Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll
#print axioms Gabbro.Grammatik.KetteVoll.kette_aus_lauf_voll_zeuge
#print axioms Gabbro.Grammatik.KetteVoll.hVollT_falsch2

end KetteVoll

end Gabbro.Grammatik
