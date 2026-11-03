/-
  File:      Grammatik/ZielOrtRahmenSem.lean
  Subject:   THE CALLEE FRAME -- the handler class that bounds a callee by
             its declared writes (`RespektiertRahmen`), the user obligation
             against it (`KoerperGutR`), its weakening from the earlier
             obligations (`koerperGutR_of_G`, `koerperGutR_of_V`), and the
             machine fact that makes it sound on G: during a call, the
             caller's footprint carriers change only where the callee
             declares a write (`rufG_rahmen`).

  The finding of `Referenz104.lean` (`r4_einzahlen_nicht_V`): the handler
  class of `KoerperGut*` (`RespektiertVertraege`) constrains a callee only by
  its `ensures`. A caller that writes a slot and then calls a function that
  writes nothing (`lies`) cannot conclude the slot is unchanged -- a
  contract-respecting handler may answer with any world meeting the
  callee's `ensures`. The repair is the call analogue of `RahmenO` (the
  declared frame of an axiom): a normal answer of the handler to `f`
  changes only the carriers `f`'s signature declares as written
  (`D.schreibt f`, `D.gschreibt f`), and keeps the held locks.

  Soundness on G needs the machine to deliver the frame. It does, for the
  carriers a caller relies on (its footprint `fussOrteG`):
  * the thread's own steps while the callee (and its callees) run write only
    carriers the running function may write (`schritt_traeger`, the
    signature permission `hw` on every write), and a callee's write set is
    inside its caller's (`RufPasst.hw`/`hg` at the push), so every write
    during the call is a declared write of the callee;
  * another thread's step leaves the caller's footprint alone: every
    footprint carrier is guarded by a signature lock of the caller, held
    for the whole life of its frame (`rufG_haelt_signatur`), or written by
    no function (`fussOrtGB`), as in the rely of the head frame.
  The invariant `RahmenStapel` records both facts for every suspended frame
  of every thread; `rufG_rahmen` proves it on every reachable machine.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem.Teil1Basis
import all Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtRahmenSem.Teil1Basis
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
theorem rahmenStapel_cons {P : Programm D} {S : Speicher D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D} {F : RufRahmenG D} {rest : List (RufRahmenG D)} :
    RahmenStapel P S G (F :: rest) ↔
      ((∀ c, TraegerSchreibt G.1 c = true → TraegerSchreibt F.f c = true) ∧
      (∀ c ∈ fussOrteG P F.f, TraegerSchreibt G.1 c = false → TraegerGleich S G.2.2.speicher c) ∧
      RahmenStapel P S (RufSchluesselG F) rest) := Iff.rfl

/-- Memory that moved only where the key's function may write keeps the
    invariant (down the stack along the write-set chain). -/
theorem rahmenStapel_speicher {P : Programm D} {S S' : Speicher D} :
    ∀ {G : Σ f : D.Fn, Env D (D.params f) × World D} {st : List (RufRahmenG D)},
      RahmenStapel P S G st →
      (∀ c, TraegerSchreibt G.1 c = false → TraegerGleich S' S c) → RahmenStapel P S' G st
  | _, [], _, _ => trivial
  | G, F :: rest, h, hS => by
      obtain ⟨hk, hf, hr⟩ := rahmenStapel_cons.mp h
      refine rahmenStapel_cons.mpr ⟨hk, fun c hc hw => traegerGleich_trans (hS c hw) (hf c hc hw),
        rahmenStapel_speicher hr (fun c hw => hS c ?_)⟩
      cases hG : TraegerSchreibt G.1 c with
      | false => rfl
      | true =>
          exact absurd ((hk c hG).symm.trans hw) Bool.noConfusion

/-- Memory that kept every footprint carrier of every suspended frame keeps
    the invariant. -/
theorem rahmenStapel_fremd {P : Programm D} {S S' : Speicher D} :
    ∀ {G : Σ f : D.Fn, Env D (D.params f) × World D} {st : List (RufRahmenG D)},
      RahmenStapel P S G st →
      (∀ F ∈ st, ∀ c ∈ fussOrteG P F.f, TraegerGleich S' S c) → RahmenStapel P S' G st
  | _, [], _, _ => trivial
  | G, F :: rest, h, hS => by
      obtain ⟨hk, hf, hr⟩ := rahmenStapel_cons.mp h
      exact rahmenStapel_cons.mpr ⟨hk,
        fun c hc hw => traegerGleich_trans (hS F List.mem_cons_self c hc) (hf c hc hw),
        rahmenStapel_fremd hr (fun F' hF' => hS F' (List.mem_cons_of_mem _ hF'))⟩

/-- A push: the head frame (same function, parameters, entry world, a new
    residue) is suspended below the callee with key `G`. -/
theorem rahmenStapel_push {P : Programm D} {S S' : Speicher D} {F : RufRahmenG D}
    {st : List (RufRahmenG D)} (h : RahmenStapel P S (RufSchluesselG F) st)
    (hmem : ∀ c, TraegerSchreibt F.f c = false → TraegerGleich S' S c)
    (G : Σ f : D.Fn, Env D (D.params f) × World D)
    (hk : ∀ c, TraegerSchreibt G.1 c = true → TraegerSchreibt F.f c = true)
    (hG : ∀ c, TraegerGleich S' G.2.2.speicher c)
    (r : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D (vertragVon D F.f) l Γ Λ) :
    RahmenStapel P S' G (⟨F.f, F.rho, F.s0, r⟩ :: st) :=
  rahmenStapel_cons.mpr ⟨hk, fun c _ _ => hG c, rahmenStapel_speicher h hmem⟩

/-- A pop: the caller becomes the head. -/
theorem rahmenStapel_pop {P : Programm D} {S S' : Speicher D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D} {caller : RufRahmenG D}
    {rst : List (RufRahmenG D)} (h : RahmenStapel P S G (caller :: rst))
    (hmem : ∀ c, TraegerSchreibt G.1 c = false → TraegerGleich S' S c) :
    RahmenStapel P S' (RufSchluesselG caller) rst := by
  obtain ⟨hk, _, hr⟩ := rahmenStapel_cons.mp h
  refine rahmenStapel_speicher hr (fun c hw => hmem c ?_)
  cases hG : TraegerSchreibt G.1 c with
  | false => rfl
  | true => exact absurd ((hk c hG).symm.trans hw) Bool.noConfusion

/-- The suspended frame's agreement, read at a return world over the same
    memory. -/
theorem gleichOhne_of_stapel {P : Programm D} {S : Speicher D}
    {G : Σ f : D.Fn, Env D (D.params f) × World D} {F : RufRahmenG D}
    {rest : List (RufRahmenG D)} (h : RahmenStapel P S G (F :: rest)) (s1 : World D)
    (hs1 : s1.slots = S.slots ∧ s1.globs = S.globs) : GleichOhne G.1 (fussOrteG P F.f) G.2.2 s1 := by
  obtain ⟨_, hf, _⟩ := rahmenStapel_cons.mp h
  refine ⟨fun t ht hw => ?_, fun x hx hw => ?_⟩
  · have e : S.slots t = G.2.2.slots t := hf (.inl t) ht hw
    rw [hs1.1]
    exact e.symm
  · have e : S.globs x = G.2.2.globs x := hf (.inr x) hx hw
    rw [hs1.2]
    exact e.symm

section Maschine

variable {P : Programm D} {O : Orakel D} {passes : Nat}

set_option maxHeartbeats 1000000 in
/-- **The acting thread keeps its frame invariant** -- every rule of G: a
    push suspends the head below the callee (whose writes are inside the
    head's by `RufPasst`, whose entry memory is the current one); a pop
    removes the top suspended frame; every other rule keeps the stack and
    the head's key, and moves memory only where the head may write
    (`schritt_traeger`). -/
theorem rahmenStapel_akteur (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M')
    (h : RahmenStapel P M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel) :
    RahmenStapel P M'.speicher (RufSchluesselG (M'.faeden u).kopf) (M'.faeden u).stapel := by
  have hmem : ∀ c, TraegerSchreibt (M.faeden u).kopf.f c = false →
      TraegerGleich M'.speicher M.speicher c :=
    fun c hc => schritt_traeger hO hs c (Or.inr hc)
  cases hs with
  -- pushes
  | g1 hs =>
    cases hs with
    | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      subst hs0
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
    | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem
  | g2 hs =>
    cases hs with
    | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      subst hs0
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem
  | g3 hs =>
    cases hs with
    | dannBindCall l Γ Λ Λ' Λ'' τ g args he hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
      subst hs0
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
    | dannBindCallElse l Γ Λ Λ' Λ'' τ g args he hp hr err rest k ρ hhead hΛ s0 hs0 rho hrho neu
        hneu =>
      subst hs0
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
    | dannCallInd l Γ Λ Λ' Λ'' n p args hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      subst hs0; replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
        _
    | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
      subst hs0; replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
        _
    | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
        neu hneu =>
      subst hs0; replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
        _
    | dannBindCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      subst hs0; replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
        _
    | dannCallIndElse l Γ Λ Λ' Λ'' τ n p args he hp hr err rest k ρ hhead hΛ s0 hs0 g hg hv rho
        hrho neu hneu =>
      subst hs0; replace hp := RufPasst.vonPasst (D.passt_sig hg) hp
      simp only [rufUpdateG_self]
      exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
        _
    -- pops
    | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
        s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem
  | g4 hs =>
    cases hs with
    | rueckCons caller rst hpop Γ Λ e hperm rest ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu
        hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | dannRet l Γ Λ Λ'' e hperm rest k ρ hhead caller rst hpop hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv
        neu hneu hnw =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | dannRetBind lk Γk Λk Λk'' e hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc
        hcaller hΛ s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | rueckConsBind lk Γk Λk e hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller hΛ
        s1 hs1 g hfg rho hrho s0 hs0 v hv he neu hneu =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | rueckGrund r hperm ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g hfg rho
        hrho s0 hs0 rg hrg hn =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem
  | g5 hs =>
    cases hs with
    | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
        hfg rho hrho s0 hs0 rg hrg hn =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
        hfg rho hrho s0 hs0 rg hrg hn =>
      simp only [rufUpdateG_self]
      rw [hpop] at h
      exact rahmenStapel_pop h hmem
    -- every other rule keeps the stack and the head's key
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem
  | g6 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem
  | g7 hs =>
    cases hs with
    | _ =>
      simp only [rufUpdateG_self]
      exact rahmenStapel_speicher h hmem

/-- **Another thread's step keeps the frame invariant**: every footprint
    carrier of a suspended frame is guarded by a signature lock of its
    function, held by the frame's thread (`rufG_haelt_signatur`), or written
    by no function. -/
theorem rahmenStapel_andere (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M M' : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M)
    {u : Faden} (hs : RufSchrittG P O passes M u M') (t : Faden) (htu : t ≠ u)
    (h : RahmenStapel P M.speicher (RufSchluesselG (M.faeden t).kopf) (M.faeden t).stapel) :
    RahmenStapel P M'.speicher (RufSchluesselG (M'.faeden t).kopf) (M'.faeden t).stapel := by
  rw [rufSchrittG_fremd hs t htu]
  refine rahmenStapel_fremd h (fun F hF c hc => ?_)
  rcases fussOrtGB_ok P fs hvoll hFuss F.f c hc with ⟨L, hB, hL⟩ | hfrei
  · have hLt := rufG_haelt_signatur hO sp init hr t F (List.mem_cons_of_mem _ hF) L hL
    exact relyG hO sp init hex hr hs t (fun e => htu e.symm) c L hB hLt
  · exact schritt_traeger hO hs c (Or.inr (hfrei _))

end Maschine
end Gabbro.Grammatik
