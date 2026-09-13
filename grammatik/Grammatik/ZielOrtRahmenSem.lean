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
import Grammatik.ZielOrtGeraetSem

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The handler class and the user obligation -/

/-- **A handler that respects the contracts AND the declared frames.** It
    respects the contracts at their place (`RespektiertVertraege`), and every
    normal answer to `f` from the world `σ` returns a world `σ'` that differs
    from `σ` only on the carriers `f`'s signature declares as written, with
    the same held locks. -/
def RespektiertRahmen (P : Programm D)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  RespektiertVertraege P R ∧
  ∀ (f : D.Fn) (σ : World D) (ρ : Env D (D.params f)) (σ' : World D) (v : ErgVal D (D.erg f)),
    R f σ ρ = RufAusgang.ok σ' v →
      Rahmen (D.schreibt f) (D.gschreibt f) σ σ' ∧ offen σ'.spur = offen σ.spur

/-- **The user obligation of one function, against frame-respecting
    handlers.** The body triple and the caller duty of `KoerperGutG`
    (every oracle that respects the declared axiom frames and is
    register-local), for every call handler that respects the contracts AND
    the callees' declared frames (`RespektiertRahmen`): a caller may use that
    a callee changes only what it declares to write. -/
def KoerperGutR (P : Programm D) (passes : Nat) (f : D.Fn) : Prop :=
  ∀ O' : Orakel D, RahmenO O' → RegLokal O' →
  ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f),
    RespektiertRahmen P R → OhneVorbedingung R →
    ∀ (σ : World D) (ρ : Env D (D.params f)), ReqAmEintritt P f σ ρ →
      (∀ (σ' : World D) (v : ErgVal D (D.erg f)),
        execEnd (V := vertragVon D f) O' passes R (P.rumpf f) σ ρ = EndAusgang.zurueck σ' v →
          EnsAmRueck P f σ σ' ρ v) ∧
      (∀ g : D.Fn,
        execEnd (V := vertragVon D f) O' passes (torRuf P R) (P.rumpf f) σ ρ ≠
          EndAusgang.logik (Logik.vorbedingung g))

/-- **The new obligation is weaker than `KoerperGutG`**: fewer handlers. -/
theorem koerperGutR_of_G {P : Programm D} {passes : Nat} {f : D.Fn}
    (h : KoerperGutG P passes f) : KoerperGutR P passes f :=
  fun O' hr hl R hR hOV σ ρ hreq => h O' hr hl R hR.1 hOV σ ρ hreq

/-- **The new obligation is weaker than `KoerperGutV`** (the obligation of
    `ziel_ort_voll`, and through `koerperGutV_of_kOk` of `ziel_ort`): every
    earlier witness carries over. -/
theorem koerperGutR_of_V {P : Programm D} {passes : Nat} {f : D.Fn}
    (h : KoerperGutV P passes f) : KoerperGutR P passes f :=
  koerperGutR_of_G (koerperGutG_of_V h)

/-! ## 2. Records whose normal answers lie in the callee's frame -/

/-- Every recorded normal answer lies in the callee's declared frame around
    its key world and keeps the held locks. -/
def RahmenV (H : List (EintragV D)) : Prop :=
  ∀ (g : D.Fn) (σ : World D) (ρ : Env D (D.params g)) (a : RufAusgang g),
    (⟨g, σ, ρ, a⟩ : EintragV D) ∈ H → ∀ (σ' : World D) (v : ErgVal D (D.erg g)),
      a = .ok σ' v → Rahmen (D.schreibt g) (D.gschreibt g) σ σ' ∧ offen σ'.spur = offen σ.spur

/-- The record facts of the replay: contracts (`VertraegeOkV`) and frames. -/
def VertraegeOkR (P : Programm D) (H : List (EintragV D)) : Prop :=
  VertraegeOkV P H ∧ RahmenV H

theorem vertraegeOkR_nil (P : Programm D) : VertraegeOkR P ([] : List (EintragV D)) :=
  ⟨vertraegeOkV_nil P, fun _ _ _ _ h => absurd h List.not_mem_nil⟩

/-- The handler of a record respects contracts and frames. -/
theorem rufAusV_rahmen {P : Programm D} {H : List (EintragV D)} (hv : VertraegeOkR P H) :
    RespektiertRahmen P (rufAusV H) :=
  ⟨rufAusV_respektiert hv.1, fun g σ ρ σ' v h =>
    hv.2 g σ ρ _ (rufAusV_mem h (fun e he => by cases he)) σ' v rfl⟩

/-! ## 3. The recorded answer world of a call -/

/-- A trace piece that keeps the held locks: the event `e0` itself unless it
    takes or releases a lock; a take-release pair of its lock otherwise. -/
def neutral : Ereignis D → List (Ereignis D)
  | .nimmt L h => [.gibt L, .nimmt L h]
  | .gibt L => [.gibt L, .nimmt L []]
  | .zugriff t b Λ h => [.zugriff t b Λ h]
  | .gzugriff g b Λ h => [.gzugriff g b Λ h]

theorem offen_neutral (e0 : Ereignis D) (s : List (Ereignis D)) :
    offen (neutral e0 ++ s) = offen s := by
  cases e0 with
  | nimmt L h =>
      show (L :: offen s).erase L = offen s
      exact List.erase_cons_head L (offen s)
  | gibt L =>
      show (L :: offen s).erase L = offen s
      exact List.erase_cons_head L (offen s)
  | zugriff => rfl
  | gzugriff => rfl

theorem neutral_laenge (e0 : Ereignis D) (s : List (Ereignis D)) :
    s.length < (neutral e0 ++ s).length := by
  cases e0 <;> simp [neutral] <;> omega

/-- **The recorded answer world of a call to `g`**: the callee's declared
    write carriers from the machine's return world `s1`, every other carrier
    from the sequential key world `κ`, a fresh trace position past `κ` that
    keeps the held locks. -/
def rahmenWelt (e0 : Ereignis D) (g : D.Fn) (κ s1 : World D) : World D :=
  ⟨fun t => if D.schreibt g t = true then s1.slots t else κ.slots t,
   fun x => if D.gschreibt g x = true then s1.globs x else κ.globs x, neutral e0 ++ κ.spur⟩

theorem rahmenWelt_rahmen (e0 : Ereignis D) (g : D.Fn) (κ s1 : World D) :
    Rahmen (D.schreibt g) (D.gschreibt g) κ (rahmenWelt e0 g κ s1) := by
  refine ⟨fun t ht k f => ?_, fun x hx => ?_⟩
  · show (if D.schreibt g t = true then s1.slots t else κ.slots t) k f = κ.slots t k f
    rw [if_neg (by simp [ht])]
  · show (if D.gschreibt g x = true then s1.globs x else κ.globs x) = κ.globs x
    rw [if_neg (by simp [hx])]

theorem rahmenWelt_offen (e0 : Ereignis D) (g : D.Fn) (κ s1 : World D) :
    offen (rahmenWelt e0 g κ s1).spur = offen κ.spur :=
  offen_neutral e0 κ.spur

theorem rahmenWelt_laenge (e0 : Ereignis D) (g : D.Fn) (κ s1 : World D) :
    κ.spur.length < (rahmenWelt e0 g κ s1).spur.length :=
  neutral_laenge e0 κ.spur

/-- Two worlds agree on the carriers of `S` that `g` does not declare as
    written. -/
def GleichOhne (g : D.Fn) (S : List (D.Tab ⊕ D.Glob)) (σ σ' : World D) : Prop :=
  (∀ t, Sum.inl t ∈ S → D.schreibt g t = false → σ.slots t = σ'.slots t) ∧
  (∀ x, Sum.inr x ∈ S → D.gschreibt g x = false → σ.globs x = σ'.globs x)

/-- The recorded answer world agrees with the machine's return world on
    every carrier of `S` on which the key world agreed with the machine's
    call world `A`, when the machine kept `S` outside the callee's writes. -/
theorem rahmenWelt_gleichAuf {S : List (D.Tab ⊕ D.Glob)} (e0 : Ereignis D) (g : D.Fn)
    {κ A s1 : World D} (hκ : GleichAuf S κ A) (hA : GleichOhne g S A s1) :
    GleichAuf S (rahmenWelt e0 g κ s1) s1 := by
  refine ⟨fun t ht => ?_, fun x hx => ?_⟩
  · show (if D.schreibt g t = true then s1.slots t else κ.slots t) = s1.slots t
    split
    · rfl
    · rename_i hw
      exact (hκ.1 t ht).trans (hA.1 t ht (by simpa using hw))
  · show (if D.gschreibt g x = true then s1.globs x else κ.globs x) = s1.globs x
    split
    · rfl
    · rename_i hw
      exact (hκ.2 x hx).trans (hA.2 x hx (by simpa using hw))

/-! ## 4. The machine delivers the frame: `RahmenStapel` -/

/-- A callee's declared writes are inside its caller's (`RufPasst.hw`/`hg`). -/
theorem traegerSchreibt_passt {f g : D.Fn} {Λ : List (Res D)}
    (hp : RufPasst D (vertragVon D f) (D.signatur g) Λ) :
    ∀ c, TraegerSchreibt g c = true → TraegerSchreibt f c = true
  | .inl t, h => hp.hw t h
  | .inr x, h => hp.hg x h

theorem traegerGleich_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob}
    (h1 : TraegerGleich s s' c) (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c with
  | inl t => exact Eq.trans h1 h2
  | inr x => exact Eq.trans h1 h2

section Stapel

variable (P : Programm D)

/-- **The frame invariant of a stack.** For every suspended frame `F`
    waiting for the callee with key `G` (function, parameters, entry world):
    the callee's declared writes are inside `F`'s, and the memory `S` agrees
    with the callee's entry memory on every footprint carrier of `F` that
    the callee does not declare as written. -/
def RahmenStapel (S : Speicher D) :
    (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest =>
      (∀ c, TraegerSchreibt G.1 c = true → TraegerSchreibt F.f c = true) ∧
      (∀ c ∈ fussOrteG P F.f, TraegerSchreibt G.1 c = false → TraegerGleich S G.2.2.speicher c) ∧
      RahmenStapel S (RufSchluesselG F) rest

/-- The frame invariant of a machine: every thread's stack, keyed from its
    head. -/
def RahmenInv (M : RufMaschineG D) : Prop :=
  ∀ t, RahmenStapel P M.speicher (RufSchluesselG (M.faeden t).kopf) (M.faeden t).stapel

end Stapel

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
  | ruf l Γ Λ g args hp hr rest ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0
    simp only [rufUpdateG_self]
    exact rahmenStapel_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
  | rufDann l Γ Λ Λ' Λ'' g args hp hr rest k ρ hhead hΛ s0 hs0 rho hrho neu hneu =>
    subst hs0
    simp only [rufUpdateG_self]
    exact rahmenStapel_push h hmem _ (traegerSchreibt_passt hp) (fun c => by cases c <;> rfl) _
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
    subst hs0 hg
    simp only [rufUpdateG_self]
    exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
      _
  | rufCallInd l Γ Λ n p args hp hr rest ρ hhead hΛ s0 hs0 g hg hv rho hrho neu hneu =>
    subst hs0 hg
    simp only [rufUpdateG_self]
    exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
      _
  | dannBindCallInd l Γ Λ Λ' Λ'' τ n p args he hp hr rest k ρ hhead hΛ s0 hs0 g hg hv rho hrho
      neu hneu =>
    subst hs0 hg
    simp only [rufUpdateG_self]
    exact rahmenStapel_push h hmem _ (traegerSchreibt_passt (g := g) hp) (fun c => by cases c <;> rfl)
      _
  -- pops
  | rueck caller rst hpop Γ Λ e hperm ρ hhead g hfg rho hrho s0 hs0 hΛ s1 hs1 v hv neu hneu hnw =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapel_pop h hmem
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
  | rueckBind caller rst hpop l Γ Λ Λ' τ restb k ρc hcaller Γc Λc e hperm ρ hhead g hfg rho hrho
      s0 hs0 hΛ s1 hs1 v hv he neu hneu =>
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
  | rueckConsGrund r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapel_pop h hmem
  | dannRetGrund r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
    simp only [rufUpdateG_self]
    rw [hpop] at h
    exact rahmenStapel_pop h hmem
  -- every other rule keeps the stack and the head's key
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

/-- **CALLEES RESPECT THEIR FRAMES ON G (`rufG_rahmen`).** On every machine
    reachable from the start, for every thread and every suspended frame
    `F` on its stack waiting for a callee `g` entered at world `s0`: `g`'s
    declared writes are inside `F`'s, and the live memory agrees with `s0`
    on every footprint carrier of `F` that `g` does not declare as written
    -- whatever `g`, its callees and all other threads did since. Premises:
    `GutO` (the oracle frame, the held locks), the footprint check
    `fussOrtGB` over a complete member list, and the exclusive start. -/
theorem rufG_rahmen (hO : GutO O) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hFuss : fussOrtGB P fs = true) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hex : StartExklusiv init)
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    RahmenInv P M := by
  induction hr with
  | start =>
      intro t
      show RahmenStapel P sp _ ((RufStartG P sp init).faeden t).stapel
      have e : ((RufStartG P sp init).faeden t).stapel = [] := by
        show (match init t with
          | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
              Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
              [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).stapel = []
        cases init t
        rfl
      rw [e]
      trivial
  | schritt M M' u hr' hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        exact rahmenStapel_akteur hO hs (ih t)
      · exact rahmenStapel_andere hO hvoll hFuss sp init hex hr' hs t htu (ih t)

end Maschine

/-! ## CUTS:

  What is proved: the handler class `RespektiertRahmen` (contracts plus the
  callee's declared frame and held locks on every normal answer), the
  obligation `KoerperGutR` over it, its weakening from `KoerperGutG` and
  `KoerperGutV` (`koerperGutR_of_G`, `koerperGutR_of_V`), the record forms
  (`RahmenV`, `VertraegeOkR`, `rufAusV_rahmen`), the recorded answer world
  `rahmenWelt` (in the callee's frame by construction, held locks kept by
  the `neutral` trace piece, agreeing with the machine on the caller's
  footprint when the machine kept it outside the callee's writes), and the
  machine fact `rufG_rahmen`: every suspended frame's footprint carriers
  change during its pending call only where the callee declares a write.

  What is NOT here: the goal theorem over `KoerperGutR`
  (`ZielOrtRahmen.lean`). The frame is a condition on NORMAL answers only;
  a reason answer (`grund`) keeps no frame in the handler class (the
  machine fact `rufG_rahmen` holds for it too, the replay records it with
  the same answer world). The frame is stated for the caller's footprint
  on the machine: carriers outside every suspended frame's footprint may be
  written by other threads during a call, and the sequential answer world
  takes them from the key world -- the caller's reasoning never reads them.
-/

#print axioms Gabbro.Grammatik.koerperGutR_of_G
#print axioms Gabbro.Grammatik.koerperGutR_of_V
#print axioms Gabbro.Grammatik.rufAusV_rahmen
#print axioms Gabbro.Grammatik.rahmenWelt_gleichAuf
#print axioms Gabbro.Grammatik.rahmenStapel_akteur
#print axioms Gabbro.Grammatik.rufG_rahmen

end Gabbro.Grammatik
