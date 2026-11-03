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
public import Grammatik.Zielsatz.ZielOrt.Geraet.ZielOrtGeraetSem
@[expose] public section


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
  | .fremd q => [.fremd q]

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
  | fremd => rfl

theorem neutral_laenge (e0 : Ereignis D) (s : List (Ereignis D)) :
    s.length < (neutral e0 ++ s).length := by
  cases e0 <;> simp only [neutral, List.cons_append, List.nil_append, List.length_cons, Nat.lt_add_one] <;> omega

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
    rw [if_neg (by simp only [ht, Bool.false_eq_true, not_false_eq_true])]
  · show (if D.gschreibt g x = true then s1.globs x else κ.globs x) = κ.globs x
    rw [if_neg (by simp only [hx, Bool.false_eq_true, not_false_eq_true])]

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


end Gabbro.Grammatik
