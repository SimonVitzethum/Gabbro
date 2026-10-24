/-
  File:      Grammatik/SperreBeweis.lean
  Subject:   The replay of `ziel_ort_ganz` (`ZielOrtRahmenBeweis.lean`) with
             LOCK INVARIANTS: the sequential side runs `execStmtH`
             (`SperreSem.lean`), the records also keep the environment's move
             at every acquire, and the sequential world agrees with the
             machine world on the STABLE carriers of the frame at its current
             holdings (`stabilS`, `SperreFuss.lean`), not on the whole
             footprint.

  Changes against `KopfR`/`WarteR`/`StapelR`/`FadenR`:
  * a third record `HU` of acquires (`UEintrag`: lock, key world, the
    memory the protected carriers were taken from), functional, below the
    sequential trace, every source meeting the lock's invariant (`InvU`);
    the sequential runs quantify over the moves repeating it (`PasstU`);
  * agreement on `stabilS P S lok F.f Λ`, where `Λ` is the residue's static
    holdings: it grows at an acquire (the new record takes the protected
    carriers from the machine, `fadenS_locks`) and shrinks at a release;
  * the release steps (`fadenS_frei`, `fadenS_peelFrei`) use the second
    clause of the obligation: the head's prediction is no `logik` outcome
    (`kopfS_keineLogik`), so the release check passes at the sequential
    world, hence (the protected carriers are stable while the lock is held)
    at the machine world (`kopfS_frei_inv`).
-/
import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 0. The carriers a leaf reads carry their guards -/

theorem Stmt.blatt_darf (P : Programm D) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (hb : s.istBlatt = true) : ∀ o ∈ stmtOrteP P s, OrtDarf Λ o := by
  intro o ho
  cases s with
  | assignSlot t f i e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with ho | ho
      · exact i.orte_darf o ho
      · exact e.orte_darf o ho
  | assignThru p t ht f i e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with (ho | ho) | ho
      · exact p.orte_darf o ho
      · exact i.orte_darf o ho
      · exact e.orte_darf o ho
  | assignSlotRef r t ht ho' f e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with ho | ho
      · exact r.orte_darf o ho
      · exact e.orte_darf o ho
  | assignGlob g e hw hL => exact e.orte_darf o ho
  | putBytes t f hf n i hlo hhi e hw hL =>
      simp only [stmtOrteP, List.mem_append] at ho
      rcases ho with ho | ho
      · exact i.orte_darf o ho
      · exact e.orte_darf o ho
  | assignVar x e => exact e.orte_darf o ho
  | shift t f hτ i von nach hn he hw hL =>
      simp only [stmtOrteP, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact hL
      · exact i.orte_darf o ho
  | axiomCall a args h hw hg hd hgd => exact args.orte_darf o ho
  | regWrite r hk e => exact e.orte_darf o ho
  | transition => simp [stmtOrteP] at ho
  | publish g e payload hp hw hL => exact e.orte_darf o ho
  | advances => simp [stmtOrteP] at ho
  | retires => simp [stmtOrteP] at ho
  | ret e hp => exact e.orte_darf o ho
  | retWhy => simp [stmtOrteP] at ho
  | leave => simp [stmtOrteP] at ho
  | next => simp [stmtOrteP] at ho
  | _ => simp [Stmt.istBlatt] at hb

/-! ## 0b. Fresh keys, with or without an event

  The replay keeps every record functional (`FunkV`, `FunkA`, `FunkU`) by
  keying each new entry at a trace position no earlier entry has: the
  recorded answer world is one trace piece longer than the key world. That
  piece is an EVENT, and a declaration without a table, a global and a lock
  has none (`Ereignis D` is empty): there every world is one and the same
  point (`welt_eq`), and a key is only (callee, parameters).

  For such a declaration the records are kept functional by JUSTIFICATION
  instead of by freshness (`Begruendet`): a recorded call answer is what the
  callee's body ends in against every handler repeating the callee's own
  (justified, functional) record, with the machine's oracle. Two justified
  answers with one key are equal (`begruendet_eindeutig`): the union of
  their records is functional by induction, and one handler repeating it
  makes both bodies end in the same outcome -- the determinism of machine G
  that such a declaration needs, obtained from the replay itself rather than
  from its 70 rules. Axiom answers are the machine oracle's own answers
  there (`PasstA O`), and no acquire is ever recorded (there is no lock). -/

/-- The trace piece that makes a recorded key fresh: `neutral e` for a
    chosen event, nothing when the declaration has no event. -/
noncomputable def frischSpur (D : Deklaration) : List (Ereignis D) :=
  haveI := Classical.propDecidable (Nonempty (Ereignis D))
  if h : Nonempty (Ereignis D) then neutral (Classical.choice h) else []

theorem offen_frischSpur (s : List (Ereignis D)) : offen (frischSpur D ++ s) = offen s := by
  unfold frischSpur
  split
  · exact offen_neutral _ s
  · rfl

theorem frischSpur_laenge (h : Nonempty (Ereignis D)) (s : List (Ereignis D)) :
    s.length < (frischSpur D ++ s).length := by
  unfold frischSpur
  rw [dif_pos h]
  exact neutral_laenge _ s

/-- **Without an event every world is the same point**: no table, no
    global, and an always-empty trace. -/
theorem welt_eq (hE : ¬ Nonempty (Ereignis D)) (σ σ' : World D) : σ = σ' := by
  obtain ⟨s, g, sp⟩ := σ
  obtain ⟨s', g', sp'⟩ := σ'
  have h1 : s = s' := funext fun t => absurd ⟨.zugriff t false [] []⟩ hE
  have h2 : g = g' := funext fun x => absurd ⟨.gzugriff x false [] []⟩ hE
  have h3 : ∀ l : List (Ereignis D), l = [] := fun l => by
    cases l with
    | nil => rfl
    | cons e _ => exact absurd ⟨e⟩ hE
  rw [h1, h2, h3 sp, h3 sp']

/-- The recorded answer world of a call to `g` (as `rahmenWelt`), with the
    fresh trace piece `frischSpur`. -/
noncomputable def rahmenWeltF (g : D.Fn) (κ s1 : World D) : World D :=
  ⟨fun t => if D.schreibt g t = true then s1.slots t else κ.slots t,
   fun x => if D.gschreibt g x = true then s1.globs x else κ.globs x, frischSpur D ++ κ.spur⟩

theorem rahmenWeltF_rahmen (g : D.Fn) (κ s1 : World D) :
    Rahmen (D.schreibt g) (D.gschreibt g) κ (rahmenWeltF g κ s1) := by
  refine ⟨fun t ht k f => ?_, fun x hx => ?_⟩
  · show (if D.schreibt g t = true then s1.slots t else κ.slots t) k f = κ.slots t k f
    rw [if_neg (by simp [ht])]
  · show (if D.gschreibt g x = true then s1.globs x else κ.globs x) = κ.globs x
    rw [if_neg (by simp [hx])]

theorem rahmenWeltF_offen (g : D.Fn) (κ s1 : World D) :
    offen (rahmenWeltF g κ s1).spur = offen κ.spur :=
  offen_frischSpur κ.spur

theorem rahmenWeltF_laenge (g : D.Fn) (κ s1 : World D) :
    κ.spur.length ≤ (rahmenWeltF g κ s1).spur.length := by
  show κ.spur.length ≤ (frischSpur D ++ κ.spur).length
  rw [List.length_append]
  exact Nat.le_add_left _ _

theorem rahmenWeltF_gleichAuf {S : List (D.Tab ⊕ D.Glob)} (g : D.Fn)
    {κ A s1 : World D} (hκ : GleichAuf S κ A) (hA : GleichOhne g S A s1) :
    GleichAuf S (rahmenWeltF g κ s1) s1 := by
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

/-- The recorded answer world of an axiom call (as `axWelt`), with the fresh
    trace piece `frischSpur`. -/
noncomputable def axWeltF (a : D.Ax) (κ σ₂ : World D) : World D :=
  ⟨fun t => if D.aschreibt a t = true then σ₂.slots t else κ.slots t,
   fun g => if D.agschreibt a g = true then σ₂.globs g else κ.globs g, frischSpur D ++ κ.spur⟩

theorem axWeltF_rahmen (a : D.Ax) (κ σ₂ : World D) :
    Rahmen (D.aschreibt a) (D.agschreibt a) κ (axWeltF a κ σ₂) := by
  refine ⟨fun t ht k f => ?_, fun g hg => ?_⟩
  · show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) k f = κ.slots t k f
    rw [if_neg (by simp [ht])]
  · show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = κ.globs g
    rw [if_neg (by simp [hg])]

theorem axWeltF_laenge (a : D.Ax) (κ σ₂ : World D) :
    κ.spur.length ≤ (axWeltF a κ σ₂).spur.length := by
  show κ.spur.length ≤ (frischSpur D ++ κ.spur).length
  rw [List.length_append]
  exact Nat.le_add_left _ _

theorem axWeltF_gleichAuf {S : List (D.Tab ⊕ D.Glob)} (a : D.Ax)
    {κ σ₁ σ₂ : World D} (hg : GleichAuf S κ σ₁)
    (hr : Rahmen (D.aschreibt a) (D.agschreibt a) σ₁ σ₂) :
    GleichAuf S (axWeltF a κ σ₂) σ₂ := by
  refine ⟨fun t ht => ?_, fun g hg' => ?_⟩
  · show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
    split
    · rfl
    · rename_i hw
      rw [hg.1 t ht]
      funext k f
      exact (hr.1 t (by simpa using hw) k f).symm
  · show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
    split
    · rfl
    · rename_i hw
      rw [hg.2 g hg']
      exact (hr.2 g (by simpa using hw)).symm

theorem axWeltF_vertrag {Q : AxEns D} (hlok : AxEnsLokal Q) (a : D.Ax)
    (κ σ₂ : World D) (v : ErgVal D (D.aerg a)) (h : Q a σ₂ v = true) :
    Q a (axWeltF a κ σ₂) v = true := by
  rw [hlok a (axWeltF a κ σ₂) σ₂ v (fun t ht => by
      show (if D.aschreibt a t = true then σ₂.slots t else κ.slots t) = σ₂.slots t
      rw [if_pos ht])
    (fun g hg => by
      show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = σ₂.globs g
      rw [if_pos hg])]
  exact h

/-- What a call answer says about an end outcome of the callee's body: the
    same value, or the same reason, at some world. -/
def Antwortet {g : D.Fn} {l : Bool} {Γ : Ctx} (x : EndAusgang (vertragVon D g) l Γ) :
    RufAusgang g → Prop
  | .ok _ v => ∃ σ, x = .zurueck σ v
  | .why _ r => ∃ σ, x = .why σ r
  | _ => False

theorem antwortet_eindeutig (hE : ¬ Nonempty (Ereignis D)) {g : D.Fn} {l : Bool} {Γ : Ctx}
    {x : EndAusgang (vertragVon D g) l Γ} {a a' : RufAusgang g} (h1 : Antwortet x a)
    (h2 : Antwortet x a') : a = a' := by
  cases a with
  | ok σ v =>
    cases a' with
    | ok σ' v' =>
      obtain ⟨s1, rfl⟩ := h1
      obtain ⟨s2, h⟩ := h2
      cases h
      rw [welt_eq hE σ σ']
    | why σ' r' =>
      obtain ⟨s1, rfl⟩ := h1
      obtain ⟨s2, h⟩ := h2
      cases h
    | logik e => exact h2.elim
    | hardware e => exact h2.elim
  | why σ r =>
    cases a' with
    | ok σ' v' =>
      obtain ⟨s1, rfl⟩ := h1
      obtain ⟨s2, h⟩ := h2
      cases h
    | why σ' r' =>
      obtain ⟨s1, rfl⟩ := h1
      obtain ⟨s2, h⟩ := h2
      cases h
      rw [welt_eq hE σ σ']
    | logik e => exact h2.elim
    | hardware e => exact h2.elim
  | logik e => exact h1.elim
  | hardware e => exact h1.elim

/-- **A justified call answer.** The answer `a` to `g` at `κ` with the
    parameters `ρ` is what `g`'s body ends in against every handler that
    repeats a functional record `H` of justified answers, with the machine's
    oracle and any environment move. -/
inductive Begruendet (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D) :
    EintragV D → Prop
  | mk (g : D.Fn) (κ : World D) (ρ : Env D (D.params g)) (a : RufAusgang g)
      (H : List (EintragV D)) :
      FunkV H → (∀ e ∈ H, Begruendet P O passes S e) →
      (∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (U : Umwelt D),
        PasstV R H →
          Antwortet (execEndH (V := vertragVon D g) S O U passes R (P.rumpf g) κ ρ) a) →
      Begruendet P O passes S ⟨g, κ, ρ, a⟩

section Begruendet

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

/-- **Two justified answers with one key are equal** (no event): the
    determinism of the calls of machine G in such a declaration. -/
theorem begruendet_eindeutig (hE : ¬ Nonempty (Ereignis D)) {e : EintragV D}
    (h : Begruendet P O passes S e) :
    ∀ a', Begruendet P O passes S ⟨e.1, e.2.1, e.2.2.1, a'⟩ → e.2.2.2 = a' := by
  induction h with
  | mk g κ ρ a H hf _ hpred ih =>
    intro a' h2
    cases h2 with
    | mk _ _ _ _ H2 hf2 hB2 hpred2 =>
      have hfun : FunkV (H ++ H2) := by
        intro g' σ ρ' b b' m1 m2
        rcases List.mem_append.mp m1 with m1 | m1 <;> rcases List.mem_append.mp m2 with m2 | m2
        · exact hf _ _ _ _ _ m1 m2
        · exact ih _ m1 b' (hB2 _ m2)
        · exact (ih _ m2 b (hB2 _ m1)).symm
        · exact hf2 _ _ _ _ _ m1 m2
      have hp := rufAusV_passt hfun
      exact antwortet_eindeutig hE
        (hpred (rufAusV (H ++ H2)) (fun _ σ => σ)
          (fun g σ ρ a hm => hp g σ ρ a (List.mem_append_left _ hm)))
        (hpred2 (rufAusV (H ++ H2)) (fun _ σ => σ)
          (fun g σ ρ a hm => hp g σ ρ a (List.mem_append_right _ hm)))

end Begruendet
/-- Without an event there is no lock: every acquire record fits every move. -/
theorem passtU_leer (hE : ¬ Nonempty (Ereignis D)) (S : SperrInv D) (U : Umwelt D)
    (HU : List (UEintrag D)) : PasstU S U HU :=
  fun L _ _ _ => absurd ⟨.gibt L⟩ hE

theorem funkA_of_passtA {O : Orakel D} {HA : List (AxEintrag D)} (h : PasstA O HA) : FunkA HA :=
  fun a σ ρ x x' h1 h2 => (h a σ ρ x h1).symm.trans (h a σ ρ x' h2)

/-- The freshness side of a call record: every key below `N` when the
    declaration has an event; every answer justified when it has none. -/
def KurzVB (P : Programm D) (O : Orakel D) (passes : Nat) (S : SperrInv D) (N : Nat)
    (H : List (EintragV D)) : Prop :=
  (Nonempty (Ereignis D) → KurzV N H) ∧
    (¬ Nonempty (Ereignis D) → ∀ e ∈ H, Begruendet P O passes S e)

/-- The freshness side of an axiom record: every key below `N` with an
    event; the machine oracle's own answers without one. -/
def KurzAB (O : Orakel D) (N : Nat) (HA : List (AxEintrag D)) : Prop :=
  (Nonempty (Ereignis D) → KurzA N HA) ∧ (¬ Nonempty (Ereignis D) → PasstA O HA)

/-- The freshness side of an acquire record (without an event there is no
    lock and no acquire). -/
def KurzUB (N : Nat) (HU : List (UEintrag D)) : Prop :=
  Nonempty (Ereignis D) → KurzU N HU

section Kurz

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

theorem kurzVB_nil (N : Nat) : KurzVB P O passes S N ([] : List (EintragV D)) :=
  ⟨fun _ => kurzV_nil N, fun _ _ h => absurd h List.not_mem_nil⟩

theorem kurzAB_nil (N : Nat) : KurzAB O N ([] : List (AxEintrag D)) :=
  ⟨fun _ => kurzA_nil N, fun _ _ _ _ _ h => absurd h List.not_mem_nil⟩

theorem kurzUB_nil (N : Nat) : KurzUB N ([] : List (UEintrag D)) := fun _ => kurzU_nil N

theorem kurzVB_mono {N N' : Nat} {H : List (EintragV D)} (h : KurzVB P O passes S N H)
    (hN : N ≤ N') : KurzVB P O passes S N' H :=
  ⟨fun hE => kurzV_mono (h.1 hE) hN, h.2⟩

theorem kurzAB_mono {N N' : Nat} {HA : List (AxEintrag D)} (h : KurzAB O N HA) (hN : N ≤ N') :
    KurzAB O N' HA :=
  ⟨fun hE => kurzA_mono (h.1 hE) hN, h.2⟩

theorem kurzUB_mono {N N' : Nat} {HU : List (UEintrag D)} (h : KurzUB N HU) (hN : N ≤ N') :
    KurzUB N' HU :=
  fun hE => kurzU_mono (h hE) hN

/-- **A new call answer keeps the record functional**: fresh when the
    declaration has an event, justified when it has none. -/
theorem funkV_appendB {N : Nat} {H : List (EintragV D)} (hf : FunkV H)
    (hk : KurzVB P O passes S N H) (e : EintragV D)
    (he : Nonempty (Ereignis D) → N ≤ e.2.1.spur.length)
    (hb : ¬ Nonempty (Ereignis D) → Begruendet P O passes S e) : FunkV (H ++ [e]) := by
  by_cases hN : Nonempty (Ereignis D)
  · exact funkV_append hf (hk.1 hN) e (he hN)
  · intro g σ ρ a a' k1 k2
    rcases List.mem_append.mp k1 with h1 | h1 <;> rcases List.mem_append.mp k2 with h2 | h2
    · exact hf g σ ρ a a' h1 h2
    · rw [List.mem_singleton] at h2
      subst h2
      exact begruendet_eindeutig hN (e := ⟨g, σ, ρ, a⟩) (hk.2 hN _ h1) a' (hb hN)
    · rw [List.mem_singleton] at h1
      subst h1
      exact (begruendet_eindeutig hN (e := ⟨g, σ, ρ, a'⟩) (hk.2 hN _ h2) a (hb hN)).symm
    · rw [List.mem_singleton] at h1 h2
      rw [← h1] at h2
      have e2 := eq_of_heq (Sigma.mk.inj h2).2
      simp only [Prod.mk.injEq] at e2
      exact e2.2.2.symm

end Kurz
/-! ## 1. The replay invariants -/

section Inv

variable (P : Programm D) (O : Orakel D) (passes : Nat) (Q : AxEns D) (S : SperrInv D)
  (lok : D.Tab ⊕ D.Glob → Bool)

/-- How a suspended frame continues once its pending call is answered (as
    `FortV`), over the semantics with lock invariants. -/
def FortS (F : RufRahmenG D) (g : D.Fn) (X : ZErgG (vertragVon D F.f))
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D) (U : Umwelt D) :
    RufAusgang g → Prop
  | .ok σa v =>
      (F.wartend = false → X.folgt (semH S O' U passes R F.rest.2.2.2.2 σa F.rest.2.2.2.1)) ∧
      (∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty)
          (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
          (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        (F.rest = ⟨l, Γ, Λ, ρc, .wartet restb k⟩ ∨
          ∃ (n : Nat) (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ),
            F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩) →
        ∀ he : D.erg g = some τ,
          X.folgt (semH S O' U passes R (.dann restb (.schrumpf k)) σa (.cons (ergWert he v) ρc)))
  | .why σa r =>
      ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (τ : Ty) (n : Nat)
        (err : Endblock D (vertragVon D F.f) l (.why n :: Γ) Λ)
        (restb : Block D (vertragVon D F.f) l (τ :: Γ) Λ Λ')
        (k : GRest D (vertragVon D F.f) l Γ Λ') (ρc : Env D Γ),
        F.rest = ⟨l, Γ, Λ, ρc, .wartetSonst n err restb k⟩ →
        ∀ hn : D.gruende g = n,
          X.folgt (semH S O' U passes R (.dann err.alsBlock.2 (.abbruch (.schrumpf k))) σa
            (.cons (Fin.cast hn r) ρc))
  | _ => True

/-- **The replay of a head frame** `F` whose thread world is `W`, with lock
    invariants. -/
def KopfS (F : RufRahmenG D) (W : World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (σ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧
    KurzVB P O passes S σ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzAB O σ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzUB σ.spur.length HU ∧
    GleichAuf (stabilS P S lok F.f F.rest.2.2.1) σ W ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      (zErgG (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)).folgt
        (semH S O' U passes R F.rest.2.2.2.2 σ F.rest.2.2.2.1)

/-- **The replay of a suspended frame** `F` waiting for the callee with key
    `G`. The key world agrees with the callee's machine entry world on the
    frame's stable carriers at its holdings, which contain the callee's
    contract carriers. -/
def WarteS (F : RufRahmenG D) (G : Σ f : D.Fn, Env D (D.params f) × World D) : Prop :=
  ∃ (H : List (EintragV D)) (HA : List (AxEintrag D)) (HU : List (UEintrag D)) (κ : World D),
    ReqAmEintritt P F.f F.s0 F.rho ∧ FunkV H ∧ VertraegeOkR P H ∧
    KurzVB P O passes S κ.spur.length H ∧
    FunkA HA ∧ RahmenA HA ∧ VertragA O.zeiger Q HA ∧ KurzAB O κ.spur.length HA ∧
    FunkU HU ∧ InvU S HU ∧ KurzUB κ.spur.length HU ∧
    F.rest.2.2.2.2.okS P (fussOrteG P F.f) (sicher P lok F.f) ∧
    ReqAmEintritt P G.1 κ G.2.1 ∧
    (GleichAuf ((P.requires G.1).orte ++ (P.ensures G.1).orte) κ G.2.2 ∧
      (P.requires G.1).orte ++ (P.ensures G.1).orte ⊆ stabilS P S lok F.f F.rest.2.2.1 ∧
      GleichAuf (stabilS P S lok F.f F.rest.2.2.1) κ G.2.2) ∧
    ∀ (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) (O' : Orakel D)
      (U : Umwelt D),
      PasstV R H → PasstA O' HA → PasstU S U HU → GleichRS O O' →
      FortS passes S F G.1
        (zErgG (execEndH (V := vertragVon D F.f) S O' U passes R (P.rumpf F.f) F.s0 F.rho)) R O' U
        (R G.1 κ G.2.1)

def StapelS : (Σ f : D.Fn, Env D (D.params f) × World D) → List (RufRahmenG D) → Prop
  | _, [] => True
  | G, F :: rest => WarteS P O passes Q S lok F G ∧ StapelS (RufSchluesselG F) rest

def FadenS (z : RufFadenG D) (W : World D) : Prop :=
  KopfS P O passes Q S lok z.kopf W ∧ StapelS P O passes Q S lok (RufSchluesselG z.kopf) z.stapel

def ZielInvS (M : RufMaschineG D) : Prop :=
  (∀ t, FadenS P O passes Q S lok (M.faeden t) (M.weltVon t)) ∧ ∀ t, LogOk P (M.faeden t).log

end Inv
/-- `FortS` is monotone in the predicted result. -/
theorem fortS_mono {passes : Nat} {S : SperrInv D} {F : RufRahmenG D} {g : D.Fn}
    {X Y : ZErgG (vertragVon D F.f)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} {O' : Orakel D} {U : Umwelt D}
    (hXY : X.folgt Y) :
    ∀ {a : RufAusgang g}, FortS passes S F g Y R O' U a → FortS passes S F g X R O' U a
  | .ok _ _, h => ⟨fun hw => ZErgG.folgt_trans hXY (h.1 hw),
      fun l Γ Λ Λ' τ restb k ρc hc he => ZErgG.folgt_trans hXY (h.2 l Γ Λ Λ' τ restb k ρc hc he)⟩
  | .why _ _, h => fun l Γ Λ Λ' τ n err restb k ρc hc hn =>
      ZErgG.folgt_trans hXY (h l Γ Λ Λ' τ n err restb k ρc hc hn)
  | .logik _, _ => trivial
  | .hardware _, _ => trivial

/-! ## 2. The steps of the replay -/


end Gabbro.Grammatik
