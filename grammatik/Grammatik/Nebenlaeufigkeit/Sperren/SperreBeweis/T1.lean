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
module
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreFuss
@[expose] public section


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
  | assignThruOwn p t ht f i e m s ho' he hg hw hL =>
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
  | transition => simp only [stmtOrteP, List.not_mem_nil] at ho
  | publish g e payload hp hw hL => exact e.orte_darf o ho
  | advances => simp only [stmtOrteP, List.not_mem_nil] at ho
  | retires => simp only [stmtOrteP, List.not_mem_nil] at ho
  | ret e hp => exact e.orte_darf o ho
  | retWhy => simp only [stmtOrteP, List.not_mem_nil] at ho
  | retScoped e _ => exact e.orte_darf o ho
  | retWhyScoped => simp only [stmtOrteP, List.not_mem_nil] at ho
  | leave => simp only [stmtOrteP, List.not_mem_nil] at ho
  | next => simp only [stmtOrteP, List.not_mem_nil] at ho
  | _ => simp only [istBlatt, Bool.false_eq_true] at hb

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
    rw [if_neg (by simp only [ht, Bool.false_eq_true, not_false_eq_true])]
  · show (if D.gschreibt g x = true then s1.globs x else κ.globs x) = κ.globs x
    rw [if_neg (by simp only [hx, Bool.false_eq_true, not_false_eq_true])]

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
    rw [if_neg (by simp only [ht, Bool.false_eq_true, not_false_eq_true])]
  · show (if D.agschreibt a g = true then σ₂.globs g else κ.globs g) = κ.globs g
    rw [if_neg (by simp only [hg, Bool.false_eq_true, not_false_eq_true])]

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


end Gabbro.Grammatik
