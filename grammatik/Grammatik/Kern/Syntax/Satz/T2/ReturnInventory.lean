/- Counted ownership of one tracked lock during canonical execution. -/
module
public import Grammatik.Kern.Syntax.Satz.T2
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

namespace ReturnInventory
variable {slack : Nat := 0}

/-- Only the callee's actual held-list preservation is needed by inventory. -/
def CallHeld (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ f σ ρ, HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt →
    ∀ σ', (R f σ ρ).welt = some σ' → σ'.haelt = σ.haelt

/-- Oracle effects preserve holdings independently of trace or footprint facts. -/
def OracleHeld (O : Orakel D) : Prop :=
  ∀ a σ ρ, (O.wirkt a σ ρ).1.haelt = σ.haelt

theorem oracleHeld_of_gutO {O : Orakel D} (hO : GutO O) : OracleHeld O :=
  fun a σ ρ => (hO a σ ρ).2.1

theorem storeSlot_held (σ : World D) (t : D.Tab) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) : (σ.schreibSlot t Λ k f v).haelt = σ.haelt := rfl

theorem storeGlob_held (σ : World D) (g : D.Glob) (Λ : List (Res D)) (v : Wert D (D.gtyp g)) :
    (σ.schreibGlob g Λ v).haelt = σ.haelt := rfl

theorem storeBytes_held (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) (bs : List Byte) : ∀ (σ : World D) (k : Int),
      (σ.schreibBytes t f hf Λ k bs).haelt = σ.haelt := by
  induction bs with
  | nil => intro σ k; rfl
  | cons b bs ih =>
    intro σ k
    rw [World.schreibBytes.eq_def, ih, storeSlot_held]

theorem oracle_held (O : Orakel D) (hO : OracleHeld O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) : (axiomAntwort O a σ ρ).1.haelt = σ.haelt :=
  (hO a (σ.fragt (.inl a)) ρ).trans (fragt_haelt σ (.inl a))

theorem oracleElse_held (O : Orakel D) (hO : OracleHeld O) (a : D.Ax) (σ : World D)
    (ρ : Env D (D.aparams a)) : (axiomAntwortSonst O a σ ρ).1.haelt = σ.haelt := by
  rw [axiomAntwortSonst_fst]
  exact oracle_held O hO a σ ρ

/-- The tracked lock has at most `slack` unrepresented caller occurrences.
    Other caller locks retain the ordinary floor-based holding contract. -/
def Entry (L : D.Lock) (bo : Option Int) (Λ : List (Res D)) (σ : World D)
    {slack : Nat := 0} : Prop :=
  HeldB bo Λ σ.haelt ∧ σ.haelt.count L ≤ Λ.count (Res.held L) + slack

theorem Entry.same {L : D.Lock} {bo : Option Int} {Λ : List (Res D)}
    {σ σ' : World D} (h : Entry (slack := slack) L bo Λ σ) (same : σ'.haelt = σ.haelt) :
    Entry (slack := slack) L bo Λ σ' := by
  constructor
  · rw [same]; exact h.1
  · rw [same]; exact h.2

theorem Entry.resources {L : D.Lock} {bo : Option Int} {Λ Λ' : List (Res D)}
    {σ : World D} (h : Entry (slack := slack) L bo Λ σ)
    (held : ∀ M, Res.held M ∈ Λ' ↔ Res.held M ∈ Λ)
    (count : Λ'.count (Res.held L) = Λ.count (Res.held L)) : Entry (slack := slack) L bo Λ' σ := by
  refine ⟨⟨fun M hM => h.1.1 M ((held M).mp hM),
    fun M hM hn => h.1.2 M hM (fun hm => hn ((held M).mpr hm))⟩, ?_⟩
  rw [count]
  exact h.2

theorem Entry.nimmt {L K : D.Lock} {bo : Option Int} {Λ : List (Res D)}
    {σ : World D} (h : Entry (slack := slack) L bo Λ σ) : Entry (slack := slack) L bo (.held K :: Λ) (σ.nimmt K) := by
  refine ⟨heldB_locks K h.1, ?_⟩
  change (K :: σ.haelt).count L ≤ (Res.held K :: Λ).count (Res.held L) + slack
  by_cases same : K = L
  · subst K
    simp only [List.count_cons_self]
    have bound := h.2
    omega
  · have different : Res.held K ≠ Res.held L := by intro e; cases e; exact same rfl
    simpa only [List.count_cons_of_ne same, List.count_cons_of_ne different] using h.2

theorem Entry.nach {L : D.Lock} {bo : Option Int} {Λ : List (Res D)} {σ : World D}
    (h : Entry (slack := slack) L bo Λ σ) (S : Signatur D.Tab D.Glob D.Lock D.Marke) :
    Entry (slack := slack) L bo (nachSig D S Λ) σ :=
  h.resources (fun M => held_nachSig_iff _ _ M) (count_held_nachSig S Λ L)

/-- A callee's own scoped releases cannot remove its inherited holdings. -/
theorem call_haelt {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : GutR R) (f : D.Fn) (σ : World D) (ρ : Env D (D.params f))
    (hh : HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt)
    {σ' : World D} (world : (R f σ ρ).welt = some σ') : σ'.haelt = σ.haelt := by
  have good := hR f σ ρ hh σ' world
  cases he : R f σ ρ with
  | ok _ _ => rw [he] at good; exact good.haelt
  | why _ _ => rw [he] at good; exact (good.toGut_entry hh).haelt
  | logik _ => simp only [he, RufAusgang.welt, reduceCtorEq] at world
  | hardware _ => simp only [he, RufAusgang.welt, reduceCtorEq] at world

theorem callHeld_of_gutR {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : GutR R) : CallHeld R :=
  fun f σ ρ held _ world => call_haelt hR f σ ρ held world

/-- Ordinary flow preserves the complete held list. A terminal return leaves
    at most the caller's `slack` occurrences of the tracked non-residual lock. -/
def Outcome (L : D.Lock) (σ : World D) (o : Ausgang V l Γ) {slack : Nat := 0} : Prop :=
  ∀ σ', o.welt = some σ' → match o with
    | .zurueck _ _ | .why _ _ => σ'.haelt.count L ≤ slack
    | _ => σ'.haelt = σ.haelt

abbrev EndOutcome (L : D.Lock) (σ : World D) (o : EndAusgang V l Γ) {slack : Nat := 0} : Prop :=
  Outcome (slack := slack) L σ o.zuAusgang

theorem Outcome.ok {L : D.Lock} {σ σ' : World D} (ρ : Env D Γ)
    (same : σ'.haelt = σ.haelt) : Outcome (slack := slack) (V := V) (l := l) L σ (.ok σ' ρ) := by
  intro σ1 hs
  cases hs
  exact same

theorem Outcome.logik {L : D.Lock} {σ : World D} (e : Logik D) :
    Outcome (slack := slack) (V := V) (l := l) (Γ := Γ) L σ (.logik e) := by
  intro σ' hs
  cases hs

theorem Outcome.hardware {L : D.Lock} {σ : World D} (e : Hardware D) :
    Outcome (slack := slack) (V := V) (l := l) (Γ := Γ) L σ (.hardware e) := by
  intro σ' hs
  cases hs

theorem Outcome.vor {L : D.Lock} {σ σ1 : World D} {o : Ausgang V l Γ}
    (same : σ1.haelt = σ.haelt) (h : Outcome (slack := slack) L σ1 o) : Outcome (slack := slack) L σ o := by
  intro σ' hs
  cases o <;> first | exact h σ' hs | exact (h σ' hs).trans same

theorem EndOutcome.vor {L : D.Lock} {σ σ1 : World D} {o : EndAusgang V l Γ}
    (same : σ1.haelt = σ.haelt) (h : EndOutcome (slack := slack) L σ1 o) : EndOutcome (slack := slack) L σ o := by
  exact Outcome.vor same h

theorem Outcome.schrumpf {L : D.Lock} {σ : World D} {o : Ausgang V l (τ :: Γ)}
    (h : Outcome (slack := slack) L σ o) : Outcome (slack := slack) L σ o.schrumpf := by
  intro σ' hs
  cases o <;> simp only [Ausgang.welt, Ausgang.schrumpf, Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem Outcome.schrumpfArm {L : D.Lock} {σ : World D} (c : Option Ty)
    {o : Ausgang V l (ArmCtx Γ c)} (h : Outcome (slack := slack) L σ o) : Outcome (slack := slack) L σ (o.schrumpfArm c) := by
  cases c with
  | none => exact h
  | some _ => exact h.schrumpf

theorem EndOutcome.schrumpf {L : D.Lock} {σ : World D} {o : EndAusgang V l (τ :: Γ)}
    (h : EndOutcome (slack := slack) L σ o) : EndOutcome (slack := slack) L σ o.schrumpf := by
  intro σ' hs
  cases o <;> simp only [Ausgang.welt, EndAusgang.zuAusgang, EndAusgang.schrumpf,
    Option.some.injEq, reduceCtorEq] at hs ⊢ <;>
    (subst hs; exact h _ rfl)

theorem EndOutcome.zuAusgang {L : D.Lock} {σ : World D} {o : EndAusgang V l Γ}
    (h : EndOutcome (slack := slack) L σ o) : Outcome (slack := slack) L σ o.zuAusgang := h

theorem Outcome.weiterOpt {L : D.Lock} {σ : World D} (e : Option Ty)
    {o : Ausgang V l (ErgCtx Γ e)} (h : Outcome (slack := slack) L σ o) :
    Outcome (slack := slack) L σ (Ausgang.weiterOpt e o) := by
  cases e with
  | none => exact h
  | some _ => exact h.schrumpf

theorem EndOutcome.weiterOpt {L : D.Lock} {σ : World D} (e : Option Ty)
    {o : EndAusgang V l (ErgCtx Γ e)} (h : EndOutcome (slack := slack) L σ o) :
    EndOutcome (slack := slack) L σ (EndAusgang.weiterOpt e o) := by
  cases e with
  | none => exact h
  | some _ => exact h.schrumpf

theorem Outcome.call {L : D.Lock} {bo : Option Int} {Λ : List (Res D)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : CallHeld R) (hbV : BodenUnter bo V.boden) (f : D.Fn)
    (hp : RufPasst D V (D.signatur f) Λ) {σ : World D} (entry : Entry (slack := slack) L bo Λ σ)
    (args : Env D (D.params f))
    (ok : World D → ErgVal D (D.erg f) → Ausgang V l Γ)
    (why : World D → Fin (D.gruende f) → Ausgang V l Γ)
    (hok : ∀ σ' v, Entry (slack := slack) L bo Λ σ' → Outcome (slack := slack) L σ' (ok σ' v))
    (hwhy : ∀ σ' r, Entry (slack := slack) L bo Λ σ' → Outcome (slack := slack) L σ' (why σ' r)) :
    Outcome (slack := slack) L σ (match R f σ args with
      | .ok σ' v => ok σ' v | .why σ' r => why σ' r
      | .logik e => .logik e | .hardware e => .hardware e) := by
  have held := heldB_ruf hp hbV entry.1
  cases he : R f σ args with
  | ok σ' v =>
    have same := hR f σ args held σ' (show (R f σ args).welt = some σ' by rw [he]; rfl)
    exact (hok σ' v (entry.same same)).vor same
  | why σ' r =>
    have same := hR f σ args held σ' (show (R f σ args).welt = some σ' by rw [he]; rfl)
    exact (hwhy σ' r (entry.same same)).vor same
  | logik e => exact Outcome.logik _
  | hardware e => exact Outcome.hardware _

theorem Outcome.option {L : D.Lock} {bo : Option Int} {Λ : List (Res D)} {α : Type}
    {σ : World D} (entry : Entry (slack := slack) L bo Λ σ) (answer : World D × Option α)
    (same : answer.1.haelt = σ.haelt) (failure : Hardware D)
    (next : World D → α → Ausgang V l Γ)
    (hn : ∀ σ' v, Entry (slack := slack) L bo Λ σ' → Outcome (slack := slack) L σ' (next σ' v)) :
    Outcome (slack := slack) L σ (match answer with
      | (σ', some v) => next σ' v | (_, none) => .hardware failure) := by
  rcases answer with ⟨σ', _ | v⟩
  · exact Outcome.hardware _
  · exact (hn σ' v (entry.same same)).vor same

theorem EndOutcome.call {L : D.Lock} {bo : Option Int} {Λ : List (Res D)}
    {R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}
    (hR : CallHeld R) (hbV : BodenUnter bo V.boden) (f : D.Fn)
    (hp : RufPasst D V (D.signatur f) Λ) {σ : World D} (entry : Entry (slack := slack) L bo Λ σ)
    (args : Env D (D.params f))
    (ok : World D → ErgVal D (D.erg f) → EndAusgang V l Γ)
    (why : World D → Fin (D.gruende f) → EndAusgang V l Γ)
    (hok : ∀ σ' v, Entry (slack := slack) L bo Λ σ' → EndOutcome (slack := slack) L σ' (ok σ' v))
    (hwhy : ∀ σ' r, Entry (slack := slack) L bo Λ σ' → EndOutcome (slack := slack) L σ' (why σ' r)) :
    EndOutcome (slack := slack) L σ (match R f σ args with
      | .ok σ' v => ok σ' v | .why σ' r => why σ' r
      | .logik e => .logik e | .hardware e => .hardware e) := by
  have held := heldB_ruf hp hbV entry.1
  cases he : R f σ args with
  | ok σ' v =>
    have same := hR f σ args held σ' (show (R f σ args).welt = some σ' by rw [he]; rfl)
    exact (hok σ' v (entry.same same)).vor same
  | why σ' r =>
    have same := hR f σ args held σ' (show (R f σ args).welt = some σ' by rw [he]; rfl)
    exact (hwhy σ' r (entry.same same)).vor same
  | logik e => exact Outcome.logik _
  | hardware e => exact Outcome.hardware _

theorem EndOutcome.option {L : D.Lock} {bo : Option Int} {Λ : List (Res D)} {α : Type}
    {σ : World D} (entry : Entry (slack := slack) L bo Λ σ) (answer : World D × Option α)
    (same : answer.1.haelt = σ.haelt) (failure : Hardware D)
    (next : World D → α → EndAusgang V l Γ)
    (hn : ∀ σ' v, Entry (slack := slack) L bo Λ σ' → EndOutcome (slack := slack) L σ' (next σ' v)) :
    EndOutcome (slack := slack) L σ (match answer with
      | (σ', some v) => next σ' v | (_, none) => .hardware failure) := by
  rcases answer with ⟨σ', _ | v⟩
  · exact Outcome.hardware _
  · exact (hn σ' v (entry.same same)).vor same

theorem count_foldl_erase (L : D.Lock) (Ls h : List D.Lock) :
    (Ls.foldl (fun h M => h.erase M) h).count L = h.count L - Ls.count L := by
  induction Ls generalizing h with
  | nil => simp
  | cons M Ms ih =>
    rw [List.foldl_cons, ih]
    by_cases same : M = L
    · subst M
      rw [List.count_erase_self, List.count_cons_self]
      omega
    · rw [List.count_erase_of_ne (Ne.symm same), List.count_cons_of_ne same]

theorem end_count_zero (L : D.Lock) (residual : L ∉ V.haelt) : V.ende.count (Res.held L) = 0 :=
  List.count_eq_zero.mpr (fun h => residual ((held_ende V L).mp h))

/-- Exact typed cleanup removes the represented occurrences, retaining at most
    the caller's slack, independently of the order of the scope list. -/
theorem Entry.cleanup {L : D.Lock} {bo : Option Int} {Λ : List (Res D)} {σ : World D}
    (h : Entry (slack := slack) L bo Λ σ) (R : RueckRessourcen D V Λ) (residual : L ∉ V.haelt) :
    (R.scopes.foldl World.gibt σ).haelt.count L ≤ slack := by
  have balance := count_of_perm (a := Res.held L) R.genau
  rw [List.count_append, end_count_zero L residual, count_held_map, Nat.zero_add] at balance
  rw [haelt_gibt_foldl, count_foldl_erase]
  have heldCount := h.2
  omega

theorem Entry.exactReturn {L : D.Lock} {bo : Option Int} {Λ : List (Res D)} {σ : World D}
    (h : Entry (slack := slack) L bo Λ σ) (exact : Λ.Perm V.ende) (residual : L ∉ V.haelt) :
    σ.haelt.count L ≤ slack := by
  have balance := count_of_perm (a := Res.held L) exact
  rw [end_count_zero L residual] at balance
  have heldCount := h.2
  omega

end ReturnInventory
end Gabbro.Grammatik
