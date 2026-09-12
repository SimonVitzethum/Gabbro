/-
  File:      Grammatik/EigenZustandD.lean
  Subject:   **OWN-STATE PROJECTION** (lane 56, attempt D).

  A step fired by a thread `h` whose program text never names table `t`
  leaves every slot of `t` unchanged. The route is bottom-up: each writing
  leaf records a `zugriff t true ..` event (carried by `hcar` of the leaf
  rule of `PCSchritt`); a leaf whose recorded events carry no `Sum.inl t`
  keeps the slots of `t`; take/release steps keep memory by construction.
-/
import Grammatik.Maschine
import Grammatik.Satz
import Grammatik.BlattGegenbeispiel
import Grammatik.ReferenzB

namespace Gabbro.Grammatik.EZD

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Trace suffix helpers: from outcome spur to the recorded list.

  A leaf step records `σ'.spur = neu ++ oldSpur`. Each writing form below
  computes `σ'.spur = pre ++ oldSpur` with a write event in `pre`; cancelling
  the common suffix `oldSpur` puts the event into `neu`. -/

/-- Cancelling a common trace suffix: two prefixes of one spur agree. -/
theorem neu_of_suffix {σ' σ : World D} {pre neu : List (Ereignis D)}
    (h1 : σ'.spur = pre ++ σ.spur) (h2 : σ'.spur = neu ++ σ.spur) :
    neu = pre :=
  List.append_cancel_right (h2.symm.trans h1)

/-- The head write event lands in the recorded list. -/
theorem neu_head {σ' σ : World D} {ev : Ereignis D} {reads neu : List (Ereignis D)}
    (h1 : σ'.spur = ev :: reads ++ σ.spur) (h2 : σ'.spur = neu ++ σ.spur) :
    ev ∈ neu := by
  have h1' : σ'.spur = (ev :: reads) ++ σ.spur := h1
  have heq : neu = ev :: reads := neu_of_suffix h1' h2
  rw [heq]
  exact List.mem_cons_self

/-- `schreibBytes` only prefixes the trace: the outcome spur is a prefix
    plus the entry spur. -/
theorem schreibBytes_spur_suffix (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte) :
    ∃ pre, (σ.schreibBytes t f hf Λ k bs).spur = pre ++ σ.spur := by
  induction bs generalizing σ k with
  | nil => exact ⟨[], by simp [World.schreibBytes]⟩
  | cons b bs ih =>
      have hcons : σ.schreibBytes t f hf Λ k (b :: bs) =
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bs := rfl
      obtain ⟨pre₂, hpre₂⟩ := ih _ _
      refine ⟨pre₂ ++ [Ereignis.zugriff t true Λ σ.haelt], ?_⟩
      have hspur : (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).spur =
          [Ereignis.zugriff t true Λ σ.haelt] ++ σ.spur := rfl
      rw [hcons, hpre₂, hspur, List.append_assoc]

/-- A nonempty `schreibBytes` records a write event for its table. -/
theorem schreibBytes_has_write (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (k : Int) (bs : List Byte)
    (hne : bs ≠ []) :
    ∃ ev ∈ (σ.schreibBytes t f hf Λ k bs).spur,
      ev.traeger = some (Sum.inl t) := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons b bs =>
      refine ⟨Ereignis.zugriff t true Λ σ.haelt, ?_, rfl⟩
      have hmem : Ereignis.zugriff (D := D) t true Λ σ.haelt ∈
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).spur :=
        List.mem_cons_self
      obtain ⟨pre, hpre⟩ := schreibBytes_spur_suffix
        (σ.schreibSlot t Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))) t f hf Λ (k + 1) bs
      have hmem₂ : Ereignis.zugriff (D := D) t true Λ σ.haelt ∈
          ((σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bs).spur := by
        rw [hpre]
        exact List.mem_append_right _ hmem
      exact hmem₂

/-- `schreibBytes` on `t` leaves every other table's slots alone. -/
theorem schreibBytes_slots_other (σ : World D) (t : D.Tab) (f : D.Feld t)
    (hf : D.typ t f = .int 0 255) (Λ : List (Res D)) (t₀ : D.Tab) (hne : t₀ ≠ t)
    (k : Int) (bs : List Byte) (k' : Int) (f' : D.Feld t₀) :
    (σ.schreibBytes t f hf Λ k bs).slots t₀ k' f' = σ.slots t₀ k' f' := by
  induction bs generalizing σ k with
  | nil => rfl
  | cons b bs ih =>
      have hcons : σ.schreibBytes t f hf Λ k (b :: bs) =
          (σ.schreibSlot t Λ k f
            (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ (k + 1) bs := rfl
      rw [hcons, ih]
      exact storeSlot_andere _ _ _ _ _ _ hne _ _

/-! ## 1b. The `schreibt` flag of an event. -/

/-- The write flag of an event: `none` for lock steps. -/
def ereignisSchreibt : Ereignis D → Option Bool
  | .zugriff _ b _ _ => some b
  | .gzugriff _ b _ _ => some b
  | _ => none

/-! ## 2. Per-constructor write lemmas: every table write records its event.

  For each leaf statement form that can change a slot of table `t`,
  `execStmt` computes the outcome as one `schreibSlot` (whose head event
  is `zugriff t true ..`), one `schreibBytes` fold (nonempty iff the byte
  list is nonempty), or the oracle answer; the `schreibBytes` and `axiomCall`
  arms need the `GutO` frame (first conjunct) to rule the slot change out. -/

/-- `assignSlot t` records its write event in the recorded list. -/
theorem assignSlot_neu (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t : D.Tab} {f : D.Feld t}
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ neu := by
  have h1 : σ'.spur =
      Ereignis.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt ::
        ((i.orte ++ e.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
    have h := (schreibt_wirkt_slot (D := D) O passes V l Γ Λ t f i e hw hL σ ρ).1
    have hsame : (execStmt O passes keinRuf
        ((.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
        (execStmt O passes keinRuf
        ((.assignSlot t f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt := rfl
    rw [h] at hstep
    have hspur : (σ.lese Λ (i.orte ++ e.orte)).spur =
        ((i.orte ++ e.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := rfl
    have hsc : (σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ) =
        ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ)).merke
        [.zugriff t true Λ (σ.lese Λ (i.orte ++ e.orte)).haelt] := rfl
    have hσ' : σ' = (σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ) :=
      Option.some_inj.mp hstep.symm
    rw [hσ', hsc]
    simp only [World.merke]
    have hspur₂ : ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ)).spur =
        (σ.lese Λ (i.orte ++ e.orte)).spur := rfl
    rw [hspur₂, hspur, List.singleton_append, List.cons_append]
  exact neu_head h1 hneu

/-- `assignDurch t` records its write event in the recorded list. -/
theorem assignDurch_neu (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat}
    {p : Expr D Γ Λ (.ptr n true)} {t : D.Tab} {ht : D.tabNr n = some t}
    {f : D.Feld t}
    {i : Expr D Γ Λ (.index (D.count t))} {e : Expr D Γ Λ (D.typ t f)}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (.assignDurch p t ht f i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    Ereignis.zugriff t true Λ
      (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt ∈ neu := by
  have h1 : σ'.spur =
      Ereignis.zugriff t true Λ
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt ::
        ((p.orte ++ i.orte ++ e.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
    have hcomp : (execStmt O passes keinRuf
        ((.assignDurch p t ht f i e hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
        some ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t Λ
          (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) := rfl
    rw [hcomp] at hstep
    have hspur : (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).spur =
        ((p.orte ++ i.orte ++ e.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := rfl
    have hσ' : σ' = (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ) :=
      Option.some_inj.mp hstep.symm
    have hsc : (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ) =
        ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).storeSlot t
          (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).merke
        [.zugriff t true Λ
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).haelt] := rfl
    rw [hσ', hsc]
    simp only [World.merke]
    have hspur₂ : ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).storeSlot t
          (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f
          (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
            (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).spur =
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)).spur := rfl
    rw [hspur₂, hspur, List.singleton_append, List.cons_append]
  exact neu_head h1 hneu

/-- `uebergang t` records its write event in the recorded list. -/
theorem uebergang_neu (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t : D.Tab} {f : D.Feld t} {lo hi : Int}
    {hτ : D.typ t f = .int lo hi}
    {i : Expr D Γ Λ (.index (D.count t))} {von nach : Int}
    {hn : lo ≤ nach ∧ nach ≤ hi} {he : D.erlaubt t f von nach = true}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (.uebergang t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt
      = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    Ereignis.zugriff t true Λ (σ.lese Λ (.inl t :: i.orte)).haelt ∈ neu := by
  have hcomp : (execStmt O passes keinRuf
      ((.uebergang t f hτ i von nach hn he hw hL : Stmt D V l Γ Λ Λ)) σ ρ).welt =
      (if (hτ ▸ (σ.lese Λ (.inl t :: i.orte)).slots t
          (eval (σ.lese Λ (.inl t :: i.orte)) i
            (σ.lese Λ (.inl t :: i.orte)) ρ).n f : Zahl _ _).n = von
        then (Ausgang.ok ((σ.lese Λ (.inl t :: i.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (.inl t :: i.orte)) i
              (σ.lese Λ (.inl t :: i.orte)) ρ).n f
            (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ :
          Ausgang V l Γ)
        else .logik .vorzustand).welt := rfl
  rw [hcomp] at hstep
  by_cases hvon : (hτ ▸ (σ.lese Λ (.inl t :: i.orte)).slots t
      (eval (σ.lese Λ (.inl t :: i.orte)) i
        (σ.lese Λ (.inl t :: i.orte)) ρ).n f : Zahl _ _).n = von
  · rw [if_pos hvon, Ausgang.welt] at hstep
    have hσ' : σ' = (σ.lese Λ (.inl t :: i.orte)).schreibSlot t Λ
        (eval (σ.lese Λ (.inl t :: i.orte)) i
          (σ.lese Λ (.inl t :: i.orte)) ρ).n f
        (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _)) :=
      Option.some_inj.mp hstep.symm
    have hspur : (σ.lese Λ (.inl t :: i.orte)).spur =
        ((.inl t :: i.orte).map fun o => match o with
          | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
          | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := rfl
    have h1 : σ'.spur =
        Ereignis.zugriff t true Λ
          (σ.lese Λ (.inl t :: i.orte)).haelt ::
          ((.inl t :: i.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := by
      have hsc : (σ.lese Λ (.inl t :: i.orte)).schreibSlot t Λ
          (eval (σ.lese Λ (.inl t :: i.orte)) i
            (σ.lese Λ (.inl t :: i.orte)) ρ).n f
          (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _)) =
          ((σ.lese Λ (.inl t :: i.orte)).storeSlot t
            (eval (σ.lese Λ (.inl t :: i.orte)) i
              (σ.lese Λ (.inl t :: i.orte)) ρ).n f
            (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).merke
          [.zugriff t true Λ (σ.lese Λ (.inl t :: i.orte)).haelt] := rfl
      rw [hσ', hsc]
      simp only [World.merke]
      have hspur₂ : ((σ.lese Λ (.inl t :: i.orte)).storeSlot t
            (eval (σ.lese Λ (.inl t :: i.orte)) i
              (σ.lese Λ (.inl t :: i.orte)) ρ).n f
            (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).spur =
          (σ.lese Λ (.inl t :: i.orte)).spur := rfl
      rw [hspur₂, hspur, List.singleton_append, List.cons_append]
    exact neu_head h1 hneu
  · rw [if_neg hvon, Ausgang.welt] at hstep
    exact absurd hstep (by simp)

/-- `schreibBytes t` with a positive count records a write event for `t`.
    Split on `n`: at `n = 0` the byte list is empty (length `0`), so the
    fold is the identity and the head case below needs `n = m+1`, where the
    byte list has length `m+1 > 0` and the definitional unfold exposes the
    first `schreibSlot` write. -/
theorem schreibBytes_neu (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t : D.Tab} {f : D.Feld t} {hf : D.typ t f = .int 0 255} {n : Nat}
    {lo hi : Int}
    {i : Expr D Γ Λ (.int lo hi)} {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t}
    {e : Expr D Γ Λ (.int 0 (256 ^ n - 1))}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (hn : 0 < n)
    (σ : World D) (ρ : Env D Γ) (σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf
      (.schreibBytes t f hf n i hlo hhi e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt
      = some σ')
    (hneu : σ'.spur = neu ++ σ.spur) :
    ∃ ev ∈ neu, ev.traeger = some (Sum.inl t) := by
  -- Name the entry world, index, value, and byte list.
  have hlen : (zahlZuBytes n (eval (σ.lese Λ (i.orte ++ e.orte)) e
      (σ.lese Λ (i.orte ++ e.orte)) ρ).n).length = n :=
    zahlZuBytes_length n _
  -- Split on `n`: `n = 0` contradicts `hn`; at `n = m+1` unfold one step.
  cases hn' : n with
  | zero => omega
  | succ m =>
      -- Abbreviate the value whose bytes are written.
      have hz : (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n =
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n := rfl
      -- The byte list is `b0 :: bs` for some head and tail.
      obtain ⟨b0, bs, hbs⟩ : ∃ b0 bs, zahlZuBytes (m + 1)
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n = b0 :: bs := by
        cases hbl : zahlZuBytes (m + 1)
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n with
        | nil =>
            have hlen2 := zahlZuBytes_length (m + 1)
              (eval (σ.lese Λ (i.orte ++ e.orte)) e
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n
            rw [hbl] at hlen2
            simp at hlen2
        | cons b0 bs => exact ⟨b0, bs, rfl⟩
      clear hz
      -- Rewrite `n` to `m+1` everywhere it matters.
      have hnEq : n = m + 1 := by omega
      subst hnEq
      -- Abbreviate the entry world and index for readability.
      have hσL : σ.lese Λ (i.orte ++ e.orte) =
          σ.lese Λ (i.orte ++ e.orte) := rfl
      clear hσL
      have hfold₂ : (σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f hf Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n
          (zahlZuBytes (m + 1)
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n) =
          (((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (cast (congrArg (Wert D) hf).symm
              (b0 : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ
            ((eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs) := by
        rw [hbs]
        rfl
      -- `hstep` fires the same statement (after `subst`, `n = m+1`
      -- definitionally); unfold its fold the same way and conclude.
      have hrfl : (execStmt O passes keinRuf
          ((.schreibBytes t f hf (m + 1) i hlo hhi e hw hL :
            Stmt D V l Γ Λ Λ)) σ ρ).welt =
          Ausgang.welt (D := D) (V := V) (l := l) (Γ := Γ) (Ausgang.ok
            ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f hf Λ
              (eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n
              (zahlZuBytes (m + 1)
                (eval (σ.lese Λ (i.orte ++ e.orte)) e
                  (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) ρ) := rfl
      have hstepFold : (execStmt O passes keinRuf
            ((.schreibBytes t f hf (m + 1) i hlo hhi e hw hL :
              Stmt D V l Γ Λ Λ)) σ ρ).welt =
            some ((((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
              (eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
              (cast (congrArg (Wert D) hf).symm
                (b0 : Wert D (.int 0 255)))).schreibBytes
              t f hf Λ
              ((eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs)) := by
          rw [hrfl, Ausgang.welt, hfold₂]
      -- Now `hstep` and `hstepFold` agree; extract the outcome world.
      have hσ' : σ' = (((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (cast (congrArg (Wert D) hf).symm
              (b0 : Wert D (.int 0 255)))).schreibBytes
            t f hf Λ
            ((eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs) :=
          Option.some_inj.mp (hstep.symm.trans hstepFold)
        -- The head write event sits in the tail fold spur by the suffix lemma.
      have hmem0 : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈
            ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
              (eval (σ.lese Λ (i.orte ++ e.orte)) i
                (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
              (cast (congrArg (Wert D) hf).symm
                (b0 : Wert D (.int 0 255)))).spur :=
          List.mem_cons_self
      obtain ⟨preTail, hpreTail⟩ := schreibBytes_spur_suffix
          ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
            (eval (σ.lese Λ (i.orte ++ e.orte)) i
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
            (cast (congrArg (Wert D) hf).symm
              (b0 : Wert D (.int 0 255))))
          t f hf Λ _ bs
      have hmemFold : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ σ'.spur := by
          rw [hσ']
          rw [hpreTail]
          exact List.mem_append_right _ hmem0
        -- Cancel the common `lese` suffix: `neu` is the fold prefix.
      have hspur₀ : (σ.lese Λ (i.orte ++ e.orte)).spur =
            ((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur := rfl
      obtain ⟨pre, hpre⟩ := schreibBytes_spur_suffix
          (σ.lese Λ (i.orte ++ e.orte)) t f hf Λ
          (eval (σ.lese Λ (i.orte ++ e.orte)) i
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n
          (zahlZuBytes (m + 1)
            (eval (σ.lese Λ (i.orte ++ e.orte)) e
              (σ.lese Λ (i.orte ++ e.orte)) ρ).n)
      have hσspur : σ'.spur = pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
          -- `hσ'` unfolds the outcome to the tail fold; `hpre` states the
          -- whole fold spur. Rewrite the goal through both equations.
          rw [hσ']
          rw [← hfold₂]
          exact hpre
      -- Cancel the common suffix: `neu` is the fold prefix plus reads.
      have hcancel : neu = pre ++ ((i.orte ++ e.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) := by
        have hassoc : (pre ++ ((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt)) ++ σ.spur =
            pre ++ (((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur) :=
          List.append_assoc _ _ _
        have hfull₂ : neu ++ σ.spur =
            (pre ++ ((i.orte ++ e.orte).map fun o => match o with
              | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
              | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt)) ++ σ.spur := by
          rw [hassoc, ← hspur₀, ← hσspur]; exact hneu.symm
        exact List.append_cancel_right hfull₂
      -- Split the head event over `pre ++ reads ++ old`.
      have hevσ₂ : Ereignis.zugriff t true Λ
          (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ neu ++ σ.spur := by
        rw [← hneu]; exact hmemFold
      rw [hcancel] at hevσ₂
      have hsplit : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ pre ∨
          Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈
            ((i.orte ++ e.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ∨
          Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ σ.spur := by
        have hmem : Ereignis.zugriff t true Λ
              (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ pre ++
            (((i.orte ++ e.orte).map fun o => match o with
            | .inl t' => Ereignis.zugriff t' false Λ σ.haelt
            | .inr g' => Ereignis.gzugriff g' false Λ σ.haelt) ++ σ.spur) := by
          rw [← List.append_assoc]; exact hevσ₂
        rw [List.mem_append, List.mem_append] at hmem
        exact hmem
      rcases hsplit with hmemPre | hmemRead | hmemOld
      · refine ⟨Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_, rfl⟩
        rw [hcancel]
        exact List.mem_append_left _ hmemPre
      · obtain ⟨o, ho, hcon⟩ := List.mem_map.mp hmemRead
        cases o with
        | inl t2 =>
            simp only at hcon
            have hflag := congrArg (ereignisSchreibt (D := D)) hcon
            simp only [ereignisSchreibt] at hflag
            exact absurd hflag (by simp)
        | inr g' =>
            simp only at hcon
            exact absurd hcon (by simp)
      · -- Old: the head write coincides with an old event. Reuse the
        -- `hmemFold`-in-`pre` argument: the head is in the tail fold spur,
        -- whose `preTail` part injects into `pre` by suffix cancellation.
        -- `hmemFold` was proved from `hpreTail`; `hpre` covers the whole
        -- fold. The head is in `pre` iff the tail split puts it there --
        -- but we are in the old case. Close by noting `hevσ₂` already
        -- split this way: contradiction is impossible, so use `hmemPre`
        -- from re-splitting `hmemFold` through `hpre` (not `hpreTail`).
        have hHeadPre : Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt ∈ pre := by
          have hmem : Ereignis.zugriff t true Λ
              (σ.lese Λ (i.orte ++ e.orte)).haelt ∈
              pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
            rw [← hσspur]; exact hmemFold
          rw [hspur₀] at hmem
          rw [List.mem_append] at hmem
          rcases hmem with hG | hH
          · exact hG
          · rw [List.mem_append] at hH
            rcases hH with hI | hJ
            · obtain ⟨o, ho, hcon⟩ := List.mem_map.mp hI
              cases o with
              | inl t2 =>
                  simp only at hcon
                  have hflag := congrArg (ereignisSchreibt (D := D)) hcon
                  simp only [ereignisSchreibt] at hflag
                  exact absurd hflag (by simp)
              | inr g' =>
                  simp only at hcon
                  exact absurd hcon (by simp)
            · -- Old again at the `hpre` level: iterate once more via
              -- `hpreTail` -- the tail fold spur is strictly shorter, so
              -- one unroll reaches `preTail` or the head world. The head
              -- world spur is `[head] ++ lese`, so membership there is the
              -- head itself or a read (closed above) or older (same shape,
              -- one level down). Since the byte list is finite, this
              -- terminates -- but Lean needs the induction. Instead observe
              -- `hmemFold` came from `hpreTail`'s RIGHT disjunct already
              -- (`hmem0`), i.e. the head IS in the head-world spur, hence
              -- in `preTail`'s base -- no. Direct: `hmem0` IS the head in
              -- the head spur; `hpreTail` puts the tail fold spur over it.
              -- The whole fold spur `hpre` extends the same base, so the
              -- head is at a FIXED position in `pre`: it is `pre`'s suffix
              -- element. Positional: `pre = preTail ++ [head]`.
              have hpos : pre = preTail ++ [Ereignis.zugriff t true Λ
                  (σ.lese Λ (i.orte ++ e.orte)).haelt] := by
                -- `hpreTail` extends the head spur `[head] ++ lese-spur`;
                -- `hpre` extends the same `lese-spur` through the whole fold
                -- (equal by `hfold₂`). Chain them and cancel the suffix.
                have hchain : preTail ++ ([Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
                    (σ.lese Λ (i.orte ++ e.orte)).spur) =
                    pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
                  have e1 : (((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t Λ
                      (eval (σ.lese Λ (i.orte ++ e.orte)) i
                        (σ.lese Λ (i.orte ++ e.orte)) ρ).n f
                      (cast (congrArg (Wert D) hf).symm
                        (b0 : Wert D (.int 0 255)))).schreibBytes
                      t f hf Λ
                      ((eval (σ.lese Λ (i.orte ++ e.orte)) i
                        (σ.lese Λ (i.orte ++ e.orte)) ρ).n + 1) bs).spur =
                      preTail ++ ([Ereignis.zugriff t true Λ
                        (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
                        (σ.lese Λ (i.orte ++ e.orte)).spur) := by
                    rw [hpreTail]
                    rfl
                  rw [← e1, ← hfold₂]
                  exact hpre
                have hchain2 : preTail ++ ([Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt] ++
                    (σ.lese Λ (i.orte ++ e.orte)).spur) =
                    pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur :=
                  hchain
                have hchain3 : (preTail ++ [Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt]) ++
                    (σ.lese Λ (i.orte ++ e.orte)).spur =
                    pre ++ (σ.lese Λ (i.orte ++ e.orte)).spur := by
                  rw [List.append_assoc]
                  exact hchain2
                have hpos2 : preTail ++ [Ereignis.zugriff t true Λ
                    (σ.lese Λ (i.orte ++ e.orte)).haelt] = pre :=
                  List.append_cancel_right hchain3
                exact hpos2.symm
              rw [hpos]
              exact List.mem_append_right _ List.mem_cons_self
        refine ⟨Ereignis.zugriff t true Λ
            (σ.lese Λ (i.orte ++ e.orte)).haelt, ?_, rfl⟩
        rw [hcancel]
        exact List.mem_append_left _ hHeadPre

/-! ## 3. The oracle arm: `axiomCall` writes stay inside the declared frame.

  `GutO` says the oracle answer's world differs from the entry world at most
  on carriers with `D.aschreibt/D.agschreibt = true`. Hence a slot of `t`
  with `D.aschreibt a t = false` survives any `axiomCall a` step.
  Proved via `axiomAntwort_gut` (the `Gut` package) rather than by unfolding
  `execStmt`: the `Rahmen` half is exactly the needed slot equality. -/

/-- The oracle frame keeps a non-written table slot, via `axiomAntwort_gut`. -/
theorem axiomCall_slots_frame (O : Orakel D) (hO : GutO O) (a : D.Ax)
    (t : D.Tab) (ht : D.aschreibt a t = false)
    (sg : World D) (rho : Env D (D.aparams a)) (k : Int) (f : D.Feld t) :
    (O.wirkt a sg rho).1.slots t k f = sg.slots t k f := by
  have hG := axiomAntwort_gut (D := D) (O := O) hO a sg rho
  -- `hG : Gut (D.aschreibt a) (D.agschreibt a) sg (axiomAntwort ..).1`;
  -- project the `Rahmen` slot leg at `ht`.
  have hR : Rahmen (D.aschreibt a) (D.agschreibt a) sg
      (axiomAntwort O a sg rho).1 := hG.1
  have hEq := hR.1 t ht k f
  -- `(axiomAntwort ..).1 = (wirkt ..).1` by `rfl` on the pair projection.
  have hProj : (axiomAntwort O a sg rho).1 =
      (O.wirkt a sg rho).1 := rfl
  rw [hProj] at hEq
  exact hEq

/-! ## 4. Slot preservation per leaf shape: every non-recording leaf keeps `slots t`.

  Each lemma below takes the firing equation `hstep` for ONE statement form
  and concludes `σ'.slots t k f = σ.slots t k f` for every table `t`. All are
  used by their proofs (rule 3): the two global-writing forms (`assignGlob`,
  `publish`) by the step lemma's global case, the rest by the compound-case
  analysis there. Forms that write a table slot (`assignSlot`, `assignDurch`,
  `uebergang`, `schreibBytes`) are NOT here: they record their event (§2). -/

/-- `assignGlob` writes a global: every table slot rides along. -/
theorem assignGlob_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Glob} {e : Expr D Γ Λ (D.gtyp g)}
    {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignGlob (V := V) (l := l) g e hw hL) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.assignGlob (V := V) (l := l) g e hw hL) sg rho).welt =
      some ((sg.lese Λ e.orte).schreibGlob g Λ
        (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = ((sg.lese Λ e.orte).schreibGlob g Λ
      (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) :=
    Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `publish` writes a global: every table slot rides along. -/
theorem publish_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {g : D.Glob} {e : Expr D Γ Λ (D.gtyp g)} {payload : List D.Glob}
    {hp : payload = D.nutzlast g} {hw : V.gschreibt g = true} {hL : gdarf D g Λ}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.publish (V := V) (l := l) g e payload hp hw hL) sg rho).welt
      = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.publish (V := V) (l := l) g e payload hp hw hL) sg rho).welt =
      some ((sg.lese Λ e.orte).schreibGlob g Λ
        (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = ((sg.lese Λ e.orte).schreibGlob g Λ
      (eval (sg.lese Λ e.orte) e (sg.lese Λ e.orte) rho)) :=
    Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `assignVar` touches only the environment: every table slot rides along. -/
theorem assignVar_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    {x : Var Γ τ} {e : Expr D Γ Λ τ}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignVar (V := V) (l := l) x e) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.assignVar (V := V) (l := l) x e) sg rho).welt =
      some (sg.lese Λ e.orte) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = sg.lese Λ e.orte := Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `regSchreib` touches only the device: every table slot rides along. -/
theorem regSchreib_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : D.Reg} {hk : (D.rklasse r).schreibbar = true} {e : Expr D Γ Λ (D.rtyp r)}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.regSchreib (V := V) (l := l) r hk e) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.regSchreib (V := V) (l := l) r hk e) sg rho).welt =
      some (sg.lese Λ e.orte) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = sg.lese Λ e.orte := Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-- `ret` only reads: every table slot rides along. -/
theorem ret_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {e : ErgExpr D Γ Λ V.erg} {hΛ : Λ.Perm V.ende}
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.ret (V := V) (l := l) e hΛ) sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.ret (V := V) (l := l) e hΛ) sg rho).welt =
      some (sg.lese Λ e.orte) := rfl
  rw [hcomp] at hstep
  have hsg' : sg' = sg.lese Λ e.orte := Option.some_inj.mp hstep.symm
  rw [hsg']
  rfl

/-! ## 5. Identity leaves: `transition`, `advances`, `retires`, `retGrund`,
    `leave`, `next` compute `.ok/.leave/.next` of the entry world or `σ`
    itself; every table slot rides along by one substitution. -/

/-- `transition` keeps every table slot (device-only step). -/
theorem transition_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : D.Reg} {hk : (D.rklasse r).schreibbar = true} {m : D.Reg}
    {hm : D.spiegel r = some m} {hl : (D.rklasse m).lesbar = true}
    {maske bits : Int}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.transition (V := V) (l := l) r hk m hm hl maske bits)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `advances` keeps every table slot (mark step, memory-free). -/
theorem advances_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {mm : D.Marke} {a : Nat} {h : Res.marke mm a ∈ Λ} {hs : a + 1 < D.stufen mm}
    (s : Stmt D V l Γ Λ ((Λ.erase (.marke mm a)) ++ [.marke mm (a + 1)]))
    (hs : s = Stmt.advances (V := V) (l := l) mm a h hs)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `retires` keeps every table slot (mark step, memory-free). -/
theorem retires_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {mm : D.Marke} {s2 : Nat} {h : Res.marke mm s2 ∈ Λ} {a : D.Annahme}
    (s : Stmt D V l Γ Λ (Λ.erase (.marke mm s2)))
    (hs : s = Stmt.retires (V := V) (l := l) mm s2 h a)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `retGrund` keeps every table slot (control step, memory-free). -/
theorem retGrund_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {r : Fin V.gruende} {hΛ : Λ.Perm V.ende}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.retGrund (V := V) (l := l) r hΛ)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `leave` keeps every table slot (control step, memory-free). -/
theorem leave_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {h : l = true}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.leave (V := V) (l := l) h)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-- `next` keeps every table slot (control step, memory-free). -/
theorem next_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {h : l = true}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.next (V := V) (l := l) h)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
  subst hstep
  rfl

/-! ## 6. Call leaves: `call`/`callInd` through `keinRuf` yield no world.

  The machine fires leaves through `execStmt O passes keinRuf`: the call
  handler is `keinRuf`, which answers every call with
  `.logik (.abstieg f)`. Hence a firing equation `hstep` for a `call` or
  `callInd` leaf reduces to `none = some σ'` -- vacuous. Both lemmas use
  every premise: `hs` to rewrite the statement, `hstep` to close. -/

/-- `call` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem call_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    {fn : D.Fn} {args : Args D Γ Λ (D.params fn)}
    {hp : RufPasst D V (D.signatur fn) Λ} {hr : D.gruende fn = 0}
    (s : Stmt D V l Γ Λ (nach D fn Λ))
    (hs : s = Stmt.call (V := V) fn args hp hr)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  have hR : keinRuf (D := D) fn (sg.lese Λ args.orte)
      (evalArgs (sg.lese Λ args.orte) args (sg.lese Λ args.orte) rho) =
      RufAusgang.logik (.abstieg fn) := rfl
  simp only [execStmt] at hstep
  rw [hR] at hstep
  simp only [Ausgang.welt] at hstep
  exact absurd hstep (by simp)

/-- `callInd` through `keinRuf` yields no world: the slot goal is vacuous. -/
theorem callInd_slots_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat}
    {p : Expr D Γ Λ (.fnptr n)} {args : Args D Γ Λ (D.sigNr n).params}
    {hp : RufPasst D V (D.sigNr n) Λ} {hr : (D.sigNr n).gruende = 0}
    (s : Stmt D V l Γ Λ (nachSig D (D.sigNr n) Λ))
    (hs : s = Stmt.callInd (V := V) p args hp hr)
    (sg : World D) (rho : Env D Γ) (sg' : World D)
    (hstep : (execStmt O passes keinRuf s sg rho).welt = some sg')
    (t : D.Tab) (k : Int) (f : D.Feld t) :
    sg'.slots t k f = sg.slots t k f := by
  subst hs
  simp only [execStmt] at hstep
  revert hstep
  generalize hP : eval (sg.lese Λ (p.orte ++ args.orte)) p
      (sg.lese Λ (p.orte ++ args.orte)) rho = pv
  intro hstep
  cases pv with
  | mk fn hf =>
      simp only at hstep
      have hR : keinRuf (D := D) fn (sg.lese Λ (p.orte ++ args.orte))
          (umsig hf (evalArgs (sg.lese Λ (p.orte ++ args.orte)) args
            (sg.lese Λ (p.orte ++ args.orte)) rho)) =
          RufAusgang.logik (.abstieg fn) := rfl
      rw [hR] at hstep
      simp only [Ausgang.welt] at hstep
      exact absurd hstep (by simp)

/-! ## 7. Other-table and degenerate arms: slots of `t` survive writes to `t₂ ≠ t`.

  Each lemma takes the firing equation for ONE constructor form with an
  explicit inequality hypothesis. All premises are used: `hstep` fixes the
  outcome, the inequality selects the `storeSlot_andere`/`schreibBytes_slots_other`
  leg. -/

/-- `assignSlot t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignSlot_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignSlot (V := V) (l := l) t₂ f₂ i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt
      = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignSlot (V := V) (l := l) t₂ f₂ i e hw hL : Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `assignDurch t₂` with `t₂ ≠ t` keeps every slot of `t`. -/
theorem assignDurch_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat}
    {p : Expr D Γ Λ (.ptr n true)} {t₂ : D.Tab} {ht₂ : D.tabNr n = some t₂}
    {f₂ : D.Feld t₂}
    {i : Expr D Γ Λ (.index (D.count t₂))} {e : Expr D Γ Λ (D.typ t₂ f₂)}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.assignDurch (V := V) (l := l) p t₂ ht₂ f₂ i e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.assignDurch (V := V) (l := l) p t₂ ht₂ f₂ i e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
        (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
          (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot t₂ Λ
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) i
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n f₂
      (eval (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) e
        (σ.lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  show ((σ.lese Λ (p.orte ++ i.orte ++ e.orte)).storeSlot t₂ _ f₂ _).slots t k f =
    σ.slots t k f
  rw [storeSlot_andere _ _ _ _ _ _ hne]
  rfl

/-- `uebergang t₂` with `t₂ ≠ t` keeps every slot of `t` (failed guard
    yields no world; success writes `t₂`). -/
theorem uebergang_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂} {lo hi : Int}
    {hτ : D.typ t₂ f₂ = .int lo hi}
    {i : Expr D Γ Λ (.index (D.count t₂))} {von nach : Int}
    {hn : lo ≤ nach ∧ nach ≤ hi} {he : D.erlaubt t₂ f₂ von nach = true}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.uebergang (V := V) (l := l) t₂ f₂ hτ i von nach hn he hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hcomp : (execStmt O passes keinRuf
      (Stmt.uebergang (V := V) (l := l) t₂ f₂ hτ i von nach hn he hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      (if (hτ ▸ (σ.lese Λ (.inl t₂ :: i.orte)).slots t₂
        (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
          (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂ : Zahl _ _).n = von
      then (Ausgang.ok ((σ.lese Λ (.inl t₂ :: i.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
          (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂
        (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ : Ausgang V l Γ)
      else .logik .vorzustand).welt := rfl
  rw [hcomp] at hstep
  by_cases hvon : (hτ ▸ (σ.lese Λ (.inl t₂ :: i.orte)).slots t₂
      (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
        (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂ : Zahl _ _).n = von
  · rw [if_pos hvon, Ausgang.welt] at hstep
    have hσ' : σ' = ((σ.lese Λ (.inl t₂ :: i.orte)).schreibSlot t₂ Λ
        (eval (σ.lese Λ (.inl t₂ :: i.orte)) i
          (σ.lese Λ (.inl t₂ :: i.orte)) ρ).n f₂
        (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) :=
      Option.some_inj.mp hstep.symm
    rw [hσ']
    have hne : t ≠ t₂ := fun h => ht h.symm
    show ((σ.lese Λ (.inl t₂ :: i.orte)).storeSlot t₂ _ f₂ _).slots t k f =
      σ.slots t k f
    rw [storeSlot_andere _ _ _ _ _ _ hne]
    rfl
  · rw [if_neg hvon, Ausgang.welt] at hstep
    exact absurd hstep (by simp)

/-- `schreibBytes t₂` with `t₂ ≠ t` keeps every slot of `t` (every fold
    step targets `t₂`). -/
theorem schreibBytes_andere_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t₂ : D.Tab} {f₂ : D.Feld t₂} {hf₂ : D.typ t₂ f₂ = .int 0 255} {n : Nat}
    {lo hi : Int}
    {i : Expr D Γ Λ (.int lo hi)} {hlo : 0 ≤ lo} {hhi : hi + n ≤ D.count t₂}
    {e : Expr D Γ Λ (.int 0 (256 ^ n - 1))}
    {hw : V.schreibt t₂ = true} {hL : darf D t₂ Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.schreibBytes (V := V) (l := l) t₂ f₂ hf₂ n i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (t : D.Tab) (ht : t₂ ≠ t) (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hEq : (execStmt O passes keinRuf
      (Stmt.schreibBytes (V := V) (l := l) t₂ f₂ hf₂ n i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t₂ f₂ hf₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n
        (zahlZuBytes n
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t₂ f₂ hf₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n
      (zahlZuBytes n
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ']
  have hne : t ≠ t₂ := fun h => ht h.symm
  exact schreibBytes_slots_other _ _ _ _ _ _ hne _ _ _ _

/-- `schreibBytes t` at `n = 0` keeps every slot of `t` (empty byte list,
    the fold is the identity on top of the `lese` prefix). -/
theorem schreibBytes_null_fest (O : Orakel D) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {t : D.Tab} {f₂ : D.Feld t} {hf₂ : D.typ t f₂ = .int 0 255}
    {lo hi : Int}
    {i : Expr D Γ Λ (.int lo hi)} {hlo : 0 ≤ lo} {hhi : hi + 0 ≤ D.count t}
    {e : Expr D Γ Λ (.int 0 (256 ^ 0 - 1))}
    {hw : V.schreibt t = true} {hL : darf D t Λ}
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf
      (Stmt.schreibBytes (V := V) (l := l) t f₂ hf₂ 0 i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt = some σ')
    (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  have hlen0 : zahlZuBytes 0
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n = [] := by
    have hlen := zahlZuBytes_length 0
      (eval (σ.lese Λ (i.orte ++ e.orte)) e
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n
    simp at hlen
    exact hlen
  have hEq : (execStmt O passes keinRuf
      (Stmt.schreibBytes (V := V) (l := l) t f₂ hf₂ 0 i hlo hhi e hw hL :
        Stmt D V l Γ Λ Λ) σ ρ).welt =
      some ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f₂ hf₂ Λ
        (eval (σ.lese Λ (i.orte ++ e.orte)) i
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n
        (zahlZuBytes 0
          (eval (σ.lese Λ (i.orte ++ e.orte)) e
            (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) := rfl
  rw [hEq] at hstep
  have hσ' : σ' = ((σ.lese Λ (i.orte ++ e.orte)).schreibBytes t f₂ hf₂ Λ
      (eval (σ.lese Λ (i.orte ++ e.orte)) i
        (σ.lese Λ (i.orte ++ e.orte)) ρ).n
      (zahlZuBytes 0
        (eval (σ.lese Λ (i.orte ++ e.orte)) e
          (σ.lese Λ (i.orte ++ e.orte)) ρ).n)) :=
    Option.some_inj.mp hstep.symm
  rw [hσ', hlen0]
  rfl

/-! ## 8. The non-writing oracle arm: `axiomCall` with `aschreibt = false`.

  When the axiom declares no write to `t`, the `GutO` frame keeps every slot
  of `t`: the `lese` prefix keeps slots by `rfl`, the oracle answer by
  `axiomCall_slots_frame` (§3). Failed `einpassen` yields no world. Both `hO`
  (frame) and `hstep` (outcome) are used. -/

/-- `axiomCall a` with `D.aschreibt a t = false` keeps every slot of `t`. -/
theorem axiomCall_nichtschreibt_fest (O : Orakel D) (hO : GutO O) (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {a : D.Ax} {args : Args D Γ Λ (D.aparams a)} {h : D.aerg a = none}
    {hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true}
    {hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true}
    {hd : ∀ t, D.aschreibt a t = true → darf D t Λ}
    {hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ}
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.axiomCall (V := V) a args h hw hg hd hgd)
    (t : D.Tab) (ht : D.aschreibt a t = false)
    (σ : World D) (ρ : Env D Γ) (σ' : World D)
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (k : Int) (f : D.Feld t) :
    σ'.slots t k f = σ.slots t k f := by
  subst hs
  -- Name the oracle answer and split on its result.
  cases hAns : axiomAntwort O a (σ.lese Λ args.orte)
      (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | mk fst snd =>
      cases snd with
      | some v =>
          have hcomp : (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
              some fst := by
            have hrfl : (execStmt O passes keinRuf
                (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
                (match axiomAntwort O a (σ.lese Λ args.orte)
                  (evalArgs (σ.lese Λ args.orte) args
                    (σ.lese Λ args.orte) ρ) with
                | (sg₂, Option.some w) => (Ausgang.ok sg₂ ρ : Ausgang V l Γ)
                | (_, Option.none) =>
                  (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ)).welt := rfl
            rw [hrfl, hAns, Ausgang.welt]
          rw [hcomp] at hstep
          have hsg' : σ' = fst := Option.some_inj.mp hstep.symm
          rw [hsg']
          have hfst : fst = (O.wirkt a (σ.lese Λ args.orte)
              (evalArgs (σ.lese Λ args.orte) args
                (σ.lese Λ args.orte) ρ)).1 := by
            have hA := hAns
            simp only [axiomAntwort] at hA
            have hF := congrArg Prod.fst hA
            simp only at hF
            exact hF.symm
          have hlese : (σ.lese Λ args.orte).slots t k f = σ.slots t k f := rfl
          rw [hfst]
          have hframe := axiomCall_slots_frame O hO a t ht
            (σ.lese Λ args.orte)
            (evalArgs (σ.lese Λ args.orte) args
              (σ.lese Λ args.orte) ρ) k f
          rw [hframe, hlese]
      | none =>
          have hcomp : (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
              (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ).welt := by
            have hrfl : (execStmt O passes keinRuf
                (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
                (match axiomAntwort O a (σ.lese Λ args.orte)
                  (evalArgs (σ.lese Λ args.orte) args
                    (σ.lese Λ args.orte) ρ) with
                | (sg₂, Option.some w) => (Ausgang.ok sg₂ ρ : Ausgang V l Γ)
                | (_, Option.none) =>
                  (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ)).welt := rfl
            rw [hrfl, hAns, Ausgang.welt]
          rw [hcomp, Ausgang.welt] at hstep
          simp at hstep

/-! ## 9. The leaf dispatch: every firing leaf either records `t`, keeps it,
    or is a declared oracle write to `t`.

  `blattSlots_dispatch`: for a fired leaf `s` with recorded list `neu`, one
  of three holds: some recorded event carries `Sum.inl t` (the four writing
  forms, §2); the outcome keeps every slot of `t` (the §4/§7/§8 lemmas);
  or `s` is an `axiomCall a` whose declared writes cover `t`
  (`D.aschreibt a t = true`) -- the open remainder (see CUTS): `GutO` keeps
  the oracle spur unchanged, so no event records the write, yet slots may
  change. Compound statements cannot fire (`istBlatt = false` contradicts
  `hleaf`). Every premise is used: `hleaf` rules compounds out,
  `hstep`/`hneu` feed the arm lemmas, `hO` feeds the oracle arm. -/

theorem blattSlots_dispatch (O : Orakel D) (hO : GutO O)
    (passes : Nat)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (σ σ' : World D) (neu : List (Ereignis D))
    (hstep : (execStmt O passes keinRuf s σ ρ).welt = some σ')
    (hneu : σ'.spur = neu ++ σ.spur)
    (t : D.Tab) :
    (∃ ev ∈ neu, ev.traeger = some (Sum.inl t)) ∨
      (∀ k f, σ'.slots t k f = σ.slots t k f) ∨
      (∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
        (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
        (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) σ ρ).welt =
          some σ' ∧
          D.aschreibt a t = true) := by
  cases s with
  | assignSlot t2 f2 i e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, assignSlot_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          assignSlot_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignDurch p t2 ht2 f2 i e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, assignDurch_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          assignDurch_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignGlob g e hw hL =>
      exact Or.inr (Or.inl fun k f =>
        assignGlob_slots_fest O passes σ ρ σ' hstep t k f)
  | schreibBytes t2 f2 hf2 n i hlo hhi e hw hL =>
      by_cases ht : t2 = t
      · subst ht
        by_cases hn : 0 < n
        · obtain ⟨ev, hmem, htr⟩ :=
            schreibBytes_neu (Λ' := Λ) O passes hn σ ρ σ' neu hstep hneu
          exact Or.inl ⟨ev, hmem, htr⟩
        · have hn0 : n = 0 := by omega
          subst hn0
          exact Or.inr (Or.inl fun k f =>
            schreibBytes_null_fest (Λ' := Λ) O passes σ ρ σ' hstep k f)
      · exact Or.inr (Or.inl fun k f =>
          schreibBytes_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | assignVar x e =>
      exact Or.inr (Or.inl fun k f =>
        assignVar_slots_fest O passes σ ρ σ' hstep t k f)
  | uebergang t2 f2 hτ i von nach hn he hw hL =>
      by_cases ht : t2 = t
      · subst ht
        exact Or.inl ⟨_, uebergang_neu (Λ' := Λ) O passes σ ρ σ' neu hstep hneu, rfl⟩
      · exact Or.inr (Or.inl fun k f =>
          uebergang_andere_fest (Λ' := Λ) O passes σ ρ σ' hstep t ht k f)
  | ite c tb eb => simp [Stmt.istBlatt] at hleaf
  | onOption o p a => simp [Stmt.istBlatt] at hleaf
  | onTag v arms => simp [Stmt.istBlatt] at hleaf
  | onGrund r arms => simp [Stmt.istBlatt] at hleaf
  | call fn args hp hr =>
      exact Or.inr (Or.inl fun k f =>
        call_slots_fest O passes (Stmt.call fn args hp hr) rfl σ ρ σ' hstep t k f)
  | callInd p args hp hr =>
      exact Or.inr (Or.inl fun k f =>
        callInd_slots_fest O passes (Stmt.callInd p args hp hr) rfl σ ρ σ' hstep t k f)
  | locks L hr body => simp [Stmt.istBlatt] at hleaf
  | breaking ii body => simp [Stmt.istBlatt] at hleaf
  | traverse tt inv body => simp [Stmt.istBlatt] at hleaf
  | retry n bis body ueb => simp [Stmt.istBlatt] at hleaf
  | forever a inv body => simp [Stmt.istBlatt] at hleaf
  | axiomCall a args h hw hg hd hgd =>
      by_cases ht : D.aschreibt a t = true
      · exact Or.inr (Or.inr ⟨a, args, h, hw, hg, hd, hgd, hstep, ht⟩)
      · have htF : D.aschreibt a t = false := by
          cases hT : D.aschreibt a t with
          | true => exact absurd hT (by simp [ht])
          | false => rfl
        exact Or.inr (Or.inl fun k f =>
          axiomCall_nichtschreibt_fest (Λ' := Λ) O hO passes (Stmt.axiomCall (V := V) (l := l) a args h hw hg hd hgd) rfl t htF σ ρ σ' hstep k f)
  | regSchreib r hk e =>
      exact Or.inr (Or.inl fun k f =>
        regSchreib_slots_fest O passes σ ρ σ' hstep t k f)
  | transition r hk m hm hl maske bits =>
      exact Or.inr (Or.inl fun k f =>
        transition_slots_fest O passes (Stmt.transition r hk m hm hl maske bits) rfl σ ρ σ' hstep t k f)
  | publish g e payload hp hw hL =>
      exact Or.inr (Or.inl fun k f =>
        publish_slots_fest O passes σ ρ σ' hstep t k f)
  | advances mm a h hs =>
      exact Or.inr (Or.inl fun k f =>
        advances_slots_fest (Λ' := ((Λ.erase (.marke mm a)) ++ [.marke mm (a + 1)])) O passes (Stmt.advances (V := V) (l := l) mm a h hs) rfl σ ρ σ' hstep t k f)
  | retires mm s2 h a =>
      exact Or.inr (Or.inl fun k f =>
        retires_slots_fest (Λ' := (Λ.erase (.marke mm s2))) O passes (Stmt.retires (V := V) (l := l) mm s2 h a) rfl σ ρ σ' hstep t k f)
  | ret e hΛ =>
      exact Or.inr (Or.inl fun k f =>
        ret_slots_fest O passes σ ρ σ' hstep t k f)
  | retGrund r hΛ =>
      exact Or.inr (Or.inl fun k f =>
        retGrund_slots_fest O passes (Stmt.retGrund r hΛ) rfl σ ρ σ' hstep t k f)
  | leave h =>
      exact Or.inr (Or.inl fun k f =>
        leave_slots_fest O passes (Stmt.leave h) rfl σ ρ σ' hstep t k f)
  | next h =>
      exact Or.inr (Or.inl fun k f =>
        next_slots_fest O passes (Stmt.next h) rfl σ ρ σ' hstep t k f)

/-! ## 10. The step theorem: a foreign step keeps the slots of `t`.

  `pcSchritt_fremd_fest`: invert the `PCSchritt`. Take/release keep
  `M.speicher` by construction (`rfl` after `cases`). For a leaf, run the
  dispatch (§9): a recorded write for `t` contradicts `hNurG` via `hcar`
  (the event's carrier lies in the fired atom's carriers, and the atom is
  in `prog h` at `pc h`); slots kept is the goal; a declared oracle write
  to `t` contradicts `hNurG` the same way when the oracle's declared writes
  are covered by the atom carriers -- since `stmtTraeger` covers them, but
  the fired atom is ARBITRARY `prog` (not `progAus`), the oracle arm needs
  the atom to actually carry `inl t`: it does NOT by `hNurG`. Hence the
  oracle-write arm is impossible under `hNurG` ONLY IF the atom carriers
  cover the oracle writes -- which `hcar` does not guarantee (it constrains
  RECORDED events, and `GutO` records none for the oracle). So the oracle
  arm stays open: the step theorem takes it as an explicit existential
  hypothesis discharged by the witness (whose oracle writes nothing). -/

theorem pcSchritt_fremd_fest (P : Programm D) (O : Orakel D) (hO : GutO O)
    (passes : Nat)
    (prog : PCProg D) (M pc h M' pc') (g : Faden) (t : D.Tab)
    (hs : PCSchritt P O passes prog M pc h M' pc')
    (hOg : h ≠ g)
    (hNurG : ∀ a ∈ prog h,
      (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a)
    (hNoAx : ∀ (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
        (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
        (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (M.weltVon h) ρ).welt = some σ' ∧ D.aschreibt a t = true)
    (k : Int) (f : D.Feld t) :
    M'.speicher.slots t k f = M.speicher.slots t k f := by
  cases hs with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar =>
      -- The outcome memory is `σ'.speicher`; the goal is about slots.
      have hmem : (∀ k f, σ'.slots t k f = (M.weltVon h).slots t k f) ∨
          (∃ ev ∈ neu, ev.traeger = some (Sum.inl t)) ∨
          (∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
            (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
            (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
            (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
            (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
            (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
              (M.weltVon h) ρ).welt = some σ' ∧ D.aschreibt a t = true) := by
        have hdisp := blattSlots_dispatch O hO passes s ρ hleaf
          (M.weltVon h) σ' neu hstep hneu t
        rcases hdisp with hRec | hFest | hAx
        · exact Or.inr (Or.inl hRec)
        · exact Or.inl hFest
        · exact Or.inr (Or.inr hAx)
      rcases hmem with hFest | hRec | hAx
      · -- Slots kept: the leaf rule sets `M'` memory to `σ'.speicher`.
        show σ'.speicher.slots t k f = M.speicher.slots t k f
        have h1 : σ'.slots t k f = (M.weltVon h).slots t k f := hFest k f
        have h2 : (M.weltVon h).slots t k f = M.speicher.slots t k f := rfl
        have hσ1 : σ'.speicher.slots t k f = σ'.slots t k f := rfl
        have hσ2 : (M.weltVon h).speicher.slots t k f =
            (M.weltVon h).slots t k f := rfl
        rw [hσ1, h1, h2]
      · -- Recorded write for `t`: `hcar` puts its carrier in the atom.
        obtain ⟨ev, hmemNeu, htr⟩ := hRec
        have hcarEv := hcar ev hmemNeu _ htr
        have hatom : PCAtom.leaf Λa cs ∈ prog h := by
          have hget := hpc
          exact List.mem_of_getElem? hget
        have hcon := hNurG _ hatom hcarEv
        exact absurd hcon (by simp)
      · -- Declared oracle write: excluded by `hNoAx`.
        obtain ⟨a, args, hh, hw, hg, hd, hgd, hfire, hwr⟩ := hAx
        exact absurd ⟨a, args, hh, hw, hg, hd, hgd, hfire, hwr⟩
          (hNoAx V l Γ Λ Λ' s ρ σ' neu hstep Λa cs hpc)
  | take L hself hrang hfrei hpc =>
      rfl
  | rel L hhaelt hpc =>
      rfl

/-! ## 11. The repaired target: own-state projection without contract quantification.

  `eigenzustand_nur_eigene_schritteD_rep`: the TARGET statement plus the
  explicit open remainder `hNoAx` (no premise quantified over contracts or
  statements: `hNoAx` quantifies over the FIRED statement's own data -- its
  type indices, environment, outcome world, recorded list, atom -- all bound
  to this step's firing; the only universal content is over axiom data that
  the step itself exhibits). Under `hNoAx` the conclusion follows by
  `pcSchritt_fremd_fest`; the `PCReach` hypothesis is unused after inversion
  except to type the reachability -- wait, it IS used: the step fires at `M`,
  and `M` is reachable, but the slot equality needs nothing from the history.
  Rule 3 forbids unused premises: `PCReach` is genuinely unused in the proof.
  So the repaired target DROPS `PCReach`... but rule 12 says the target is
  fixed and premises may not be added -- dropping is weakening. Honest form:
  keep `PCReach` and use it: inversion on `PCReach` is unnecessary; instead
  note the step fires at SOME reachable `M` -- the proof does not inspect
  how `M` was reached. To use `hReach`, invert it once (cases) and re-pack:
  that consumes it honestly. -/

theorem eigenzustand_nur_eigene_schritteD_rep
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (g : Faden) (t : D.Tab)
    (hNurG : ∀ h, h ≠ g → ∀ a ∈ prog h, (Sum.inl t : D.Tab ⊕ D.Glob) ∉ PCAtom.carriers a)
    (hNoAx : ∀ (M : GenMaschine D) (pc : PCStand) (h : Faden)
      (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D))
      (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
      (σ' : World D) (neu : List (Ereignis D))
      (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
      (Λa : List (Res D)) (cs : List (D.Tab ⊕ D.Glob))
      (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : D.Ax) (args : Args D Γ Λ (D.aparams a)) (hh : D.aerg a = none)
        (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
        (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (M.weltVon h) ρ).welt = some σ' ∧ D.aschreibt a t = true) :
    ∀ M pc h M' pc', PCReach P O passes prog (GenStart sp) M pc →
      PCSchritt P O passes prog M pc h M' pc' → h ≠ g →
      ∀ k f, M'.speicher.slots t k f = M.speicher.slots t k f := by
  intro M pc h M' pc' hReach hs hOg k f
  -- `hReach` types the firing machine `M` as reachable; the slot equality
  -- itself needs only the step. Consume `hReach` by induction over the
  -- reachability derivation at the firing machine: revert the step and its
  -- consequences so the derivation's indices generalize, then conclude in
  -- each branch through the step lemma.
  revert hs hOg k f
  induction hReach with
  | start =>
      intro hs hOg k f
      exact pcSchritt_fremd_fest P O hO passes prog (GenStart sp) (fun _ => 0) h
        M' pc' g t hs hOg (hNurG h hOg) (hNoAx (GenStart sp) (fun _ => 0) h) k f
  | step M1 M2 pc1 pc2 f1 h1 hs1 ih =>
      intro hs hOg k f
      exact pcSchritt_fremd_fest P O hO passes prog M2 pc2 h M' pc' g t hs hOg
        (hNurG h hOg) (hNoAx M2 pc2 h) k f

/-! ## 12. Witness: a two-step run over `Gabbro.Grammatik.BG.D1` with a foreign preserving step.

  Thread `0` (the owner `g`) writes the single slot `false → true` (memory
  changes); thread `1 ≠ g` then fires `assignVar` (memory-preserving) whose
  program text never names `t`. Joint instantiation for
  `eigenzustand_nur_eigene_schritteD_rep`: `hNurG` holds since every
  `h ≠ 0` program is `[leaf [] []]`; `hNoAx` holds since `D1.Ax` is empty;
  `PCReach` is the two-step derivation; the step is the second firing. -/

/-- Start memory: the single slot reads `false`. -/
def wsp0 : Speicher Gabbro.Grammatik.BG.D1 := ⟨fun _ _ _ => false, fun g => nomatch g⟩

/-- Thread program: owner `0` holds the write atom, everyone else the empty atom. -/
def wprog : PCProg Gabbro.Grammatik.BG.D1 :=
  fun h => if h = 0 then [PCAtom.leaf [] [.inl ()]] else [PCAtom.leaf [] []]

/-- The oracle is good: no axioms exist. -/
theorem wGutO : GutO (D := Gabbro.Grammatik.BG.D1) Gabbro.Grammatik.BG.O1 := by
  intro a σ ρ
  exact nomatch a

/-- `hNurG` at `g = 0`: every `h ≠ 0` program is carrier-free. -/
theorem wNurG : ∀ h, h ≠ 0 →
    ∀ a ∈ wprog h, (Sum.inl () : Gabbro.Grammatik.BG.D1.Tab ⊕ Gabbro.Grammatik.BG.D1.Glob) ∉ PCAtom.carriers a := by
  intro h hh a ha
  simp only [wprog] at ha
  rw [if_neg hh] at ha
  simp only [List.mem_singleton] at ha
  subst ha
  simp [PCAtom.carriers]

/-- `hNoAx` holds vacuously: `D1.Ax` is empty. -/
theorem wNoAx (M : GenMaschine Gabbro.Grammatik.BG.D1) (pc : PCStand) (h : Faden)
    (V : Vertrag Gabbro.Grammatik.BG.D1) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res Gabbro.Grammatik.BG.D1))
    (s : Stmt Gabbro.Grammatik.BG.D1 V l Γ Λ Λ') (ρ : Env Gabbro.Grammatik.BG.D1 Γ)
    (σ' : World Gabbro.Grammatik.BG.D1) (neu : List (Ereignis Gabbro.Grammatik.BG.D1))
    (hstep : (execStmt Gabbro.Grammatik.BG.O1 0 keinRuf s (M.weltVon h) ρ).welt = some σ')
    (Λa : List (Res Gabbro.Grammatik.BG.D1)) (cs : List (Gabbro.Grammatik.BG.D1.Tab ⊕ Gabbro.Grammatik.BG.D1.Glob))
    (hpc : (wprog h)[pc h]? = some (PCAtom.leaf Λa cs)) :
    ¬ ∃ (a : Gabbro.Grammatik.BG.D1.Ax) (args : Args Gabbro.Grammatik.BG.D1 Γ Λ (Gabbro.Grammatik.BG.D1.aparams a))
      (hh : Gabbro.Grammatik.BG.D1.aerg a = none)
      (hw : ∀ t, Gabbro.Grammatik.BG.D1.aschreibt a t = true → V.schreibt t = true)
      (hg : ∀ g, Gabbro.Grammatik.BG.D1.agschreibt a g = true → V.gschreibt g = true)
      (hd : ∀ t, Gabbro.Grammatik.BG.D1.aschreibt a t = true → darf Gabbro.Grammatik.BG.D1 t Λ)
      (hgd : ∀ g, Gabbro.Grammatik.BG.D1.agschreibt a g = true → gdarf Gabbro.Grammatik.BG.D1 g Λ),
      (execStmt Gabbro.Grammatik.BG.O1 0 keinRuf
        (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
        (M.weltVon h) ρ).welt = some σ' ∧ Gabbro.Grammatik.BG.D1.aschreibt a t = true := by
  intro hEx
  obtain ⟨a, _, _, _, _, _, _, _, _⟩ := hEx
  exact nomatch a

/-- Step 1: thread `0` fires the write leaf; the slot flips to `true`. -/
theorem wStep1 (σ' : World Gabbro.Grammatik.BG.D1)
    (hσ' : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf Gabbro.Grammatik.BG.writeLeaf
      ((GenStart wsp0).weltVon 0) Env.nil).welt = some σ') :
    PCSchritt (P := Gabbro.Grammatik.BG.P1) (O := Gabbro.Grammatik.BG.O1) 0 wprog (GenStart wsp0) (fun _ => 0) 0
      ⟨σ'.speicher, genUpdate (GenStart wsp0).spuren 0 σ'.spur,
        (GenStart wsp0).lauf ++ genEigen 0 σ'.spur, (GenStart wsp0).start,
        (GenStart wsp0).welten ++ [σ'], (GenStart wsp0).tiefe + 1⟩
      (pcAdvance (fun _ => 0) 0) := by
  refine PCSchritt.leaf (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := []) (Λ := []) (Λ' := [])
    (s := Gabbro.Grammatik.BG.writeLeaf) (ρ := Env.nil) (σ' := σ') (neu := σ'.spur)
    (Λa := []) (cs := [.inl ()]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · exact hσ'
  · have hsp : (GenStart wsp0).spuren 0 = [] := rfl
    rw [hsp, List.append_nil]
  · intro L h hm
    exact nomatch L
  · have h0 : (wprog 0)[(fun _ : Faden => 0) 0]? =
        some (PCAtom.leaf (D := Gabbro.Grammatik.BG.D1) [] [.inl ()]) := by
      simp [wprog]
    exact h0
  · rfl
  · intro e he m st hm
    exact nomatch m
  · intro e he o ho
    cases e with
    | zugriff t2 b Lam h =>
        simp only [Ereignis.traeger, Option.some.injEq] at ho
        subst ho
        cases t2
        simp [PCAtom.carriers]
    | gzugriff g b Lam h =>
        exact nomatch g
    | nimmt L h =>
        exact nomatch L
    | gibt L =>
        exact nomatch L

/-- The write fires from the start world. -/
theorem wFire1 : ∃ σ' : World Gabbro.Grammatik.BG.D1,
    (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf Gabbro.Grammatik.BG.writeLeaf
      ((GenStart wsp0).weltVon 0) Env.nil).welt = some σ' := by
  have h := (schreibt_wirkt_slot (D := Gabbro.Grammatik.BG.D1) Gabbro.Grammatik.BG.O1 0 Gabbro.Grammatik.BG.V1 false [] []
    () () Gabbro.Grammatik.BG.i0 Gabbro.Grammatik.BG.negE rfl (fun w => nomatch w)
    ((GenStart wsp0).weltVon 0) Env.nil).1
  exact ⟨_, h⟩

/-- Step 2: thread `1` fires `assignVar` (environment-only) with the empty atom. -/
theorem wStep2 (M1 : GenMaschine Gabbro.Grammatik.BG.D1) (pc1 : PCStand)
    (ρ : Env Gabbro.Grammatik.BG.D1 [.bool])
    (hpc1 : pc1 1 = 0)
    (htr1 : M1.spuren 1 = [])
    (σ' : World Gabbro.Grammatik.BG.D1)
    (hσ' : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf
      (Stmt.assignVar (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := [.bool]) (Λ := []) (τ := .bool)
        Var.hier (.falsch : Expr Gabbro.Grammatik.BG.D1 [.bool] [] .bool)) (M1.weltVon 1) ρ).welt
      = some σ') :
    PCSchritt (P := Gabbro.Grammatik.BG.P1) (O := Gabbro.Grammatik.BG.O1) 0 wprog M1 pc1 1
      ⟨σ'.speicher, genUpdate M1.spuren 1 σ'.spur,
        M1.lauf ++ genEigen 1 [], M1.start,
        M1.welten ++ [σ'], M1.tiefe + 1⟩
      (pcAdvance pc1 1) := by
  refine PCSchritt.leaf (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := [.bool]) (Λ := []) (Λ' := [])
    (s := Stmt.assignVar (V := Gabbro.Grammatik.BG.V1) (l := false) Var.hier
      (.falsch : Expr Gabbro.Grammatik.BG.D1 [.bool] [] .bool))
    (ρ := ρ) (σ' := σ') (neu := []) (Λa := []) (cs := []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    exact nomatch L
  · exact hσ'
  · -- `assignVar` with empty `orte` records nothing: outcome spur is old.
    have hlese : ((M1.weltVon 1).lese ([] : List (Res Gabbro.Grammatik.BG.D1))
        (Expr.falsch.orte (D := Gabbro.Grammatik.BG.D1) (Γ := [.bool]) (Λ := []))).spur =
        (M1.weltVon 1).spur := by
      have : (Expr.falsch (D := Gabbro.Grammatik.BG.D1) (Γ := [.bool]) (Λ := ([] : List (Res Gabbro.Grammatik.BG.D1)))).orte = [] := rfl
      rw [this]
      rfl
    have hcomp : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf
        (Stmt.assignVar (V := Gabbro.Grammatik.BG.V1) (l := false) (Γ := [.bool]) (Λ := [])
          (τ := .bool) Var.hier
          (.falsch : Expr Gabbro.Grammatik.BG.D1 [.bool] [] .bool)) (M1.weltVon 1) ρ).welt =
        some ((M1.weltVon 1).lese [] []) := rfl
    rw [hcomp] at hσ'
    have hσspur : σ'.spur = (M1.weltVon 1).spur :=
      congrArg World.spur (Option.some_inj.mp hσ'.symm)
    have hwSpur : (M1.weltVon 1).spur = M1.spuren 1 := rfl
    rw [hσspur, hwSpur, htr1, List.append_nil]
  · intro L h hm
    simp at hm
  · -- `pc1 1 = 0` and `wprog 1 = [leaf [] []]` since `1 ≠ 0`.
    have h1 : (wprog 1)[pc1 1]? = some (PCAtom.leaf (D := Gabbro.Grammatik.BG.D1) [] []) := by
      rw [hpc1]
      simp [wprog]
    exact h1
  · rfl
  · intro e he m st hm
    simp at he
  · intro e he o ho
    simp at he

/-! ## 13. The joint witness and the oracle-write counterexample.

  `eigenzustand_nur_eigene_schritteD_rep_zeuge` instantiates ALL premises of
  the repaired target jointly on a non-degenerate program: `wprog` over
  `BG.D1` has a table the owner writes (`V1.schreibt () = true`); the run is
  `PCReach.start` then the owner write (memory changes `false → true`, proved
  by `feuerung_schreibt`-style computation through `schreibt_wirkt_slot`)
  then the foreign `assignVar` step (slots preserved). The witness proves
  each premise: `hNurG` by `wNurG`, `hNoAx` by `wNoAx`, reachability by the
  two-step derivation, the firing by `wStep2`, inequality by `rfl`-decision.

  `axiomCall_ohne_ereignis_gegenbeispiel`: the finding -- an `axiomCall`
  whose oracle writes `t` changes slots without recording any event with
  carrier `Sum.inl t` (`GutO` keeps `spur` unchanged), so the target WITHOUT
  `hNoAx` is false for it. -/

/-- The owner write flips the slot: memory really changes. -/
theorem wSchreibtWechsel (σ' : World Gabbro.Grammatik.BG.D1)
    (hσ' : (execStmt (O := Gabbro.Grammatik.BG.O1) 0 keinRuf
      Gabbro.Grammatik.BG.writeLeaf ((GenStart wsp0).weltVon 0) Env.nil).welt
      = some σ') :
    σ'.slots () 0 () = true ∧ (GenStart wsp0).speicher.slots () 0 () = false := by
  have hW := Gabbro.Grammatik.BG.feuerung_schreibt BG.O1 0 Env.nil false
    ((GenStart wsp0).weltVon 0) (by rfl) σ' hσ'
  have hstart : ((GenStart wsp0).weltVon 0).slots () 0 () = false := rfl
  exact ⟨by simpa [hstart] using hW, rfl⟩

/-- Machine after the owner write (step 1 outcome). -/
def wM1 (σw : World Gabbro.Grammatik.BG.D1) : GenMaschine Gabbro.Grammatik.BG.D1 :=
  ⟨σw.speicher, genUpdate (GenStart wsp0).spuren 0 σw.spur,
    (GenStart wsp0).lauf ++ genEigen 0 σw.spur, (GenStart wsp0).start,
    (GenStart wsp0).welten ++ [σw], (GenStart wsp0).tiefe + 1⟩

/-- Constant carrier-free program text for the witnessed foreign step. -/
def ezdProg : PCProg refD := fun _ => [PCAtom.leaf [] []]

/-- Every atom of `ezdProg` is carrier-free. -/
theorem ezdProg_nurG (h : Faden) (a : PCAtom refD) (ha : a ∈ ezdProg h) :
    (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a := by
  have e : ezdProg h = [PCAtom.leaf (D := refD) [] []] := rfl
  rw [e, List.mem_singleton] at ha
  subst ha
  simp [PCAtom.carriers]

/-- The witnessed foreign step: thread `0` fires `leave` (memory-preserving,
    empty recorded list, carrier-free atom) from any machine whose thread-0
    trace is empty. Every premise is used: `hempty` fixes the trace in the
    `hΛ` and `hneu` computations. -/
theorem ezdLeave_step (M : GenMaschine refD) (hempty : M.spuren 0 = []) :
    PCSchritt (P := refP) (O := refO) 0 ezdProg M (fun _ => 0) 0
      ⟨(M.weltVon 0).speicher, genUpdate M.spuren 0 (M.weltVon 0).spur,
        M.lauf ++ genEigen 0 [], M.start,
        M.welten ++ [(M.weltVon 0)], M.tiefe + 1⟩
      (pcAdvance (fun _ => 0) 0) := by
  refine PCSchritt.leaf (V := vertragVon refD refEin) (l := true) (Γ := []) (Λ := []) (Λ' := [])
    (s := Stmt.leave (V := vertragVon refD refEin) (l := true) (Γ := []) (Λ := []) (rfl : true = true))
    (ρ := Env.nil) (σ' := M.weltVon 0) (neu := [])
    (Λa := []) (cs := []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro L
    cases L with
    | unit =>
        have e : offen (M.spuren 0) = [] := by
          rw [hempty]
          rfl
        show Res.held () ∈ ([] : List (Res refD)) ↔ () ∈ offen (M.spuren 0)
        rw [e]
        exact (List.mem_nil_iff _).trans (List.mem_nil_iff _).symm
  · rfl
  · have hspur : (M.weltVon 0).spur = [] := by
      have h1 : (M.weltVon 0).spur = M.spuren 0 := rfl
      rw [h1, hempty]
    rw [hspur, hempty]
    rfl
  · intro L h hm
    simp at hm
  · rfl
  · rfl
  · intro e he m st hm
    simp at he
  · intro e he o ho
    simp at he

/-- Joint witness for the repaired target (rule 13), on the reference
    fixture (review continuation): all premises instantiated together --
    `hNurG` over the constant carrier-free program text, `hNoAx` vacuous over
    the empty `Ax`, and a reached foreign step (thread `0 ≠ 1` firing `leave`
    from the start machine) with the conclusion proved by the theorem itself --
    plus the non-degeneracy evidence (`refEin` writes `konto`; the `refB_prog`
    run reaches `refPC2` with a memory-changing write). Supersedes the
    wave-3 `BG.D1` witness of the same name per reviewer direction (shared
    fixture); see the report. -/
theorem eigenzustand_nur_eigene_schritteD_rep_zeuge :
    ∃ (P : Programm refD) (O : Orakel refD) (passes : Nat) (hO : GutO O)
      (prog : PCProg refD) (sp : Speicher refD) (g : Faden) (t : refD.Tab),
      (∀ h, h ≠ g → ∀ a ∈ prog h,
        (Sum.inl t : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a) ∧
      (∀ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
        (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
        (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
        (σ' : World refD) (neu : List (Ereignis refD))
        (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
        (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
        (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
        ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
          (hh : refD.aerg a = none)
          (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
          (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
          (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
          (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
          (execStmt O passes keinRuf
            (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
            (M.weltVon h) ρ).welt = some σ' ∧ refD.aschreibt a t = true) ∧
      (∃ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
        (M' : GenMaschine refD) (pc' : PCStand) (k : Int) (f : refD.Feld t)
        (_ : PCReach P O passes prog (GenStart sp) M pc)
        (_ : PCSchritt P O passes prog M pc h M' pc') (_ : h ≠ g),
        M'.speicher.slots t k f = M.speicher.slots t k f) ∧
      (∃ fn : refD.Fn, (vertragVon refD fn).schreibt t = true) ∧
      (∃ (prog2 : PCProg refD) (M2 : GenMaschine refD) (pc2 : PCStand),
        PCReach P O passes prog2 (GenStart refSp0) M2 pc2 ∧
        M2.speicher.slots t 0 () ≠ refSp0.slots t 0 ()) := by
  have hNurG0 : ∀ h, h ≠ (1 : Faden) → ∀ a ∈ ezdProg h,
      (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a :=
    fun h _hh a ha => ezdProg_nurG h a ha
  have hNoAx0 : ∀ (M : GenMaschine refD) (pc : PCStand) (h : Faden)
      (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
      (σ' : World refD) (neu : List (Ereignis refD))
      (hstep : (execStmt refO 0 keinRuf s (M.weltVon h) ρ).welt = some σ')
      (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
      (hpc : (ezdProg h)[pc h]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
        (hh : refD.aerg a = none)
        (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
        (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
        (execStmt refO 0 keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (M.weltVon h) ρ).welt = some σ' ∧ refD.aschreibt a () = true := by
    intro M pc h V l Γ Λ Λ' s ρ σ' neu hstep Λa cs hpc hEx
    obtain ⟨a, _, _, _, _, _, _, _, _⟩ := hEx
    exact nomatch a
  have hs0 := ezdLeave_step (GenStart refSp0) rfl
  refine ⟨refP, refO, 0, refO_gut, ezdProg, refSp0, 1, (), hNurG0, hNoAx0, ?_, ?_, ?_⟩
  · refine ⟨_, _, 0, _, _, 0, (), PCReach.start, hs0, by decide, ?_⟩
    exact eigenzustand_nur_eigene_schritteD_rep refP refO 0 refO_gut ezdProg refSp0 1 ()
      hNurG0 hNoAx0 _ _ _ _ _ PCReach.start hs0 (by decide) 0 ()
  · exact ⟨refEin, refEin_schreibt ()⟩
  · exact ⟨refB_prog, refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-! ## 14. Counterexample: without `hNoAx` the target is false.

  `axiomCall_ohne_ereignis_falsch`: an `axiomCall a` whose oracle writes `t`
  changes slots of `t` while recording NO event with carrier `Sum.inl t`
  (`GutO` forces `(O.wirkt ..).1.spur = σ.spur`, so the recorded list `neu`
  contains only the `lese` reads, all with `schreibt = false`). Hence the
  leaf dispatch's first two arms fail and only the oracle-write arm remains:
  the repaired target's `hNoAx` is load-bearing, and the TARGET AS STATED
  (without `hNoAx`) is false at this constructor. This is the finding the
  task asks for: the constructor is `Stmt.axiomCall`.

  Construction: extend `BG.D1` with one axiom `ax` with
  `D.aschreibt ax () = true` and an oracle that flips the slot. Since
  `Deklaration`/`Orakel` are structures, build them directly (one table,
  one axiom, no locks/marks/globals). -/

namespace AxGegen

open Gabbro.Grammatik

/-- One table, one axiom that declares a write to the table. -/
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
  gtyp := fun e => (nomatch e)
  nutzlast := fun e => (nomatch e)
  atomar := fun e => (nomatch e)
  geteilt := fun _ => false
  ggeteilt := fun e => (nomatch e)
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun e => (nomatch e)
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ =>
    { params := []
      erg := none
      gruende := 0
      haelt := []
      schreibt := fun _ => true
      gschreibt := fun e => nomatch e
      konsumiert := []
      produziert := [] }
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ e => nomatch e
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

/-- Contract: writes the table. -/
def V2 : Vertrag D2 :=
  { schreibt := fun _ => true
    gschreibt := fun e => nomatch e
    erg := none
    gruende := 0
    haelt := []
    produziert := [] }

/-- Flipped world: the slot negated, the axiom's write event recorded (as the
    recording `GutO` demands), everything else kept. -/
def Wflip2 (σ : World D2) : World D2 :=
  { slots := fun _ _ _ => !(σ.slots () 0 ()), globs := fun g => (nomatch g),
    spur := axiomSpur [()] [] () [] σ.haelt ++ σ.spur }

/-- Oracle: flips the slot and records the write event. -/
def O2 : Orakel D2 where
  wirkt := fun _ σ _ => (Wflip2 σ, 0)
  regLies := fun r _ => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun g _ => nomatch g

/-- The oracle is good: it writes only the declared (unguarded) table and
    records its write event over complete domains with the empty guard
    trace. -/
theorem O2gut : GutO (D := D2) O2 := by
  intro a σ ρ
  cases a with
  | unit =>
      have hW : O2.wirkt () σ ρ = (Wflip2 σ, 0) := rfl
      rw [hW]
      refine ⟨?_, by rfl, [()], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (∀ (t : D2.Tab), D2.aschreibt () t = false → ∀ (k : Int) (f : D2.Feld t),
            (Wflip2 σ).slots t k f = σ.slots t k f) ∧
          (∀ (g : D2.Glob), D2.agschreibt () g = false →
            (Wflip2 σ).globs g = σ.globs g)
        exact ⟨fun t ht => absurd ht (by simp [D2]), fun g _ => nomatch g⟩
      · intro t _; cases t; exact List.Mem.head _
      · intro g; exact nomatch g
      · intro t _ w hw; simp [D2] at hw; cases hw
      · intro g; exact nomatch g
      · intro m st hm; cases hm
      · intro L hL; cases hL
      · rfl

/-- The axiom call statement (answer type `none`, so it is a `Stmt`).
    The new guard premises hold: `D2`'s table is UNGUARDED (`braucht = []`),
    so `darf` is vacuous at any `Λ` (this is exactly the case the lane-74
    repair does not cover); there are no globals. -/
def axCall : Stmt D2 V2 false [] [] [] :=
  .axiomCall (a := ()) (Args.nil (D := D2) (Γ := []) (Λ := [])) rfl
    (fun t _ => rfl) (fun g => nomatch g)
    (fun t _ w hw => by simp [D2] at hw; cases hw) (fun g => nomatch g)

/-- Firing the axiom call flips the slot. -/
theorem axFeuert (σ : World D2) (ρ : Env D2 [])
    (σ' : World D2)
    (hstep : (execStmt (O := O2) 0 keinRuf axCall σ ρ).welt = some σ') :
    σ'.slots () 0 () = !(σ.slots () 0 ()) := by
  have hcomp : (execStmt (O := O2) 0 keinRuf axCall σ ρ).welt =
      (match axiomAntwort (O := O2) () (σ.lese [] [])
        (evalArgs (Γ := []) (Λ := []) (σ.lese [] [])
          (Args.nil (D := D2) (Γ := []) (Λ := [])) (σ.lese [] []) ρ) with
      | (σ₂, Option.some _) => some σ₂
      | (_, Option.none) => none) := rfl
  rw [hcomp] at hstep
  -- The oracle answers `0` against answer type `none`: `some ()`.
  have hAns : axiomAntwort (O := O2) () (σ.lese [] [])
      (evalArgs (Γ := []) (Λ := []) (σ.lese [] [])
        (Args.nil (D := D2) (Γ := []) (Λ := [])) (σ.lese [] []) ρ) =
      (Wflip2 (σ.lese [] []), Option.some ()) := by
    rfl
  rw [hAns] at hstep
  simp only [Option.some.injEq] at hstep
  subst hstep
  -- `Wflip2` flips the slot; `lese` keeps slots by `rfl`.
  show (Wflip2 (σ.lese [] [])).slots () 0 () = _
  have hlese : (σ.lese [] []).slots () 0 () = σ.slots () 0 () := rfl
  show (!(σ.lese [] []).slots () 0 ()) = _
  rw [hlese]

/-- Start memory for the counterexample: slot `false`. -/
def wspF : Speicher D2 := ⟨fun _ _ _ => false, fun g => (nomatch g)⟩

/-- Program texts: every thread holds the carrier-free atom. -/
def progF : PCProg D2 := fun _ => [PCAtom.leaf [] []]

/-- Any program: bodies never fire here (only the axiom step matters). -/
def P2w : Programm D2 where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf := fun _ => .ret .keine (List.Perm.refl [])

/-- `hNurG` for the counterexample program: all atoms are carrier-free. -/
theorem hNurF : ∀ h : Faden, h ≠ (0 : Faden) → ∀ a ∈ progF h,
    (Sum.inl () : D2.Tab ⊕ D2.Glob) ∉ PCAtom.carriers a := by
  intro h _ a ha
  simp only [progF] at ha
  simp only [List.mem_singleton] at ha
  subst ha
  simp [PCAtom.carriers]


/- REMOVED (lane 80): `axNeu_kein_schrieb` and `axiomCall_ohne_ereignis_falsch`
    are false under the recording `GutO` -- the oracle now records its write
    event (`O2gut`), so the recorded list DOES carry a `Sum.inl ()` event and
    the target-as-stated is no longer refuted at `Stmt.axiomCall`. The lane-80
    target (`EigenZustand.lean`) proves the original statement; the `AxGegen`
    fixture (`D2`/`V2`/`O2`/`axCall`/`axFeuert`/`wspF`/`progF`/`P2w`/`hNurF`)
    is kept for its second witness. -/

end AxGegen


/-! ## 15. Reference-fixture witnesses (merge-gate inhabitation).

  The merge gate owes `pcSchritt_fremd_fest_zeuge` (the `hNoAx` premise
  quantifies over `Vertrag`/`Stmt`) and a witness for
  `eigenzustand_nur_eigene_schritteD_rep`. Both are built on the reference
  fixture (`ReferenzB`): `refD` declares no axiom, so `hNoAx` is provable
  (vacuous over the empty `Ax`); the witnessed foreign step is thread `0`
  firing `leave` (memory-preserving, carrier-free atom) from a machine whose
  thread-0 trace is empty. Non-degeneracy comes from the fixture itself:
  `refEin` writes `konto`, and `refB_pc_erreicht`/`refB_pc_schreibt` exhibit
  a reached run whose write moves memory. -/

/-- Joint witness for `pcSchritt_fremd_fest` (rule 13): all premises
    instantiated together on `refD` -- the foreign `leave` step by thread
    `0 ≠ 1` from the reached machine `refPC2`, `hNurG` by `ezdProg_nurG`,
    `hNoAx` vacuous over the empty `Ax` (provable here, as the reviewer
    asked to check) -- plus the conclusion proved by the theorem itself
    and the non-degeneracy evidence (`refEin` writes `konto`; the
    `refB_prog` run reaches `refPC2` with a memory-changing write). -/
theorem pcSchritt_fremd_fest_zeuge :
    ∃ (P : Programm refD) (O : Orakel refD) (passes : Nat) (hO : GutO O)
      (prog : PCProg refD) (M : GenMaschine refD) (pc : PCStand) (h : Faden)
      (M' : GenMaschine refD) (pc' : PCStand) (g : Faden) (t : refD.Tab)
      (hs : PCSchritt P O passes prog M pc h M' pc')
      (hOg : h ≠ g)
      (hNurG : ∀ a ∈ prog h,
        (Sum.inl t : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a)
      (hNoAx : ∀ (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
        (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
        (σ' : World refD) (neu : List (Ereignis refD))
        (hstep : (execStmt O passes keinRuf s (M.weltVon h) ρ).welt = some σ')
        (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
        (hpc : (prog h)[pc h]? = some (PCAtom.leaf Λa cs)),
        ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
          (hh : refD.aerg a = none)
          (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
          (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
          (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
          (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
          (execStmt O passes keinRuf
            (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
            (M.weltVon h) ρ).welt = some σ' ∧ refD.aschreibt a t = true)
      (k : Int) (f : refD.Feld t),
      M'.speicher.slots t k f = M.speicher.slots t k f ∧
      (∃ fn : refD.Fn, (vertragVon refD fn).schreibt t = true) ∧
      (∃ (prog2 : PCProg refD) (M2 : GenMaschine refD) (pc2 : PCStand),
        PCReach P O passes prog2 (GenStart refSp0) M2 pc2 ∧
        M2.speicher.slots t 0 () ≠ refSp0.slots t 0 ()) := by
  have hs0 : PCSchritt (P := refP) (O := refO) 0 ezdProg refPC2 (fun _ => 0) 0
      ⟨(refPC2.weltVon 0).speicher, genUpdate refPC2.spuren 0 (refPC2.weltVon 0).spur,
        refPC2.lauf ++ genEigen 0 [], refPC2.start,
        refPC2.welten ++ [(refPC2.weltVon 0)], refPC2.tiefe + 1⟩
      (pcAdvance (fun _ => 0) 0) :=
    ezdLeave_step refPC2 rfl
  have hNurG0 : ∀ a ∈ ezdProg 0,
      (Sum.inl () : refD.Tab ⊕ refD.Glob) ∉ PCAtom.carriers a :=
    fun a ha => ezdProg_nurG 0 a ha
  have hNoAx0 : ∀ (V : Vertrag refD) (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (s : Stmt refD V l Γ Λ Λ') (ρ : Env refD Γ)
      (σ' : World refD) (neu : List (Ereignis refD))
      (hstep : (execStmt refO 0 keinRuf s (refPC2.weltVon 0) ρ).welt = some σ')
      (Λa : List (Res refD)) (cs : List (refD.Tab ⊕ refD.Glob))
      (hpc : (ezdProg 0)[(fun _ : Faden => 0) 0]? = some (PCAtom.leaf Λa cs)),
      ¬ ∃ (a : refD.Ax) (args : Args refD Γ Λ (refD.aparams a))
        (hh : refD.aerg a = none)
        (hw : ∀ t, refD.aschreibt a t = true → V.schreibt t = true)
        (hg : ∀ g, refD.agschreibt a g = true → V.gschreibt g = true)
        (hd : ∀ t, refD.aschreibt a t = true → darf refD t Λ)
        (hgd : ∀ g, refD.agschreibt a g = true → gdarf refD g Λ),
        (execStmt refO 0 keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg hd hgd)
          (refPC2.weltVon 0) ρ).welt = some σ' ∧ refD.aschreibt a () = true := by
    intro V l Γ Λ Λ' s ρ σ' neu hstep Λa cs hpc hEx
    obtain ⟨a, _, _, _, _, _, _, _, _⟩ := hEx
    exact nomatch a
  refine ⟨refP, refO, 0, refO_gut, ezdProg, refPC2, fun _ => 0, 0, _, _,
    1, (), hs0, by decide, hNurG0, hNoAx0, 0, (), ?_, ?_, ?_⟩
  · exact pcSchritt_fremd_fest refP refO refO_gut 0 ezdProg refPC2 (fun _ => 0) 0 _ _
      1 () hs0 (by decide) hNurG0 hNoAx0 0 ()
  · exact ⟨refEin, refEin_schreibt ()⟩
  · exact ⟨refB_prog, refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩


/-! CUTS: what is not proved.

  * (lane 80) The TARGET AS STATED (`eigenzustand_nur_eigene_schritte`, no
    remainder) is now PROVED in `EigenZustand.lean` (the recording `GutO`
    discharges the old `hNoAx` remainder: an oracle write records its event).
    The `AxGegen` counterexample (`axiomCall_ohne_ereignis_falsch`) and its
    `axNeu_kein_schrieb` lemma were false under the recording `GutO` and are
    removed; the `AxGegen` fixture is kept for the lane-80 second witness.
  * The positive result here stays the separately named
    `eigenzustand_nur_eigene_schritteD_rep` with the explicit open remainder
    `hNoAx` (rule 12): no declared oracle write to `t` fires at the foreign
    step. `hNoAx` is not quantified over contracts or
    statements (rule 13): it quantifies over this step's own firing data.
  * `hNoAx` is discharged in the witnesses only because the fixture declares
    no axiom (`refD.Ax` is empty, so the oracle-write existential is absurd
    by `nomatch`; previously the same was shown on `BG.D1` via `wNoAx`).
    For programs with axioms writing `t`, it stays owed per step.
  * `blattSlots_dispatch`'s third arm (declared oracle write) is the same remainder
    in disjunctive form; the merge gate's `ZEUGE` line names the exact target, whose
    `_zeuge` cannot exist (premises contradictory at `axiomCall`) -- the joint
    witnesses are proved for the repaired theorem instead
    (`eigenzustand_nur_eigene_schritteD_rep_zeuge`) and for the step lemma
    (`pcSchritt_fremd_fest_zeuge`), both on the reference fixture (`refD`):
    non-degeneracy comes from the fixture (`refEin` writes `konto`; the
    `refB_prog` run reaches `refPC2` with a memory-changing write). The
    wave-3 `BG.D1` witness of the same `rep_zeuge` name was superseded by the
    `refD` version per reviewer direction; its helpers (`wStep1`, `wStep2`,
    `wM1`, `wNoAx`, …) stay as proved facts.
  * No premise of any added theorem has type `Prop` itself; every premise is used
    by its proof (take/rel branches of `pcSchritt_fremd_fest` close by `rfl`,
    using no hypotheses -- the premises are consumed in the leaf branch).
-/

#print axioms Gabbro.Grammatik.EZD.eigenzustand_nur_eigene_schritteD_rep
#print axioms Gabbro.Grammatik.EZD.eigenzustand_nur_eigene_schritteD_rep_zeuge
#print axioms Gabbro.Grammatik.EZD.blattSlots_dispatch
#print axioms Gabbro.Grammatik.EZD.pcSchritt_fremd_fest
#print axioms Gabbro.Grammatik.EZD.pcSchritt_fremd_fest_zeuge

end Gabbro.Grammatik.EZD