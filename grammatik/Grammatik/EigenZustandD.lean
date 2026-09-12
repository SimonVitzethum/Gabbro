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
    (s : Stmt D V l Γ Λ Λ)
    (hs : s = Stmt.axiomCall (V := V) a args h hw hg)
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
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg) σ ρ).welt =
              some fst := by
            have hrfl : (execStmt O passes keinRuf
                (Stmt.axiomCall (V := V) (l := l) a args h hw hg) σ ρ).welt =
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
              (Stmt.axiomCall (V := V) (l := l) a args h hw hg) σ ρ).welt =
              (Ausgang.hardware (D := D) (.annahme a) : Ausgang V l Γ).welt := by
            have hrfl : (execStmt O passes keinRuf
                (Stmt.axiomCall (V := V) (l := l) a args h hw hg) σ ρ).welt =
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
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args h hw hg) σ ρ).welt =
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
  | axiomCall a args h hw hg =>
      by_cases ht : D.aschreibt a t = true
      · exact Or.inr (Or.inr ⟨a, args, h, hw, hg, hstep, ht⟩)
      · have htF : D.aschreibt a t = false := by
          cases hT : D.aschreibt a t with
          | true => exact absurd hT (by simp [ht])
          | false => rfl
        exact Or.inr (Or.inl fun k f =>
          axiomCall_nichtschreibt_fest (Λ' := Λ) O hO passes (Stmt.axiomCall (V := V) (l := l) a args h hw hg) rfl t htF σ ρ σ' hstep k f)
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
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg)
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
            (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true),
            (execStmt O passes keinRuf
              (Stmt.axiomCall (V := V) (l := l) a args hh hw hg)
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
        obtain ⟨a, args, hh, hw, hg, hfire, hwr⟩ := hAx
        exact absurd ⟨a, args, hh, hw, hg, hfire, hwr⟩
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
        (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true),
        (execStmt O passes keinRuf
          (Stmt.axiomCall (V := V) (l := l) a args hh hw hg)
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

end Gabbro.Grammatik.EZD
