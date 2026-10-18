/-
  File:      Grammatik/Gen/Erzeuger/Knoten.lean
  Subject:   The TABLE of the statements, blocks and end blocks of one context by size (`genT`) and its COMPLETENESS
             (`genT_vollst`): every statement, block and end block of size at most `n` (and at most the fuel) is in
             the bucket of its size. The table of a context is built bucket by bucket from the buckets below; the
             contexts the clauses reach into (the rest of a block after a `let`, the body of a lock) are drawn from
             the tables of fuel one less (`Orakel`), so the fuel bounds the nesting and the recursion terminates
             structurally.
-/
import Grammatik.Gen.Erzeuger.BlockVollst

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D] [Zahlen] {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- The statements, blocks and end blocks of one size. -/
abbrev Eimer (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) : Type :=
  List (SS D V l Γ Λ) × List (SB D V l Γ Λ) × List (Endblock D V l Γ Λ)

/-- The statements of a table as a stream. -/
def tabS (t : List (Eimer V l Γ Λ)) : Sz (SS D V l Γ Λ) := fun i => (t.getD i ([], [], [])).1

/-- The blocks of a table as a stream. -/
def tabB (t : List (Eimer V l Γ Λ)) : Sz (SB D V l Γ Λ) := fun i => (t.getD i ([], [], [])).2.1

/-- The end blocks of a table as a stream. -/
def tabN (t : List (Eimer V l Γ Λ)) : Sz (Endblock D V l Γ Λ) := fun i => (t.getD i ([], [], [])).2.2

/-- The blocks of `prev` as the blocks of an equal context. -/
def tabBAls {l l' : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)} (h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ)
    (prev : List (Eimer V l Γ Λ)) : Sz (SB D V l' Γ' Λ') := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact tabB prev

/-- The end blocks of `prev` as the end blocks of an equal context. -/
def tabNAls {l l' : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)} (h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ)
    (prev : List (Eimer V l Γ Λ)) : Sz (Endblock D V l' Γ' Λ') := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact tabN prev

/-- The oracle answers the context at hand from the buckets already built (`prev`) instead of building the table of
    this very context again: a block after a statement that holds the same resources is a block of the same context. -/
def selbst (O : Orakel V) (prev : List (Eimer V l Γ Λ)) : Orakel V where
  ex := O.ex
  bl := fun l' Γ' Λ' m => if h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ then tabBAls h prev else O.bl l' Γ' Λ' m
  en := fun l' Γ' Λ' m => if h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ then tabNAls h prev else O.en l' Γ' Λ' m

/-- One bucket: the statements, blocks and end blocks of size `k`, from the buckets below (`prev`), the expressions
    of the context (`E`) and the oracle for the other contexts. -/
def schritt (O : Orakel V) (E : Sz (SE D Γ Λ)) (prev : List (Eimer V l Γ Λ)) (k : Nat) : Eimer V l Γ Λ :=
  let O' := selbst O prev
  (stmtS O' E (tabB prev) k, blockS O' E (tabS prev) (tabB prev) (tabN prev) k, endS O' E (tabS prev) k)

/-- The buckets `0 .. n` of a context for a given oracle and expression stream. -/
def tabT {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (O : Orakel V) (E : Sz (SE D Γ Λ)) (n : Nat) :
    List (Eimer V l Γ Λ) :=
  buckets ([], [], []) (fun prev k => schritt O E prev k) n

/-! ## Sharing the tables of the child contexts of one node

  A node asks for the table of a child context (the rest of a block after a `let`: the context extended by the
  type of the bound expression) again for every size of the first part and every step. The node therefore builds
  each child table ONCE, lazily (`Thunk`: evaluated at the first request, never if it is not asked for), for the
  largest bound the node can ask it for, and answers every request that bound covers from it. A request the cache
  does not cover falls back to building the table, so the cache only saves work and every answer is the same table
  of the same function. -/

/-- A cached table of one context, built lazily for a bound. -/
structure CEintrag (V : Vertrag D) where
  l : Bool
  Γ : Ctx
  Λ : List (Res D)
  n : Nat
  t : Thunk (List (Eimer V l Γ Λ))

/-- The key of a cached table: flag, context, resources, bound. -/
abbrev Schl (D : Deklaration) : Type := Bool × Ctx × List (Res D) × Nat

/-- The lazily built table of a key, from the function that builds a table (`gen`). -/
def CEintrag.neu (V : Vertrag D)
    (gen : Nat → (l : Bool) → (Γ : Ctx) → (Λ : List (Res D)) → List (Eimer V l Γ Λ)) (k : Schl D) : CEintrag V :=
  ⟨k.1, k.2.1, k.2.2.1, k.2.2.2, Thunk.mk fun _ => gen k.2.2.2 k.1 k.2.1 k.2.2.1⟩

/-- A table of one context as a table of an equal context. -/
def castTab {l l' : Bool} {Γ Γ' : Ctx} {Λ Λ' : List (Res D)} (h : l = l' ∧ Γ = Γ' ∧ Λ = Λ')
    (t : List (Eimer V l Γ Λ)) : List (Eimer V l' Γ' Λ') := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact t

/-- The cached table of a context whose bound covers `m`, if there is one. -/
def finde (cs : List (CEintrag V)) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (m : Nat) :
    Option (List (Eimer V l Γ Λ)) :=
  cs.findSome? fun c =>
    if h : c.l = l ∧ c.Γ = Γ ∧ c.Λ = Λ then (if m ≤ c.n then some (castTab h c.t.get) else none) else none

/-- The table of a context: from the cache if it covers the request, else built. -/
def findeOder (cs : List (CEintrag V)) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (m : Nat)
    (dflt : Unit → List (Eimer V l Γ Λ)) : List (Eimer V l Γ Λ) :=
  match finde cs l Γ Λ m with
  | some t => t
  | none => dflt ()

/-- The oracle of a node: the expressions are built, the blocks and end blocks come from the cache or are built. -/
def orakelC (V : Vertrag D)
    (gen : Nat → (l : Bool) → (Γ : Ctx) → (Λ : List (Res D)) → List (Eimer V l Γ Λ)) (cs : List (CEintrag V)) :
    Orakel V where
  ex := fun Γ' Λ' m => tab (genE m m Γ' Λ')
  bl := fun l' Γ' Λ' m => tabB (findeOder cs l' Γ' Λ' m fun _ => gen m l' Γ' Λ')
  en := fun l' Γ' Λ' m => tabN (findeOder cs l' Γ' Λ' m fun _ => gen m l' Γ' Λ')

/-- The types of the expressions of a table with the size at which each first occurs. -/
def typenErstAux {Γ : Ctx} {Λ : List (Res D)} : Nat → List (List (SE D Γ Λ)) → List Ty → List (Nat × Ty)
  | _, [], _ => []
  | i, b :: bs, seen =>
    let neu := (schluessel (fun p => p.1) b).filter fun τ => τ ∉ seen
    neu.map (fun τ => (i, τ)) ++ typenErstAux (i + 1) bs (seen ++ neu)

/-- The keys of the child tables a node with bound `n` can ask for: the context extended by the type of a bound
    expression (also the index of an optional one), the bodies of loops and locks. -/
def knotenKeys (n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (Et : List (List (SE D Γ Λ))) : List (Schl D) :=
  ((typenErstAux 0 Et []).flatMap fun p =>
    (l, p.2 :: Γ, Λ, n - 1 - p.1) ::
    (match p.2 with
      | .opt m => [(l, Ty.index m :: Γ, Λ, n - 1 - p.1)]
      | _ => [])) ++
  (Aufz.tab.map fun t => (true, Ty.index (D.count t) :: Γ, Λ, n - 2)) ++
  [(true, Γ, Λ, n - 2)] ++
  (Aufz.lock.map fun L => (l, Γ, Res.held L :: Λ, n - 1))

/-- **The table of a context by size**: the buckets `0 .. n`, by fuel. -/
def genT (V : Vertrag D) : Nat → Nat → (l : Bool) → (Γ : Ctx) → (Λ : List (Res D)) → List (Eimer V l Γ Λ)
  | _, 0, _, _, _ => [([], [], [])]
  | 0, n + 1, _, _, _ => List.replicate (n + 2) ([], [], [])
  | f + 1, n + 1, l, Γ, Λ =>
    let Et := genE (n + 1) (n + 1) Γ Λ
    let gen := fun m l' Γ' Λ' => genT V f m l' Γ' Λ'
    tabT (orakelC V gen ((knotenKeys (n + 1) l Γ Λ Et).map (CEintrag.neu V gen))) (tab Et) (n + 1)

theorem groesseStmt_pos {Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : 1 ≤ groesseStmt s := by
  cases s <;> simp only [groesseStmt] <;> omega

theorem groesseBlock_pos {Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : 1 ≤ groesseBlock b := by
  cases b <;> simp only [groesseBlock] <;> omega

theorem groesseEnd_pos (e : Endblock D V l Γ Λ) : 1 ≤ groesseEnd e := by
  cases e <;> simp only [groesseEnd] <;> omega

/-- The three completeness statements for one context and one table. -/
def TVoll (V : Vertrag D) (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (f n : Nat) (t : List (Eimer V l Γ Λ)) : Prop :=
  (∀ (Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'), groesseStmt s ≤ n → groesseStmt s ≤ f →
    groesseStmt s < unendlich → (⟨Λ', s⟩ : SS D V l Γ Λ) ∈ tabS t (groesseStmt s)) ∧
  (∀ (Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b ≤ n → groesseBlock b ≤ f →
    groesseBlock b < unendlich → (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ tabB t (groesseBlock b)) ∧
  (∀ (e : Endblock D V l Γ Λ), groesseEnd e ≤ n → groesseEnd e ≤ f → groesseEnd e < unendlich →
    e ∈ tabN t (groesseEnd e))

/-- The oracle that answers the context at hand from `prev` is complete below `n + 1` when the oracle is and `prev` is
    complete up to `n`. -/
theorem ounter_selbst (O : Orakel V) (prev : List (Eimer V l Γ Λ)) (f n : Nat) (hP : TVoll V l Γ Λ f n prev)
    (hO : OUnter O (n + 1)) (hf : n + 1 ≤ f) (hu : n + 1 < unendlich) : OUnter (selbst O prev) (n + 1) := by
  obtain ⟨hPS, hPB, hPN⟩ := hP
  refine ⟨fun m Γ' Λ' τ e hlt hle => hO.ex m Γ' Λ' τ e hlt hle,
    fun m l' Γ' Λ' Λ'' b hlt hle => ?_, fun m l' Γ' Λ' e hlt hle => ?_⟩
  · unfold selbst
    dsimp only
    by_cases h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ
    · rw [dif_pos h]
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hPB Λ'' b (by omega) (by omega) (by omega)
    · rw [dif_neg h]
      exact hO.bl m l' Γ' Λ' Λ'' b hlt hle
  · unfold selbst
    dsimp only
    by_cases h : l' = l ∧ Γ' = Γ ∧ Λ' = Λ
    · rw [dif_pos h]
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hPN e (by omega) (by omega) (by omega)
    · rw [dif_neg h]
      exact hO.en m l' Γ' Λ' e hlt hle

/-- **One step of completeness**: if the buckets below (`prev`, complete up to size `n`), the expressions and the
    oracle (complete below `n + 1`) are complete, then every statement, block and end block of size `n + 1` is in the
    bucket `schritt` builds. -/
theorem schritt_vollst (O : Orakel V) (E : Sz (SE D Γ Λ)) (prev : List (Eimer V l Γ Λ)) (f n : Nat)
    (hP : TVoll V l Γ Λ f n prev)
    (hE : ∀ (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e ≤ n → groesseExpr e < unendlich →
      (⟨τ, e⟩ : SE D Γ Λ) ∈ E (groesseExpr e))
    (hO : OUnter O (n + 1)) (hf : n + 1 ≤ f) (hu : n + 1 < unendlich) :
    (∀ (Λ' : List (Res D)) (s : Stmt D V l Γ Λ Λ'), groesseStmt s = n + 1 →
        (⟨Λ', s⟩ : SS D V l Γ Λ) ∈ (schritt O E prev (n + 1)).1) ∧
    (∀ (Λ' : List (Res D)) (b : Block D V l Γ Λ Λ'), groesseBlock b = n + 1 →
        (⟨Λ', b⟩ : SB D V l Γ Λ) ∈ (schritt O E prev (n + 1)).2.1) ∧
    (∀ (e : Endblock D V l Γ Λ), groesseEnd e = n + 1 → e ∈ (schritt O E prev (n + 1)).2.2) := by
  obtain ⟨hPS, hPB, hPN⟩ := hP
  have hEu : Unter E (n + 1) := fun τ e hlt => hE τ e (by omega) (by omega)
  have hS : SUnter (tabS prev) (n + 1) := fun Λ' s hlt => hPS Λ' s (by omega) (by omega) (by omega)
  have hB : BUnter (tabB prev) (n + 1) := fun Λ' b hlt => hPB Λ' b (by omega) (by omega) (by omega)
  have hN : NUnter (tabN prev) (n + 1) := fun e hlt => hPN e (by omega) (by omega) (by omega)
  have hO' := ounter_selbst O prev f n ⟨hPS, hPB, hPN⟩ hO hf hu
  refine ⟨fun Λ' s hs => ?_, fun Λ' b hb => ?_, fun e he => ?_⟩
  · have := stmtS_vollst (selbst O prev) E (tabB prev) s (by omega) (by rw [hs]; exact hEu) (by rw [hs]; exact hB)
      (by rw [hs]; exact hO')
    rw [hs] at this
    exact this
  · have := blockS_vollst (selbst O prev) E (tabS prev) (tabB prev) (tabN prev) b (by omega) (by rw [hb]; exact hEu)
      (by rw [hb]; exact hS) (by rw [hb]; exact hB) (by rw [hb]; exact hN) (by rw [hb]; exact hO')
    rw [hb] at this
    exact this
  · have := endS_vollst (selbst O prev) E (tabS prev) e (by omega) (by rw [he]; exact hEu) (by rw [he]; exact hS)
      (by rw [he]; exact hO')
    rw [he] at this
    exact this

theorem TVoll.mono {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {f n m : Nat}
    {t : List (Eimer V l Γ Λ)} (h : TVoll V l Γ Λ f n t) (hm : m ≤ n) : TVoll V l Γ Λ f m t :=
  ⟨fun Λ' s h1 h2 h3 => h.1 Λ' s (by omega) h2 h3, fun Λ' b h1 h2 h3 => h.2.1 Λ' b (by omega) h2 h3,
    fun e h1 h2 h3 => h.2.2 e (by omega) h2 h3⟩

/-- A request the cache answers is answered by a table of the function `gen`, built for a bound that covers it. -/
theorem findeOder_vollst (V : Vertrag D)
    (gen : Nat → (l : Bool) → (Γ : Ctx) → (Λ : List (Res D)) → List (Eimer V l Γ Λ)) (f : Nat)
    (hgen : ∀ n l Γ Λ, TVoll V l Γ Λ f n (gen n l Γ Λ)) (keys : List (Schl D)) (l : Bool) (Γ : Ctx)
    (Λ : List (Res D)) (m : Nat) :
    TVoll V l Γ Λ f m (findeOder (keys.map (CEintrag.neu V gen)) l Γ Λ m fun _ => gen m l Γ Λ) := by
  unfold findeOder
  cases hf : finde (keys.map (CEintrag.neu V gen)) l Γ Λ m with
  | none => exact hgen m l Γ Λ
  | some t =>
    unfold finde at hf
    obtain ⟨l₁, c, l₂, hc, hfc, _⟩ := List.findSome?_eq_some_iff.1 hf
    have hmem : c ∈ keys.map (CEintrag.neu V gen) := by
      rw [hc]; simp
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hmem
    by_cases h : (CEintrag.neu V gen k).l = l ∧ (CEintrag.neu V gen k).Γ = Γ ∧ (CEintrag.neu V gen k).Λ = Λ
    · rw [dif_pos h] at hfc
      by_cases hm : m ≤ (CEintrag.neu V gen k).n
      · rw [if_pos hm] at hfc
        have ht := Option.some.inj hfc
        rw [← ht]
        obtain ⟨h1, h2, h3⟩ := h
        obtain ⟨kl, kΓ, kΛ, kn⟩ := k
        simp only [CEintrag.neu] at h1 h2 h3 hm ⊢
        subst h1 h2 h3
        exact (hgen kn kl kΓ kΛ).mono hm
      · rw [if_neg hm] at hfc
        cases hfc
    · rw [dif_neg h] at hfc
      cases hfc

/-- The oracle of a node with the cache is complete below `K` when the function `gen` is complete for the fuel
    one below. -/
theorem ounter_orakelC (V : Vertrag D)
    (gen : Nat → (l : Bool) → (Γ : Ctx) → (Λ : List (Res D)) → List (Eimer V l Γ Λ)) (f : Nat)
    (hgen : ∀ n l Γ Λ, TVoll V l Γ Λ f n (gen n l Γ Λ)) (keys : List (Schl D)) (K : Nat) (hK : K ≤ f + 1)
    (hKu : K ≤ unendlich) : OUnter (orakelC V gen (keys.map (CEintrag.neu V gen))) K := by
  refine ⟨fun m Γ' Λ' τ e hlt hle => ?_, fun m l' Γ' Λ' Λ'' b hlt hle => ?_,
    fun m l' Γ' Λ' e hlt hle => ?_⟩
  · exact genE_vollst m m Γ' Λ' τ e hle hle (by omega)
  · exact (findeOder_vollst V gen f hgen keys l' Γ' Λ' m).2.1 Λ'' b hle (by omega) (by omega)
  · exact (findeOder_vollst V gen f hgen keys l' Γ' Λ' m).2.2 e hle (by omega) (by omega)

set_option maxHeartbeats 8000000 in
/-- **Completeness of the table**: every statement, block and end block of size at most `n` and at most the fuel is in
    the bucket of its size. -/
theorem genT_vollst (V : Vertrag D) : ∀ (f n : Nat) (l : Bool) (Γ : Ctx) (Λ : List (Res D)),
    TVoll V l Γ Λ f n (genT V f n l Γ Λ) := by
  intro f
  induction f with
  | zero =>
    intro n l Γ Λ
    refine ⟨fun Λ' s _ hf _ => ?_, fun Λ' b _ hf _ => ?_, fun e _ hf _ => ?_⟩
    · have := groesseStmt_pos s; omega
    · have := groesseBlock_pos b; omega
    · have := groesseEnd_pos e; omega
  | succ f ih =>
    intro nmax' l Γ Λ
    rcases nmax' with _ | nmax
    · show TVoll V l Γ Λ (f + 1) 0 [([], [], [])]
      refine ⟨fun Λ' s hle _ _ => ?_, fun Λ' b hle _ _ => ?_, fun e hle _ _ => ?_⟩
      · have := groesseStmt_pos s; omega
      · have := groesseBlock_pos b; omega
      · have := groesseEnd_pos e; omega
    · let Et := genE (nmax + 1) (nmax + 1) Γ Λ
      let gen := fun m l' Γ' Λ' => genT V f m l' Γ' Λ'
      let O := orakelC V gen ((knotenKeys (nmax + 1) l Γ Λ Et).map (CEintrag.neu V gen))
      let E : Sz (SE D Γ Λ) := tab Et
      have hgen : genT V (f + 1) (nmax + 1) l Γ Λ = tabT O E (nmax + 1) := rfl
      rw [hgen]
      have hOU : ∀ K, K ≤ f + 1 → K ≤ unendlich → OUnter O K := fun K hK hKu =>
        ounter_orakelC V gen f ih _ K hK hKu
      have hEv : ∀ (τ : Ty) (e : Expr D Γ Λ τ), groesseExpr e ≤ nmax + 1 → groesseExpr e < unendlich →
          (⟨τ, e⟩ : SE D Γ Λ) ∈ E (groesseExpr e) :=
        fun τ e hle hu => genE_vollst (nmax + 1) (nmax + 1) Γ Λ τ e hle hle hu
      have key : ∀ n, n ≤ nmax + 1 → TVoll V l Γ Λ (f + 1) n (tabT O E n) := by
        intro n
        induction n with
        | zero =>
          intro _
          refine ⟨fun Λ' s hle _ _ => ?_, fun Λ' b hle _ _ => ?_, fun e hle _ _ => ?_⟩
          · have := groesseStmt_pos s; omega
          · have := groesseBlock_pos b; omega
          · have := groesseEnd_pos e; omega
        | succ n ihn =>
          intro hn
          have ih' := ihn (by omega)
          have hsc := schritt_vollst O E (tabT O E n) (f + 1) n ih'
            (fun τ e h1 h2 => hEv τ e (by omega) h2)
          refine ⟨fun Λ' s hle hf hu => ?_, fun Λ' b hle hf hu => ?_, fun e hle hf hu => ?_⟩
          · by_cases hlt : groesseStmt s ≤ n
            · have : tabS (tabT (l := l) O E (n + 1)) (groesseStmt s) =
                  tabS (tabT (l := l) O E n) (groesseStmt s) := by
                unfold tabS tabT; rw [getD_buckets_alt _ _ _ hlt]
              rw [this]
              exact ih'.1 Λ' s hlt hf hu
            · have heq : groesseStmt s = n + 1 := by omega
              have := (hsc (hOU (n + 1) (by omega) (by omega)) (by omega) (by omega)).1 Λ' s heq
              unfold tabS tabT
              rw [heq, getD_buckets_neu]
              exact this
          · by_cases hlt : groesseBlock b ≤ n
            · have : tabB (tabT (l := l) O E (n + 1)) (groesseBlock b) =
                  tabB (tabT (l := l) O E n) (groesseBlock b) := by
                unfold tabB tabT; rw [getD_buckets_alt _ _ _ hlt]
              rw [this]
              exact ih'.2.1 Λ' b hlt hf hu
            · have heq : groesseBlock b = n + 1 := by omega
              have := (hsc (hOU (n + 1) (by omega) (by omega)) (by omega) (by omega)).2.1 Λ' b heq
              unfold tabB tabT
              rw [heq, getD_buckets_neu]
              exact this
          · by_cases hlt : groesseEnd e ≤ n
            · have : tabN (tabT (l := l) O E (n + 1)) (groesseEnd e) =
                  tabN (tabT (l := l) O E n) (groesseEnd e) := by
                unfold tabN tabT; rw [getD_buckets_alt _ _ _ hlt]
              rw [this]
              exact ih'.2.2 e hlt hf hu
            · have heq : groesseEnd e = n + 1 := by omega
              have := (hsc (hOU (n + 1) (by omega) (by omega)) (by omega) (by omega)).2.2 e heq
              unfold tabN tabT
              rw [heq, getD_buckets_neu]
              exact this
      exact key (nmax + 1) (Nat.le_refl _)

end Gabbro.Grammatik.Gen
