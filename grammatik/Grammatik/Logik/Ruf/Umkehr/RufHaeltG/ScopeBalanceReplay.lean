module

public import Grammatik.Logik.Ruf.Umkehr.RufHaeltG.ScopeBalance
import Aesop

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Keep arbitrary residues folded so that frame equations rewrite the
    entire sigma before its dependent projections are reduced. -/
private theorem restScopeBalance_mk {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (ρ : Env D Γ) (r : GRest D V l Γ Λ) :
    RestScopeBalance ⟨l, Γ, Λ, ρ, r⟩ ↔ r.scopeChain := Iff.rfl

private theorem cons_cons_ne_self {α : Type} (a b : α) (xs : List α) :
    a :: b :: xs ≠ xs := by
  intro he
  have hn := congrArg List.length he
  simp only [List.length_cons] at hn
  omega

private theorem heldCountEq_refl (Λ : List (Res D)) : HeldCountEq Λ Λ := fun _ => rfl

private theorem heldCountEq_symm {Λ Λ' : List (Res D)}
    (h : HeldCountEq Λ Λ') : HeldCountEq Λ' Λ := fun L => (h L).symm

/-- Forward closure uses two existing witnesses; backward application would
    invent an intermediate resource list and recursively search for it. -/
private theorem heldCountEq_trans {Λ Λ' Λ'' : List (Res D)}
    (h : HeldCountEq Λ Λ') (h' : HeldCountEq Λ' Λ'') : HeldCountEq Λ Λ'' :=
  fun L => (h L).trans (h' L)

private theorem heldCountEq_block {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : HeldCountEq Λ' Λ :=
  fun L => block_heldCount L b

private theorem heldCountEq_alsBlock {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ) : HeldCountEq e.alsBlock.1 Λ :=
  heldCountEq_block e.alsBlock.2

private theorem heldCountEq_stmt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : HeldCountEq Λ' Λ :=
  fun L => stmt_heldCount L s

private theorem heldCountEq_nach (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ : List (Res D)) : HeldCountEq (nachSig D S Λ) Λ :=
  fun L => count_held_nachSig S Λ L

private theorem heldCountEq_nach_left (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ Λ' : List (Res D)) : HeldCountEq (nachSig D S Λ) Λ' ↔ HeldCountEq Λ Λ' := by
  simp only [HeldCountEq, count_held_nachSig]

private theorem heldCountEq_nach_right (S : Signatur D.Tab D.Glob D.Lock D.Marke)
    (Λ Λ' : List (Res D)) : HeldCountEq Λ (nachSig D S Λ') ↔ HeldCountEq Λ Λ' := by
  simp only [HeldCountEq, count_held_nachSig]

private theorem scopeChain_weiterOpt {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (e : Option Ty) (k : GRest D V l Γ Λ') :
    (GRest.weiterOpt (Λ := Λ) e k).scopeChain ↔ k.scopeChain := by
  cases e <;> exact Iff.rfl

private theorem antwortRestG_scopeChain {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (c c' : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (hc : RestScopeBalance c) (ha : antwortRestG g a c = some c') :
    RestScopeBalance c' := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := c
  cases a with
  | inl v =>
      cases r with
      | wartet b k | wartetSonst _ _ b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            exact hc
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst c'
          exact hc
  | inr grund =>
      cases r with
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst c'
            refine ⟨?_, hc⟩
            exact heldCountEq_trans (heldCountEq_block err.alsBlock.2)
              (fun L => (block_heldCount L b).symm)
          · cases ha
      | _ => simp only [antwortRestG, reduceCtorEq] at ha

private theorem rufAntwortG_scopeChain {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (hz : FadenScopeBalanceG z) (ha : rufAntwortG z vor σ a = some z') :
    FadenScopeBalanceG z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact ⟨trivial, by simp⟩
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨antwortRestG_scopeChain _ _ _ _ (hz.2 c (by simp [hst])) hr, ?_⟩
      intro F hF
      exact hz.2 F (by simp only [hst, List.mem_cons]; exact Or.inr hF)

/-- Frame-local preservation under the three stack movements. This lets a
    cost segment ignore arbitrary suspended callers below its entry. -/
structure ScopeBalanceMove (z z' : RufFadenG D) : Prop where
  same : z'.stapel = z.stapel → RestScopeBalance z.kopf.rest → RestScopeBalance z'.kopf.rest
  push : ∀ c, z'.stapel = c :: z.stapel → RestScopeBalance z.kopf.rest → RestScopeBalance c.rest
  pop : ∀ c st, z.stapel = c :: st → z'.stapel = st →
    RestScopeBalance c.rest → RestScopeBalance z'.kopf.rest

private theorem rufAntwortG_scopeMove {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') : ScopeBalanceMove z z' := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      refine ⟨fun _ _ => trivial, ?_, ?_⟩ <;> simp [hst]
  | cons c st =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a c.rest = some r := by
        cases hr : antwortRestG z.kopf.f a c.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      refine ⟨?_, ?_, ?_⟩
      · intro he _
        have := congrArg List.length he
        simp only [hst, List.length_cons] at this
        omega
      · intro c' he _
        have := congrArg List.length he
        simp only [hst, List.length_cons] at this
        omega
      · intro c' st' he _ hc
        rw [hst] at he
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        exact antwortRestG_scopeChain _ _ _ _ hc hr

set_option maxHeartbeats 4000000 in
/-- G preserves scope provenance separately for each surviving frame. -/
theorem rufSchrittG_scopeMove {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M') :
    ScopeBalanceMove (M.faeden t) (M'.faeden t) := by
  cases hs with
  | g7 hs =>
      cases hs with
      | rueckFreigabeLetzte _ _ _ _ z ha
      | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z ha
      | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z ha =>
          simp only [rufUpdateG_self]
          exact rufAntwortG_scopeMove ha
      | _ =>
          simp only [rufUpdateG_self]
          constructor <;>
            simp_all [restScopeBalance_mk, GRest.scopeChain, cons_cons_ne_self]
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;> simp only [rufUpdateG_self] <;> constructor <;>
        simp_all [restScopeBalance_mk, GRest.scopeChain, scopeChain_weiterOpt,
          GRest.scopeChain_eintritt (P := P), RufWartetHeadG, cons_cons_ne_self, nach,
          heldCountEq_nach_left, heldCountEq_nach_right]
      all_goals aesop (add norm simp restScopeBalance_mk,
        norm simp GRest.scopeChain, norm simp scopeChain_weiterOpt,
        norm simp heldCountEq_nach_left, norm simp heldCountEq_nach_right,
        safe forward (immediate := [b]) heldCountEq_block,
        safe forward (immediate := [s]) heldCountEq_stmt,
        safe forward (immediate := [e]) heldCountEq_alsBlock,
        safe forward (immediate := [h]) heldCountEq_symm,
        safe forward (immediate := [h, h']) heldCountEq_trans,
        safe apply heldCountEq_refl) (config := { maxRuleApplications := 500, terminal := true })

set_option maxHeartbeats 4000000 in
/-- Counted scope provenance is preserved by G, independently of memory,
    oracle answers, and the checker's separate rank/floor scope facts. -/
theorem fadenScopeBalanceG_schritt {P : Programm D} {O : Orakel D} {pa : Nat}
    {M M' : RufMaschineG D} {t : Faden} (hs : RufSchrittG P O pa M t M')
    (h : FadenScopeBalanceG (M.faeden t)) : FadenScopeBalanceG (M'.faeden t) := by
  obtain ⟨hk, hst⟩ := h
  cases hs with
  | g7 hs =>
      cases hs with
      | rueckFreigabeLetzte _ _ _ _ z ha
      | rueckScopedWertDirekt _ _ _ _ _ _ _ _ _ _ _ _ _ z ha
      | rueckScopedGrundDirekt _ _ _ _ _ _ _ _ _ z ha =>
          simp only [rufUpdateG_self]
          exact rufAntwortG_scopeChain ⟨hk, hst⟩ ha
      | _ =>
          simp only [rufUpdateG_self]
          simp_all [FadenScopeBalanceG, restScopeBalance_mk, GRest.scopeChain]
  | g1 hs | g2 hs | g3 hs | g4 hs | g5 hs | g6 hs =>
      cases hs <;> simp only [rufUpdateG_self] <;>
        simp_all [FadenScopeBalanceG, restScopeBalance_mk, GRest.scopeChain,
          scopeChain_weiterOpt, GRest.scopeChain_eintritt (P := P), RufWartetHeadG, cons_cons_ne_self,
          nach, heldCountEq_nach_left, heldCountEq_nach_right]
      all_goals aesop (add norm simp restScopeBalance_mk,
        norm simp GRest.scopeChain, norm simp scopeChain_weiterOpt,
        norm simp heldCountEq_nach_left, norm simp heldCountEq_nach_right,
        safe forward (immediate := [b]) heldCountEq_block,
        safe forward (immediate := [s]) heldCountEq_stmt,
        safe forward (immediate := [e]) heldCountEq_alsBlock,
        safe forward (immediate := [h]) heldCountEq_symm,
        safe forward (immediate := [h, h']) heldCountEq_trans,
        safe apply heldCountEq_refl) (config := { maxRuleApplications := 500, terminal := true })

/-- The initial residue has no local acquisitions or pending releases. -/
theorem fadenScopeBalanceG_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    FadenScopeBalanceG ((RufStartG P sp init).faeden t) := by
  dsimp only [RufStartG]
  cases init t with
  | mk g rho => exact ⟨GRest.scopeChain_eintritt (P := P) g, by simp⟩

/-- No new acceptance or goal premise: typed frame entry and preservation
    supply balance at every reachable thread. -/
theorem fadenScopeBalanceG_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat}
    {sp : Speicher D} {init : Faden → Σ f : D.Fn, Env D (D.params f)}
    {M : RufMaschineG D} (hr : RufErreichbarG P O pa (RufStartG P sp init) M) :
    ∀ t, FadenScopeBalanceG (M.faeden t) := by
  induction hr with
  | start => exact fadenScopeBalanceG_start P sp init
  | schritt N N' u hn hs ih =>
      intro t
      by_cases htu : t = u
      · subst t
        exact fadenScopeBalanceG_schritt hs (ih u)
      · rw [rufSchrittG_passt_anders P O pa N N' u t htu hs]
        exact ih t

end Gabbro.Grammatik
