/-
  File:      Grammatik/Zielsatz/AtomarAkzeptiertZeuge.lean
  Subject:   THE WITNESSES of the checker side of the atomic rely (Opus lane O25b, 2026-09-26),
             on the noninterference fixture (`NIZeuge`: globals `konfig`, `zaehler` are `atomic`,
             tables `tabA`, `tabB` plain).

  * POSITIVE, the FLAG (`n1_ziel_atomar`): configuration 1 -- `kern` publishes the atomic
    `konfig`, `hauptA`/`hauptB` read it with no lock -- is refused by the goal's checker and
    accepted by `AkzeptiertX`; its user obligation WITH the rely holds (`n1_logikA`), and
    `ziel_atomar_spec` gives every leg of `ZielAtomarW` at every machine W reaches, for every
    order assignment, budget and start memory. Non-degenerate: `konfig` IS an admitted shared
    atomic (`n1_konfig_geteilt`), and W's stale read of it really happens on a covered run
    (`n1_stale_gedeckt`: `hauptA` stores the initial `konfig` after `kern` wrote 3, where G
    stores 3).
  * THE RELY BITES (`hP_havoc_bites`): `zaehlB` of the program `hP` stores `konfig` into
    `tabB[0]`, then tests `konfig == tabB[0]` and writes 1 or 2; it ensures `tabB[0] == 1`.
    Accepted by `AkzeptiertX` (`hP_akzeptiertX`, `konfig` is in no contract). The OLD
    obligation holds for the body (`hP_seq`: sequentially the second read equals the first),
    the obligation with the rely FAILS (`hP_rely_nicht`): an environment that answers the second
    read of `konfig` differently drives the body into `tabB[0] = 2`. So (b) with the rely is
    strictly stronger than (b) on units with a shared atomic, and it refuses exactly the
    sequential reasoning another thread breaks (`kern` writing between the two reads).
  * THE REFUSAL (`vertrag_atomar_abgelehnt`): a contract over the shared atomic -- `kern`
    ensures `konfig == 3` -- is refused by `AkzeptiertX` (component `fussWXB`), while
    `AkzeptiertA` (Speichermodell/AtomarZeuge.lean, no contract condition) accepts it.
-/
import Grammatik.Zielsatz.AtomarAkzeptiert
import Grammatik.Speichermodell.AtomarZeuge
import Grammatik.Speichermodell.Zeuge
import Grammatik.ZielOrtGanzZeuge

namespace Gabbro.Grammatik.AtomarXZeuge

open Gabbro.Grammatik Speichermodell Zielsatz NIZeuge

/-! ## 1. The flag, covered -/

/-- The declared starts of configuration 1. -/
abbrev n1ws : List nD.Fn := [NFn.hauptA, NFn.hauptB, NFn.kern]

theorem n1_akzeptiertX : AkzeptiertX nP SchwachZeuge.nS nFs [] nCs n1ws = true := by decide

theorem n1_alt_abgelehnt : Akzeptiert nP SchwachZeuge.nS nFs [] nCs n1ws = false :=
  AtomarZeuge.n1_abgelehnt

/-- Every body of `nP` returns (no call, no transition, no `forever`): no `logik` outcome. -/
theorem nP_zurueck (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (A : AUmwelt nD)
    (passes : Nat) (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (f : nD.Fn) (σ : World nD) (ρ : Env nD (nD.params f)) (e : Logik nD) :
    execEndHA (V := vertragVon nD f) S O' U A passes R (nP.rumpf f) σ ρ ≠ EndAusgang.logik e := by
  cases f <;> simp [nP, nRumpfA, nRumpfB, nRumpfKern, nKernS, nRumpfZA, nRumpfZB, nRumpfLeck,
    lkS, lkW, lkRet, execEndHA, execStmtHA, execBlockHA]
  split
  all_goals first | (simp; done) | (rename_i heq; split at heq <;> simp at heq)

/-- **(b) with the rely on configuration 1**: no contract, no invariant, no reason, and no
    `logik` outcome whatever a shared atomic read answers. -/
theorem n1_logikA (T : nD.Tab ⊕ nD.Glob → Prop) : LogikPflichtA nP SchwachZeuge.nS (axWahr nD) T := by
  refine ⟨fun passes f => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨(fun (L : nD.Lock) => nomatch L), axEnsLokal_wahr⟩⟩
  · intro O' _ _ _ U _ A _ R _ _ σ ρ _
    exact ⟨fun _ _ _ => rfl, fun g => nP_zurueck _ O' U A passes (torRuf nP R) f σ ρ _⟩
  · intro O' _ _ _ U _ A _ R _ _ σ ρ _ e
    exact nP_zurueck _ O' U A passes R f σ ρ e
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i
    exact nomatch i
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r _
    cases f <;> exact r.elim0

/-- **THE FLAG, COVERED**: at every machine W reaches from configuration 1 -- every order
    assignment, budget, start memory -- every leg of `ZielAtomarW`. -/
theorem n1_ziel_atomar (sp : Speicher nD) (ord : nD.Glob → Ordnung) (passes : Nat) :
    ∀ W : RufMaschineW nD, RufErreichbarW nP nO passes ord (RufStartW (RufStartG nP sp init1)) W →
      ZielAtomarW nP SchwachZeuge.nS nO passes ord (GeteiltV nP n1ws) (RufStartG nP sp init1) W :=
  ziel_atomar_spec nP SchwachZeuge.nS (axWahr nD) nFs_voll (ls := []) (fun L => nomatch L) n1ws
    (akzeptiertSpecX_of nFs_voll (fun L => nomatch L) nCs_voll n1_akzeptiertX)
    (n1_logikA _) nO ⟨nO_gut, nO_lokal, axVertragO_wahr nO⟩ passes ord sp init1
    (AtomarZeuge.n1_start sp)

/-- **Non-degenerate: `konfig` is an admitted shared atomic** -- atomic, unguarded, read by
    `hauptA`'s footprint while `kern` writes it, in no contract. -/
theorem n1_konfig_geteilt : GeteiltV nP n1ws (.inr NGlob.konfig) := by
  refine ⟨⟨⟨_, rfl, rfl⟩, ⟨(fun (L : nD.Lock) _ => nomatch L), fun h => ?_⟩⟩, fun g => ?_⟩
  · have := h NFn.hauptA List.mem_cons_self NFn.kern
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (Or.inl (fun e => by cases e)) NFn.hauptA NFn.kern .wurzel (istIn_iff.mp (by decide)) .wurzel
    exact Bool.noConfusion this
  · cases g <;> exact ⟨List.not_mem_nil, List.not_mem_nil, List.not_mem_nil⟩

/-- **Non-degenerate: W's stale read happens on a covered run.** After `kern` wrote
    `konfig := 3`, W lets `hauptA` store the INITIAL `konfig` (0) into `tabA[0]`, where G on the
    same schedule stores 3; the machine after that step satisfies every leg of `ZielAtomarW`. -/
theorem n1_stale_gedeckt (ord : nD.Glob → Ordnung) :
    ∃ W1 W2 : RufMaschineW nD,
      RufErreichbarW nP nO 0 ord (RufStartW (RufStartG nP sp0 init1)) W1 ∧
      RufSchrittW nP nO 0 ord W1 0 W2 ∧
      (W1.g.speicher.globs NGlob.konfig).n = 3 ∧ (W2.g.speicher.slots NTab.tabA 0 ()).n = 0 ∧
      ((r1M2 sp0).speicher.slots NTab.tabA 0 ()).n = 3 ∧
      ZielAtomarW nP SchwachZeuge.nS nO 0 ord (GeteiltV nP n1ws) (RufStartG nP sp0 init1) W2 := by
  obtain ⟨W1, W2, hW1, hs, _, hk, hA, hG⟩ := SchwachZeuge.w_nicht_sc ord
  exact ⟨W1, W2, hW1, hs, hk, hA, hG, n1_ziel_atomar sp0 ord 0 W2 (.schritt _ _ _ hW1 hs)⟩

/-! ## 2. The rely bites -/

/-- The test `konfig == tabB[0]`. -/
def hC : Expr nD [] [] .bool := .eq (.glob NGlob.konfig (nGd _ _)) (.slot NTab.tabB () nI0 (nDarf _ _))

/-- `tabB[0] = konfig`. -/
def hLies : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _)

/-- `tabB[0] = k`. -/
def hSetze (k : Int) (h0 : (0 : Int) ≤ k) (h9 : k ≤ 9) : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (nW k h0 h9) rfl (nDarf _ _)

/-- `if konfig == tabB[0] { tabB[0] = 1 } else { tabB[0] = 2 }`. -/
def hTest : Stmt nD (vertragVon nD NFn.zaehlB) false [] [] [] :=
  .ite hC (.cons (hSetze 1 (by decide) (by decide)) .nil) (.cons (hSetze 2 (by decide) (by decide)) .nil)

/-- The body of `zaehlB` in `hP`: read `konfig`, then test it again. -/
def hRumpf : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons hLies (.cons hTest (.ret .keine List.Perm.nil))

/-- `zaehlB` ensures `tabB[0] == 1`. -/
def hEns : Expr nD (ErgCtx (nD.params NFn.zaehlB) (nD.erg NFn.zaehlB)) (vertragVon nD NFn.zaehlB).ende
    .bool :=
  .eq (.slot NTab.tabB () nI0 (nDarf _ _)) (nW 1 (by decide) (by decide))

/-- **The program `hP`**: `nP` with `zaehlB := hRumpf` and its contract `tabB[0] == 1`. -/
def hP : Programm nD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .hauptA => .wahr
    | .hauptB => .wahr
    | .kern => .wahr
    | .ruhe => .wahr
    | .zaehlA => .wahr
    | .zaehlB => hEns
    | .leck => .wahr
  rumpf
    | .hauptA => nRumpfA
    | .hauptB => nRumpfB
    | .kern => nRumpfKern
    | .ruhe => .ret .keine List.Perm.nil
    | .zaehlA => nRumpfZA
    | .zaehlB => hRumpf
    | .leck => nRumpfLeck

/-- `kern` writes `konfig`, `zaehlB` reads it. -/
abbrev hws : List nD.Fn := [NFn.kern, NFn.zaehlB]

/-- **Accepted by the checker with the rely** (`konfig` is shared and in no contract; `tabB` is
    `zaehlB`'s alone) ... -/
theorem hP_akzeptiertX : AkzeptiertX hP SchwachZeuge.nS nFs [] nCs hws = true := by decide

/-- ... and refused by the goal's checker (the unguarded shared read). -/
theorem hP_alt_abgelehnt : Akzeptiert hP SchwachZeuge.nS nFs [] nCs hws = false := by decide

theorem hP_konfig_geteilt : GeteiltA hP hws (.inr NGlob.konfig) := by
  refine ⟨⟨_, rfl, rfl⟩, ⟨(fun (L : nD.Lock) _ => nomatch L), fun h => ?_⟩⟩
  have := h NFn.zaehlB (List.mem_cons_of_mem _ List.mem_cons_self) NFn.kern List.mem_cons_self
    (Or.inl (fun e => by cases e)) NFn.zaehlB NFn.kern .wurzel (istIn_iff.mp (by decide)) .wurzel
  exact Bool.noConfusion this

/-- The value of `tabB[0]` after a normal return (`-1` otherwise). -/
def tabBNach {V : Vertrag nD} {l : Bool} {Γ : Ctx} : EndAusgang V l Γ → Int
  | .zurueck σ' _ => (σ'.slots NTab.tabB 0 ()).n
  | _ => -1

/-- **Sequentially, the body meets its contract**: the second read of `konfig` sees the value
    the first one stored, so the test holds and the body writes 1. -/
theorem hP_seq_wert (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f) (σ : World nD)
    (ρ : Env nD (nD.params NFn.zaehlB)) :
    tabBNach (execEndH (V := vertragVon nD NFn.zaehlB) S O' U passes R hRumpf σ ρ) = 1 := by
  simp only [hRumpf, hLies, hTest, execEndH, execStmtH, execBlockH]
  split <;> rename_i heq <;> split at heq <;> rename_i hc
  all_goals first
    | exact (hc (decide_eq_true rfl)).elim
    | (simp only [hSetze, execStmtH] at heq <;> cases heq <;> rfl)

/-- The body always returns (both engines, every environment). -/
theorem hRumpf_zurueckA (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (A : AUmwelt nD)
    (passes : Nat) (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    ∃ σ' v, execEndHA (V := vertragVon nD NFn.zaehlB) S O' U A passes R hRumpf σ ρ =
      EndAusgang.zurueck σ' v := by
  simp only [hRumpf, hLies, hTest, execEndHA, execStmtHA, execBlockHA]
  split <;> rename_i heq <;> split at heq <;>
    (simp only [hSetze, execStmtHA] at heq <;> cases heq <;> exact ⟨_, _, rfl⟩)

theorem hRumpf_zurueck (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f)
    (σ : World nD) (ρ : Env nD (nD.params NFn.zaehlB)) :
    ∃ σ' v, execEndH (V := vertragVon nD NFn.zaehlB) S O' U passes R hRumpf σ ρ =
      EndAusgang.zurueck σ' v := by
  simp only [hRumpf, hLies, hTest, execEndH, execStmtH, execBlockH]
  split <;> rename_i heq <;> split at heq <;>
    (simp only [hSetze, execStmtH] at heq <;> cases heq <;> exact ⟨_, _, rfl⟩)

theorem hP_seq (passes : Nat) :
    KoerperGutS hP passes (axWahr nD) SchwachZeuge.nS NFn.zaehlB := by
  refine ⟨fun O' _ _ _ U _ R _ _ σ ρ _ => ⟨fun σ' v h => ?_, fun g h => ?_⟩,
    fun O' _ _ _ U _ R _ _ σ ρ _ e h => ?_⟩
  · have h1 := hP_seq_wert SchwachZeuge.nS O' U passes R σ ρ
    change execEndH _ _ _ _ _ hRumpf σ ρ = _ at h
    rw [h] at h1
    show decide ((σ'.slots NTab.tabB 0 ()).n = 1) = true
    exact decide_eq_true h1
  · obtain ⟨σ', v, h'⟩ := hRumpf_zurueck SchwachZeuge.nS O' U passes (torRuf hP R) σ ρ
    change execEndH _ _ _ _ _ hRumpf σ ρ = _ at h
    rw [h'] at h
    cases h
  · obtain ⟨σ', v, h'⟩ := hRumpf_zurueck SchwachZeuge.nS O' U passes R σ ρ
    change execEndH _ _ _ _ _ hRumpf σ ρ = _ at h
    rw [h'] at h
    cases h

/-- The environment that answers the TEST's read of `konfig` with 5 (another thread wrote it
    between the two reads); every other read unchanged. -/
def aFuenf : AUmwelt nD := fun X σ =>
  if X = hC.orte then σ.storeGlob NGlob.konfig (⟨5, by decide, by decide⟩ : Zahl 0 9) else σ

theorem aFuenf_havoc : HavocA (GeteiltA hP hws) aFuenf := by
  intro X σ
  unfold aFuenf
  split
  · rename_i hX
    refine ⟨rfl, fun c hc => ?_⟩
    cases c with
    | inl t => rfl
    | inr g =>
        cases g with
        | konfig =>
            exact absurd ⟨by rw [hX]; exact List.mem_cons_self, hP_konfig_geteilt⟩ hc
        | zaehler => rfl
  · exact ⟨rfl, fun c _ => traegerGleich_refl _ c⟩

/-- **With the rely, the body breaks its contract**: from the all-zero memory, the first read
    stores 0, the test reads 5, the body writes 2. -/
theorem hP_wert_A (S : SperrInv nD) (O' : Orakel nD) (U : Umwelt nD) (passes : Nat)
    (R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f) :
    tabBNach (execEndHA (V := vertragVon nD NFn.zaehlB) S O' U aFuenf passes R hRumpf
      (sp0.welt []) .nil) = 2 := by
  simp only [hRumpf, hLies, hTest, execEndHA, execStmtHA, execBlockHA]
  split <;> rename_i heq <;> split at heq <;> rename_i hc
  all_goals first
    | exact absurd hc (by decide)
    | (simp only [hSetze, execStmtHA] at heq <;> cases heq <;> rfl)

/-- **THE RELY BITES**: the obligation with the rely fails for `zaehlB`, though the sequential
    one holds (`hP_seq`). -/
theorem hP_rely_nicht :
    ¬ KoerperGutSA hP 0 (axWahr nD) SchwachZeuge.nS (GeteiltA hP hws) NFn.zaehlB := by
  intro h
  let R : ∀ f : nD.Fn, World nD → Env nD (nD.params f) → RufAusgang f :=
    fun _ _ _ => .hardware .ieee
  have hR : RespektiertRahmen hP R := ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
  have hOV : OhneVorbedingung R := fun _ _ _ _ h => by cases h
  have hU : HavocOk SchwachZeuge.nS (fun _ σ => σ) := fun L => nomatch L
  have hE := (h.1 nO (gutO_rahmenO nO_gut) nO_lokal (axVertragO_wahr nO) (fun _ σ => σ) hU aFuenf
    aFuenf_havoc R hR hOV (sp0.welt []) .nil rfl).1
  obtain ⟨σ', v, hr⟩ := hRumpf_zurueckA SchwachZeuge.nS nO (fun _ σ => σ) aFuenf 0 R (sp0.welt []) .nil
  have h2 := hP_wert_A SchwachZeuge.nS nO (fun _ σ => σ) 0 R
  rw [hr] at h2
  have h1 := hE σ' v hr
  change decide ((σ'.slots NTab.tabB 0 ()).n = 1) = true at h1
  have := of_decide_eq_true h1
  change (σ'.slots NTab.tabB 0 ()).n = 2 at h2
  omega

/-- So `hP`'s user obligation with the rely FAILS: the goal over GX does not cover it. -/
theorem hP_logikA_nicht : ¬ LogikPflichtA hP SchwachZeuge.nS (axWahr nD) (GeteiltA hP hws) :=
  fun h => hP_rely_nicht (h.1 0 NFn.zaehlB).1

/-- **Both directions together**: accepted by `AkzeptiertX`, the old (b) holds for the body at
    every budget, the new (b) fails. -/
theorem hP_havoc_bites :
    AkzeptiertX hP SchwachZeuge.nS nFs [] nCs hws = true ∧
      (∀ passes, KoerperGutS hP passes (axWahr nD) SchwachZeuge.nS NFn.zaehlB) ∧
      ¬ KoerperGutSA hP 0 (axWahr nD) SchwachZeuge.nS (GeteiltA hP hws) NFn.zaehlB :=
  ⟨hP_akzeptiertX, hP_seq, hP_rely_nicht⟩

/-! ## 3. The refusal: a contract over a shared atomic -/

/-- `kern` ensures `konfig == 3`. -/
def vEns : Expr nD (ErgCtx (nD.params NFn.kern) (nD.erg NFn.kern)) (vertragVon nD NFn.kern).ende .bool :=
  .eq (.glob NGlob.konfig (nGd _ _)) (nW 3 (by decide) (by decide))

/-- `nP` with `kern`'s contract `konfig == 3`. -/
def vP : Programm nD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures
    | .hauptA => .wahr
    | .hauptB => .wahr
    | .kern => vEns
    | .ruhe => .wahr
    | .zaehlA => .wahr
    | .zaehlB => .wahr
    | .leck => .wahr
  rumpf := nP.rumpf

/-- **THE REFUSAL**: on configuration 1 with a contract over the shared `konfig`, `AkzeptiertX`
    refuses at its footprint component, where `AkzeptiertA` (no contract condition) accepts. -/
theorem vertrag_atomar_abgelehnt :
    AkzeptiertX vP SchwachZeuge.nS nFs [] nCs n1ws = false ∧
      fussWXB vP SchwachZeuge.nS nFs n1ws = false ∧
      AkzeptiertA vP SchwachZeuge.nS nFs [] nCs n1ws = true := by
  decide

/-- Non-degenerate: `konfig` is in `kern`'s contract, and shared (as in configuration 1). -/
theorem vertrag_atomar_echt :
    (.inr NGlob.konfig : nD.Tab ⊕ nD.Glob) ∈ (vP.ensures NFn.kern).orte ∧
      ¬ VertragsFrei vP (.inr NGlob.konfig) :=
  ⟨List.mem_cons_self, fun h => (h NFn.kern).2.1 List.mem_cons_self⟩

#print axioms n1_ziel_atomar
#print axioms n1_konfig_geteilt
#print axioms n1_stale_gedeckt
#print axioms hP_havoc_bites
#print axioms hP_logikA_nicht
#print axioms vertrag_atomar_abgelehnt

end Gabbro.Grammatik.AtomarXZeuge
