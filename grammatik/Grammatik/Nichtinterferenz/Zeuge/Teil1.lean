module
public import Grammatik.Nichtinterferenz.Zeuge.Teil1Basis
import all Grammatik.Nichtinterferenz.Zeuge.Teil1Basis

public import Grammatik.Nichtinterferenz.Fluss

@[expose] public section



namespace Gabbro.Grammatik

namespace NIZeuge

inductive NDom where
  | K
  | A
  | B
  deriving DecidableEq

def nDarfD : NDom → NDom → Bool
  | .K, _ => true
  | .A, .A => true
  | .B, .B => true
  | _, _ => false

/-- The policy: the kernel domain may flow to both tenants; the tenants
    only to themselves. -/
def nπ : Politik NDom where
  darf := nDarfD
  refl := fun d => by cases d <;> rfl
  trans := fun a b c h1 h2 => by
    cases a <;> cases b <;> cases c <;> simp_all [nDarfD]

/-- The carrier labels. -/
def nLab (dz : NDom) : nD.Tab ⊕ nD.Glob → NDom
  | .inl .tabA => .A
  | .inl .tabB => .B
  | .inr .konfig => .K
  | .inr .zaehler => dz

/-- The oracle: no axiom, no register; every publication visible. -/
def nO : Orakel nD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r => nomatch r
  sichtbar := fun _ _ => true

theorem nO_gut : GutO nO := fun a => nomatch a
theorem nO_lokal : RegLokal nO := ⟨fun r => (nomatch r), fun _ _ _ _ => rfl⟩
theorem nO_treu (T : nD.Tab ⊕ nD.Glob → Bool) (Ax : nD.Ax → Bool) : OrakelTreu T Ax nO :=
  fun a => nomatch a

/-! ## 4. The admitted configuration -/

/-- Config 1: `hauptA : A`, `hauptB : B`, `kern : K`, `ruhe : K`. -/
def L1 : FlussEtiketten nD NDom where
  lab := nLab .B
  labAx := fun a => nomatch a
  wurzel
    | .hauptA => some .A
    | .hauptB => some .B
    | .kern => some .K
    | .ruhe => some .K
    | _ => none

/-- **The admitted configuration passes the flow check**: the shared
    `konfig` is written by the kernel domain only, read by both tenants. -/
theorem n1_fluss : flussB nπ nP nFs nCs L1 = true := by decide

def init1 : Faden → Σ f : nD.Fn, Env nD (nD.params f) :=
  fun t => if t = 0 then ⟨NFn.hauptA, .nil⟩ else if t = 1 then ⟨NFn.hauptB, .nil⟩
    else if t = 2 then ⟨NFn.kern, .nil⟩ else ⟨NFn.ruhe, .nil⟩

def fdom1 : Faden → NDom :=
  fun t => if t = 0 then .A else if t = 1 then .B else .K

theorem n1_wurzel : ∀ t, L1.wurzel (init1 t).1 = some (fdom1 t) := by
  intro t
  unfold init1 fdom1
  by_cases h0 : t = 0
  · simp only [h0, if_true]; rfl
  · by_cases h1 : t = 1
    · simp only [h1, if_true, show (1 : Nat) ≠ 0 from by decide, if_false]; rfl
    · by_cases h2 : t = 2
      · simp only [h2, show (2 : Nat) ≠ 0 from by decide, show (2 : Nat) ≠ 1 from by decide,
          if_true, if_false]; rfl
      · simp only [h0, h1, h2, if_false]; rfl

/-- **NONINTERFERENCE for the two tenants (`n1_ni`)**, every premise of
    `nichtinterferenz` discharged: for every observer domain `B'`, every
    budget, every two start memories agreeing on what `B'` may see and
    every two runs with the same schedule, `B'` sees the same. -/
theorem n1_ni (B' : NDom) (passes : Nat) (sp₁ sp₂ : Speicher nD)
    (hsp : SpeicherGleich (sichtbarC nπ (etiketten L1 fdom1) B') sp₁ sp₂)
    (ms ns : Nat → RufMaschineG nD) (fs' : Nat → Faden) (n : Nat)
    (hm : LaufG nP nO passes (RufStartG nP sp₁ init1) ms fs' n)
    (hn : LaufG nP nO passes (RufStartG nP sp₂ init1) ns fs' n) :
    ∀ k, k ≤ n → beob nπ (etiketten L1 fdom1) B' (ms k) = beob nπ (etiketten L1 fdom1) B' (ns k) :=
  nichtinterferenz nπ nP nO passes init1 L1 fdom1 nFs_voll nCs_voll n1_fluss n1_wurzel B'
    nO_gut nO_lokal (nO_treu _ _) sp₁ sp₂ hsp ms ns fs' n hm hn

/-! ### Two concrete runs of the admitted configuration -/

/-- A memory with tenant A's slot `a` and everything else `0`. -/
def nSp (a : Int) (h0 : (0 : Int) ≤ a) (h9 : a ≤ 9) : Speicher nD :=
  ⟨fun t _ _ => match t with
    | .tabA => (⟨a, h0, h9⟩ : Zahl 0 9)
    | .tabB => (⟨0, by decide, by decide⟩ : Zahl 0 9),
   fun _ => (⟨0, by decide, by decide⟩ : Zahl 0 9)⟩

def sp5 : Speicher nD := nSp 5 (by decide) (by decide)
def sp7 : Speicher nD := nSp 7 (by decide) (by decide)

/-- The world a leaf reaches, when it reaches one. -/
def blattWelt {V : Vertrag nD} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res nD)}
    (s : Stmt nD V l Γ Λ Λ') (σ : World nD) (ρ : Env nD Γ) : World nD :=
  match execStmt nO 0 keinRuf s σ ρ with
  | .ok σ' _ => σ'
  | _ => σ

/-- One `blatt` step of thread `f` whose head is `s; return` at the start
    of its body (empty trace), as the machine after it. -/
def blattM (M : RufMaschineG nD) (f : Faden)
    (s : Stmt nD (vertragVon nD (M.faeden f).kopf.f) false [] [] [])
    (rest : Endblock nD (vertragVon nD (M.faeden f).kopf.f) false [] []) : RufMaschineG nD :=
  let σ' := blattWelt s (M.weltVon f) .nil
  ⟨σ'.speicher,
   rufUpdateG M.faeden f
     ⟨(M.faeden f).stapel,
      ⟨(M.faeden f).kopf.f, (M.faeden f).kopf.rho, (M.faeden f).kopf.s0,
       ⟨false, [], [], .nil, .ende rest⟩⟩,
      σ'.spur, (M.faeden f).log⟩,
   M.lauf ++ rufEigenG f σ'.spur, M.start⟩

theorem blattM_schritt (M : RufMaschineG nD) (f : Faden)
    (s : Stmt nD (vertragVon nD (M.faeden f).kopf.f) false [] [] [])
    (rest : Endblock nD (vertragVon nD (M.faeden f).kopf.f) false [] [])
    (hleaf : s.istBlatt = true)
    (hhead : (M.faeden f).kopf.rest = ⟨false, [], [], .nil, .ende (.cons s rest)⟩)
    (hspur : (M.faeden f).spur = [])
    (hstep : execStmt nO 0 keinRuf s (M.weltVon f) .nil =
      .ok (blattWelt s (M.weltVon f) .nil) .nil) :
    RufSchrittG nP nO 0 M f (blattM M f s rest) := by
  have h := RufSchrittG.blatt (P := nP) M f false [] [] [] s rest .nil hleaf hhead
    (fun _ h => nomatch h) (blattWelt s (M.weltVon f) .nil) .nil
    (blattWelt s (M.weltVon f) .nil).spur hstep (by rw [hspur, List.append_nil])
    (fun L => nomatch L)
  exact h

/-- The runs: thread 2 (`kern`), then thread 0 (`hauptA`), then thread 1
    (`hauptB`) -- a fixed timetable. -/
def tafel1 : Nat → Faden
  | 0 => 2
  | 1 => 0
  | _ => 1

def r1M0 (sp : Speicher nD) : RufMaschineG nD := RufStartG nP sp init1
def r1M1 (sp : Speicher nD) : RufMaschineG nD :=
  blattM (r1M0 sp) 2 nKernS (.ret .empty List.Perm.nil)
def r1M2 (sp : Speicher nD) : RufMaschineG nD :=
  blattM (r1M1 sp) 0 (.assignSlot NTab.tabA () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .empty List.Perm.nil)
def r1M3 (sp : Speicher nD) : RufMaschineG nD :=
  blattM (r1M2 sp) 1 (.assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .empty List.Perm.nil)

def r1 (sp : Speicher nD) : Nat → RufMaschineG nD
  | 0 => r1M0 sp
  | 1 => r1M1 sp
  | 2 => r1M2 sp
  | _ => r1M3 sp

theorem r1_lauf (sp : Speicher nD) : LaufG nP nO 0 (RufStartG nP sp init1) (r1 sp) tafel1 3 := by
  refine ⟨rfl, fun k hk => ?_⟩
  match k, hk with
  | 0, _ => exact blattM_schritt (r1M0 sp) 2 _ _ rfl rfl rfl rfl
  | 1, _ => exact blattM_schritt (r1M1 sp) 0 _ _ rfl rfl rfl rfl
  | 2, _ => exact blattM_schritt (r1M2 sp) 1 _ _ rfl rfl rfl rfl

/-- The two start memories agree on what tenant B may see: everything but
    `tabA`. -/
theorem sp57_B : SpeicherGleich (sichtbarC nπ (etiketten L1 fdom1) NDom.B) sp5 sp7 := by
  intro c hc
  cases c with
  | inl t =>
      cases t with
      | tabA => exact absurd hc (by decide)
      | tabB => rfl
  | inr g => rfl

/-- **The witness run (`n1_zeuge`).** Two runs of the admitted
    configuration under the fixed timetable `kern, hauptA, hauptB`, from
    memories that DIFFER in tenant A's table (5 vs 7): both runs exist
    (three steps each, memory moves: `konfig`, `tabA` and `tabB` are
    written; B's table ends at 3), and tenant B sees the same at every
    index -- by `nichtinterferenz_zeitplan`, every premise discharged.
    Tenant A's inputs really differ. -/
theorem n1_zeuge :
    (∀ k, k ≤ 3 → beob nπ (etiketten L1 fdom1) NDom.B (r1 sp5 k) =
      beob nπ (etiketten L1 fdom1) NDom.B (r1 sp7 k)) ∧
    (sp5.slots NTab.tabA 0 ()).n ≠ (sp7.slots NTab.tabA 0 ()).n ∧
    ((r1 sp5 3).speicher.slots NTab.tabB 0 ()).n = 3 := by
  refine ⟨nichtinterferenz_zeitplan nπ nP nO 0 init1 L1 fdom1 nFs_voll nCs_voll n1_fluss n1_wurzel
    NDom.B nO_gut nO_lokal (nO_treu _ _) tafel1 sp5 sp7 sp57_B (r1 sp5) (r1 sp7) 3
    (r1_lauf sp5) (r1_lauf sp7), ?_, ?_⟩
  · decide
  · rfl

/-! ## 5. The shared lock-free counter is refused -/

/-- Config 2: `zaehlA : A`, `zaehlB : B` share `zaehler`, labelled `dz`. -/
def L2 (dz : NDom) : FlussEtiketten nD NDom where
  lab := nLab dz
  labAx := fun a => nomatch a
  wurzel
    | .zaehlA => some .A
    | .zaehlB => some .B
    | .ruhe => some .K
    | _ => none

/-- **The shared lock-free counter is refused for every label**: labelled
    `A`, tenant B reads A's data; labelled `B` or `K`, tenant A writes
    down. -/
theorem n2_abgelehnt : ∀ dz, flussB nπ nP nFs nCs (L2 dz) = false := by
  intro dz
  cases dz <;> decide

/-! ## 6. The leak: refused, and noninterference fails on two runs -/

/-- Config 3: the root `leck` of domain `d`. -/
def L3 (d : NDom) : FlussEtiketten nD NDom where
  lab := nLab .B
  labAx := fun a => nomatch a
  wurzel
    | .leck => some d
    | _ => none

/-- **The leak is refused for every domain of its root**: it reads `tabA`
    (so its domain must admit `A`) and writes `tabB` (so its domain must
    flow to `B`). -/
theorem n3_abgelehnt : ∀ d, flussB nπ nP nFs nCs (L3 d) = false := by
  intro d
  cases d <;> decide

def init3 : Faden → Σ f : nD.Fn, Env nD (nD.params f) := fun _ => ⟨NFn.leck, .nil⟩

def fdom3 : Faden → NDom := fun _ => .A

def sp0 : Speicher nD := nSp 0 (by decide) (by decide)
def sp1 : Speicher nD := nSp 1 (by decide) (by decide)

def lkM0 (sp : Speicher nD) : RufMaschineG nD := RufStartG nP sp init3

/-- After `endeEntf`: the `if` unfolds into a `dann` residue. -/
def lkM1 (sp : Speicher nD) : RufMaschineG nD :=
  ⟨(lkM0 sp).speicher,
   rufUpdateG (lkM0 sp).faeden 0
     ⟨((lkM0 sp).faeden 0).stapel,
      ⟨((lkM0 sp).faeden 0).kopf.f, ((lkM0 sp).faeden 0).kopf.rho, ((lkM0 sp).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann (.cons lkS .nil) (.ende lkRet)⟩⟩,
      ((lkM0 sp).faeden 0).spur, ((lkM0 sp).faeden 0).log⟩,
   (lkM0 sp).lauf, (lkM0 sp).start⟩

end NIZeuge
end Gabbro.Grammatik
