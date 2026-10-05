/-
  File:      Grammatik/Nichtinterferenz/Zeuge.lean
  Subject:   THE WITNESSES of the noninterference theorem: two tenants on one
             machine.

  Declaration `nD`: tables `tabA` (tenant A) and `tabB` (tenant B), one
  slot each, values `0 .. 9`; two lock-free (`atomic`) globals: `konfig`
  (a configuration the kernel domain `K` writes and both tenants read) and
  `zaehler` (a shared counter). Domains `K`, `A`, `B`: `K` may flow to
  everything, `A` and `B` only to themselves.

  Functions:
  * `hauptA`: `tabA[0] = konfig; return`   (tenant A)
  * `hauptB`: `tabB[0] = konfig; return`   (tenant B)
  * `kern`:   `konfig = 3; return`         (kernel domain)
  * `ruhe`:   `return`
  * `zaehlA`: `zaehler = tabA[0]; return`  (A publishes into a shared
    lock-free structure)
  * `zaehlB`: `tabB[0] = zaehler; return`  (B reads it)
  * `leck`:   `if tabA[0] == 0 { tabB[0] = 1 }; return` -- a write to a
    B-observable carrier under an A-dependent branch.

  1. The ADMITTED configuration (roots `hauptA : A`, `hauptB : B`,
     `kern : K`, `ruhe : K`) passes `flussB` (`n1_fluss`): the shared
     structure `konfig` is written by `K` only and read by both. The
     noninterference theorem holds for it (`n1_ni`, every premise
     discharged), and on two concrete runs with the same fixed timetable
     from memories that differ in tenant A's table (`n1_zeuge`).
  2. The SHARED LOCK-FREE COUNTER (roots `zaehlA : A`, `zaehlB : B`) is
     refused for EVERY label of `zaehler` (`n2_abgelehnt`).
  3. The LEAK (root `leck`) is refused for EVERY domain of its root
     (`n3_abgelehnt`), and it VIOLATES noninterference on two concrete
     runs (`n3_verletzt`): same schedule, start memories equal on every
     B-visible carrier, and after three steps B sees `tabB[0] = 1` in one
     run and `0` in the other.
-/
import Grammatik.Nichtinterferenz.Fluss

namespace Gabbro.Grammatik

namespace NIZeuge

/-! ## 1. The declaration -/

inductive NTab where
  | tabA
  | tabB
  deriving DecidableEq

inductive NGlob where
  | konfig
  | zaehler
  deriving DecidableEq

inductive NFn where
  | hauptA
  | hauptB
  | kern
  | ruhe
  | zaehlA
  | zaehlB
  | leck
  deriving DecidableEq

def nSig (ts : List NTab) (gs : List NGlob) : Signatur NTab NGlob Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => decide (t ∈ ts)
  gschreibt := fun g => decide (g ∈ gs)
  konsumiert := []
  produziert := []

def nSigNr : Nat → Signatur NTab NGlob Empty Empty
  | 0 => nSig [.tabA] []
  | 1 => nSig [.tabB] []
  | 2 => nSig [] [.konfig]
  | 4 => nSig [] [.zaehler]
  | 5 => nSig [.tabB] []
  | 6 => nSig [.tabB] []
  | _ => nSig [] []

def nSigOf : NFn → Nat
  | .hauptA => 0
  | .hauptB => 1
  | .kern => 2
  | .ruhe => 3
  | .zaehlA => 4
  | .zaehlB => 5
  | .leck => 6

/-- The declaration of the two-tenant witness. -/
def nD : Deklaration where
  Tab := NTab
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 9
  erlaubt := fun _ _ _ _ => false
  tabNr := fun _ => none
  Glob := NGlob
  decGlob := inferInstance
  gtyp := fun _ => .int 0 9
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := NFn
  sig := nSigOf
  sigNr := nSigNr
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by simp at h

instance : DecidableEq nD.Fn := inferInstanceAs (DecidableEq NFn)

theorem nDarf (t : nD.Tab) (Λ : List (Res nD)) : darf nD t Λ := fun _ h => nomatch h
theorem nGd (g : nD.Glob) (Λ : List (Res nD)) : gdarf nD g Λ := fun _ h => nomatch h

def nI0 {Γ : Ctx} {Λ : List (Res nD)} {t : nD.Tab} : Expr nD Γ Λ (.index (nD.count t)) :=
  .weiter (by decide) (show (0 : Int) ≤ 1 - 1 by decide) (.lit 0)

def nW {Γ : Ctx} {Λ : List (Res nD)} (k : Int) (h0 : (0 : Int) ≤ k) (h9 : k ≤ 9) :
    Expr nD Γ Λ (.int 0 9) :=
  .weiter h0 h9 (.lit k)

/-! ## 2. The program -/

def nRumpfA : Endblock nD (vertragVon nD NFn.hauptA) false [] [] :=
  .cons (.assignSlot NTab.tabA () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .keine List.Perm.nil)

def nRumpfB : Endblock nD (vertragVon nD NFn.hauptB) false [] [] :=
  .cons (.assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .keine List.Perm.nil)

def nKernS : Stmt nD (vertragVon nD NFn.kern) false [] [] [] :=
  .assignGlob NGlob.konfig (nW 3 (by decide) (by decide)) rfl (nGd _ _)

def nRumpfKern : Endblock nD (vertragVon nD NFn.kern) false [] [] :=
  .cons nKernS (.ret .keine List.Perm.nil)

def nRumpfZA : Endblock nD (vertragVon nD NFn.zaehlA) false [] [] :=
  .cons (.assignGlob NGlob.zaehler (.slot NTab.tabA () nI0 (nDarf _ _)) rfl (nGd _ _))
    (.ret .keine List.Perm.nil)

def nRumpfZB : Endblock nD (vertragVon nD NFn.zaehlB) false [] [] :=
  .cons (.assignSlot NTab.tabB () nI0 (.glob NGlob.zaehler (nGd _ _)) rfl (nDarf _ _))
    (.ret .keine List.Perm.nil)

/-- The condition of the leak: `tabA[0] == 0`. -/
def lkC : Expr nD [] [] .bool := .eq (.slot NTab.tabA () nI0 (nDarf _ _)) (.lit 0)

/-- The write under it: `tabB[0] = 1`. -/
def lkW : Stmt nD (vertragVon nD NFn.leck) false [] [] [] :=
  .assignSlot NTab.tabB () nI0 (nW 1 (by decide) (by decide)) rfl (nDarf _ _)

def lkS : Stmt nD (vertragVon nD NFn.leck) false [] [] [] := .ite lkC (.cons lkW .nil) .nil

def lkRet : Endblock nD (vertragVon nD NFn.leck) false [] [] := .ret .keine List.Perm.nil

def nRumpfLeck : Endblock nD (vertragVon nD NFn.leck) false [] [] := .cons lkS lkRet

def nP : Programm nD where
  invariante := fun i => nomatch i
  requires := fun _ => .wahr
  ensures := fun _ => .wahr
  rumpf
    | .hauptA => nRumpfA
    | .hauptB => nRumpfB
    | .kern => nRumpfKern
    | .ruhe => .ret .keine List.Perm.nil
    | .zaehlA => nRumpfZA
    | .zaehlB => nRumpfZB
    | .leck => nRumpfLeck

def nFs : List nD.Fn := [NFn.hauptA, NFn.hauptB, NFn.kern, NFn.ruhe, NFn.zaehlA, NFn.zaehlB,
  NFn.leck]

theorem nFs_voll : ∀ g : nD.Fn, g ∈ nFs := by
  intro g
  cases g <;> (unfold nFs; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

def nCs : List (nD.Tab ⊕ nD.Glob) :=
  [.inl NTab.tabA, .inl NTab.tabB, .inr NGlob.konfig, .inr NGlob.zaehler]

theorem nCs_voll : ∀ c : nD.Tab ⊕ nD.Glob, c ∈ nCs := by
  intro c
  cases c with
  | inl t => cases t <;>
      (unfold nCs; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))
  | inr g => cases g <;>
      (unfold nCs; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-! ## 3. Domains, policy, labels, oracle -/

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
  blattM (r1M0 sp) 2 nKernS (.ret .keine List.Perm.nil)
def r1M2 (sp : Speicher nD) : RufMaschineG nD :=
  blattM (r1M1 sp) 0 (.assignSlot NTab.tabA () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .keine List.Perm.nil)
def r1M3 (sp : Speicher nD) : RufMaschineG nD :=
  blattM (r1M2 sp) 1 (.assignSlot NTab.tabB () nI0 (.glob NGlob.konfig (nGd _ _)) rfl (nDarf _ _))
    (.ret .keine List.Perm.nil)

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

theorem lk_s1 (sp : Speicher nD) : RufSchrittG nP nO 0 (lkM0 sp) 0 (lkM1 sp) :=
  RufSchrittG.endeEntf (lkM0 sp) 0 false [] [] [] lkS lkRet .nil rfl rfl

/-- The read world of the condition. -/
def lkσ₁ (sp : Speicher nD) : World nD := ((lkM1 sp).weltVon 0).lese [] lkC.orte

/-- Run 1 (`tabA[0] = 0`): the true branch is taken. -/
def lkM2w (sp : Speicher nD) : RufMaschineG nD :=
  ⟨(lkM1 sp).speicher,
   rufUpdateG (lkM1 sp).faeden 0
     ⟨((lkM1 sp).faeden 0).stapel,
      ⟨((lkM1 sp).faeden 0).kopf.f, ((lkM1 sp).faeden 0).kopf.rho, ((lkM1 sp).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann (.cons lkW .nil) (.dann .nil (.ende lkRet))⟩⟩,
      (lkσ₁ sp).spur, ((lkM1 sp).faeden 0).log⟩,
   (lkM1 sp).lauf ++ rufEigenG 0 (lkσ₁ sp).spur, (lkM1 sp).start⟩

theorem lk_s2w : RufSchrittG nP nO 0 (lkM1 sp0) 0 (lkM2w sp0) :=
  RufSchrittG.dannIteWahr (lkM1 sp0) 0 false [] [] [] [] lkC (.cons lkW .nil) .nil .nil
    (.ende lkRet) .nil rfl (lkσ₁ sp0) rfl rfl (lkσ₁ sp0).spur rfl (fun _ h => nomatch h)

/-- The world after the write `tabB[0] = 1`. -/
def lkσ' : World nD := blattWelt lkW ((lkM2w sp0).weltVon 0) .nil

def lkM3w : RufMaschineG nD :=
  ⟨lkσ'.speicher,
   rufUpdateG (lkM2w sp0).faeden 0
     ⟨((lkM2w sp0).faeden 0).stapel,
      ⟨((lkM2w sp0).faeden 0).kopf.f, ((lkM2w sp0).faeden 0).kopf.rho,
       ((lkM2w sp0).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann .nil (.dann .nil (.ende lkRet))⟩⟩,
      lkσ'.spur, ((lkM2w sp0).faeden 0).log⟩,
   (lkM2w sp0).lauf ++ rufEigenG 0 [Ereignis.zugriff NTab.tabB true [] []], (lkM2w sp0).start⟩

theorem lk_s3w : RufSchrittG nP nO 0 (lkM2w sp0) 0 lkM3w :=
  RufSchrittG.dannBlatt (lkM2w sp0) 0 false [] [] [] [] lkW .nil (.dann .nil (.ende lkRet)) .nil
    rfl rfl (fun _ h => nomatch h) lkσ' .nil [Ereignis.zugriff NTab.tabB true [] []] rfl rfl
    (fun L => nomatch L)

/-- Run 2 (`tabA[0] = 1`): the (empty) false branch is taken. -/
def lkM2f (sp : Speicher nD) : RufMaschineG nD :=
  ⟨(lkM1 sp).speicher,
   rufUpdateG (lkM1 sp).faeden 0
     ⟨((lkM1 sp).faeden 0).stapel,
      ⟨((lkM1 sp).faeden 0).kopf.f, ((lkM1 sp).faeden 0).kopf.rho, ((lkM1 sp).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann .nil (.dann .nil (.ende lkRet))⟩⟩,
      (lkσ₁ sp).spur, ((lkM1 sp).faeden 0).log⟩,
   (lkM1 sp).lauf ++ rufEigenG 0 (lkσ₁ sp).spur, (lkM1 sp).start⟩

theorem lk_s2f : RufSchrittG nP nO 0 (lkM1 sp1) 0 (lkM2f sp1) :=
  RufSchrittG.dannIteFalsch (lkM1 sp1) 0 false [] [] [] [] lkC (.cons lkW .nil) .nil .nil
    (.ende lkRet) .nil rfl (lkσ₁ sp1) rfl rfl (lkσ₁ sp1).spur rfl (fun _ h => nomatch h)

def lkM3f : RufMaschineG nD :=
  ⟨(lkM2f sp1).speicher,
   rufUpdateG (lkM2f sp1).faeden 0
     ⟨((lkM2f sp1).faeden 0).stapel,
      ⟨((lkM2f sp1).faeden 0).kopf.f, ((lkM2f sp1).faeden 0).kopf.rho,
       ((lkM2f sp1).faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .dann .nil (.ende lkRet)⟩⟩,
      ((lkM2f sp1).faeden 0).spur, ((lkM2f sp1).faeden 0).log⟩,
   (lkM2f sp1).lauf, (lkM2f sp1).start⟩

theorem lk_s3f : RufSchrittG nP nO 0 (lkM2f sp1) 0 lkM3f :=
  RufSchrittG.dannLeer (lkM2f sp1) 0 false [] [] (.dann .nil (.ende lkRet)) .nil rfl

def lkRun1 : Nat → RufMaschineG nD
  | 0 => lkM0 sp0
  | 1 => lkM1 sp0
  | 2 => lkM2w sp0
  | _ => lkM3w

def lkRun2 : Nat → RufMaschineG nD
  | 0 => lkM0 sp1
  | 1 => lkM1 sp1
  | 2 => lkM2f sp1
  | _ => lkM3f

theorem lkRun1_lauf : LaufG nP nO 0 (RufStartG nP sp0 init3) lkRun1 (fun _ => 0) 3 := by
  refine ⟨rfl, fun k hk => ?_⟩
  match k, hk with
  | 0, _ => exact lk_s1 sp0
  | 1, _ => exact lk_s2w
  | 2, _ => exact lk_s3w

theorem lkRun2_lauf : LaufG nP nO 0 (RufStartG nP sp1 init3) lkRun2 (fun _ => 0) 3 := by
  refine ⟨rfl, fun k hk => ?_⟩
  match k, hk with
  | 0, _ => exact lk_s1 sp1
  | 1, _ => exact lk_s2f
  | 2, _ => exact lk_s3f

theorem sp01_B : SpeicherGleich (sichtbarC nπ (etiketten (L3 .A) fdom3) NDom.B) sp0 sp1 := by
  intro c hc
  cases c with
  | inl t =>
      cases t with
      | tabA => exact absurd hc (by decide)
      | tabB => rfl
  | inr g => rfl

/-- **The leak violates noninterference (`n3_verletzt`).** Same program,
    same oracle, same schedule (thread 0 three times), start memories that
    agree on every carrier tenant B may see (they differ only in `tabA`):
    after three steps B sees `tabB[0] = 1` in one run and `0` in the other.
    Together with `n3_abgelehnt`: the premise `flussB` of
    `nichtinterferenz` is not decoration -- without it the conclusion
    fails. -/
theorem n3_verletzt :
    SpeicherGleich (sichtbarC nπ (etiketten (L3 .A) fdom3) NDom.B) sp0 sp1 ∧
    LaufG nP nO 0 (RufStartG nP sp0 init3) lkRun1 (fun _ => 0) 3 ∧
    LaufG nP nO 0 (RufStartG nP sp1 init3) lkRun2 (fun _ => 0) 3 ∧
    beob nπ (etiketten (L3 .A) fdom3) NDom.B (lkRun1 3) ≠
      beob nπ (etiketten (L3 .A) fdom3) NDom.B (lkRun2 3) ∧
    (∀ d, flussB nπ nP nFs nCs (L3 d) = false) := by
  refine ⟨sp01_B, lkRun1_lauf, lkRun2_lauf, fun h => ?_, n3_abgelehnt⟩
  have hg := ((beob_gleich_iff _ _ _ _ _).mp h).1 (.inl NTab.tabB) rfl
  have h1 : (lkRun1 3).speicher.slots NTab.tabB 0 () = (lkRun2 3).speicher.slots NTab.tabB 0 () :=
    congrFun (congrFun hg 0) ()
  have h2 := congrArg Zahl.n h1
  exact absurd h2 (by decide)

#print axioms Gabbro.Grammatik.NIZeuge.n1_ni
#print axioms Gabbro.Grammatik.NIZeuge.n1_zeuge
#print axioms Gabbro.Grammatik.NIZeuge.n2_abgelehnt
#print axioms Gabbro.Grammatik.NIZeuge.n3_verletzt

end NIZeuge

end Gabbro.Grammatik
