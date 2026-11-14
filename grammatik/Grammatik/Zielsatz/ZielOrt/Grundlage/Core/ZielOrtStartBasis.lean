/-
  File:      Grammatik/ZielOrtStart.lean
  Subject:   WHAT A START FUNCTION OWES AT ITS END (THEOREM-MAP §15.6, §16.2).

  Machine G logs a return only when a frame POPS (`rueck g rho v s0 s1`),
  and a thread's start frame has no caller: it never pops. So `InvAmOrtG`
  (every logged return meets its owed invariants) and the `ensures` half of
  `VertragAmOrtG` said nothing about a start function -- an invariant owed
  at the return of a thread's start function was never checked.

  **The decision.** The completion of a start function IS a machine state:
  the thread's stack is empty and its head stands at a `return` (one of the
  three shapes a pop would fire on: `ret`, `ret` before the rest of an end
  block, `ret` before the rest of a block). No rule of G applies there (the
  returns need a caller, `kein_schritt_ruhig` for the bare shape); the
  thread is finished and stays so. The statement is therefore a property of
  every reachable machine, not of a log entry, and it needs no change of G:

  * `StartEndeG P M`: for every thread whose stack is empty and whose head
    stands at a `return e`, the start function's `ensures` AND every
    invariant it owes hold at the world that return reads
    (`(M.weltVon t).lese Λ e.orte`, exactly the world a pop would log), with
    the value `e` evaluates to there.

  Because it holds on EVERY reachable machine, it holds at the moment the
  thread finishes and at every later moment: the carriers read are stable
  for the finished frame (signature-guarded -- the finished thread holds
  those locks for good --, protected by a lock the frame names, or local),
  and the replay invariant keeps them. A start function that never returns
  owes nothing here (the premise never fires); no `never`/`diverges`
  annotation is needed. The obligation is the existing one: `KoerperGutS`
  (ensures) and `InvGutS` (owed invariants) of the start function, the same
  per-function sequential triples every function owes.

  `ziel_ort_ende` (generic in the local carriers) and
  `ziel_ort_mehrfaden_ende` (thread-local carriers): the flagship's
  conclusion AND `StartEndeG`.

  Since 2026-09-14 (second round, THEOREM-MAP §18): the goal statements of
  §4 demand the obligations at EVERY `forever` budget and conclude on the
  machines of every budget (probe D, `Durchgaenge.lean`, `ProbeD.lean`;
  the per-budget statements are the lemmas `*_bei` of §3), and start
  functions declare no reasons (§2a: `StartOhneGrund`, `KeinStartGrundG`),
  `StartEndeG` covers both plain and completed scoped returns. Replay supplies
  `ScopedRueckGutG` at the release source; `ZielOrtStartSaved.lean` carries
  that guarantee with the saved pre-release world.
-/
module
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
public import Grammatik.Kern.Semantik.Evaluation.Durchgaenge
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. The predicate -/

/-- The residue stands at a `return e` a pop would fire on: `ret` as the
    end block, `ret` before the rest of an end block, or `ret` before the
    rest of a block. -/
def RetKopf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : ErgExpr D Γ Λ V.erg) (r : GRest D V l Γ Λ) : Prop :=
  ∃ hperm : Λ.Perm V.ende,
    r = .ende (.ret e hperm) ∨ (∃ rest, r = .ende (.cons (.ret e hperm) rest)) ∨
    (∃ (Λ'' : List (Res D)) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ''),
      r = .dann (.cons (.ret e hperm) rest) k)

/-- A completed scoped root retains its saved-world contract and invariants.
    Its owed invariants also hold in the current world, by the head replay. -/
def StartScopedEndeG (P : Programm D) (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden), (M.faeden t).stapel = [] →
    ∀ (l : Bool) (Γ : Ctx) (ρ : Env D Γ)
      (v : ErgVal D (vertragVon D (M.faeden t).kopf.f).erg) (vor : World D),
      (M.faeden t).kopf.rest =
        ⟨l, Γ, (vertragVon D (M.faeden t).kopf.f).ende, ρ, .zurueckgekehrt ⟨.inl v, vor⟩⟩ →
      EnsAmRueck P (M.faeden t).kopf.f (M.faeden t).kopf.s0 vor (M.faeden t).kopf.rho v ∧
        InvAmRueck P (M.faeden t).kopf.f vor ∧
        InvAmRueck P (M.faeden t).kopf.f (M.weltVon t)

/-- **The start function's completion**: at every thread whose stack is
    empty and whose head stands at `return e`, the start function's
    `ensures` and every invariant it owes hold at the world the return
    reads, with the returned value. Completed scoped roots additionally owe
    the same guarantees at their saved world before scope release. -/
def StartEndeG (P : Programm D) (M : RufMaschineG D) : Prop :=
  (∀ (t : Faden), (M.faeden t).stapel = [] →
    ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ)
      (e : ErgExpr D Γ Λ (vertragVon D (M.faeden t).kopf.f).erg),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ → RetKopf e r →
      EnsAmRueck P (M.faeden t).kopf.f (M.faeden t).kopf.s0 ((M.weltVon t).lese Λ e.orte)
          (M.faeden t).kopf.rho (evalErg ((M.weltVon t).lese Λ e.orte) e
            ((M.weltVon t).lese Λ e.orte) ρ) ∧
        InvAmRueck P (M.faeden t).kopf.f ((M.weltVon t).lese Λ e.orte)) ∧
    StartScopedEndeG P M

/-! ## 2. From the replay -/

section Ende

variable {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D} {S : SperrInv D}
  {lok : D.Tab ⊕ D.Glob → Bool}

/-- **A replayed head at a `return` meets `ensures` and its owed
    invariants at the machine world** -- whether or not a caller waits. -/
theorem kopfS_ret (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hS : SperrInvOk S)
    {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutS P passes Q S f) (hI : ∀ f, InvGutS P passes Q S f)
    (hFS : ∀ f, FussS P S lok f) {G : RufRahmenG D} {W : World D}
    (hG : KopfS P O passes Q S lok G W) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {ρ : Env D Γ}
    {r : GRest D (vertragVon D G.f) l Γ Λ} (hr : G.rest = ⟨l, Γ, Λ, ρ, r⟩)
    (e : ErgExpr D Γ Λ (vertragVon D G.f).erg) (hk : RetKopf e r) :
    EnsAmRueck P G.f G.s0 (W.lese Λ e.orte) G.rho (evalErg (W.lese Λ e.orte) e (W.lese Λ e.orte) ρ) ∧
      InvAmRueck P G.f (W.lese Λ e.orte) := by
  obtain ⟨hperm, h | ⟨rest, h⟩ | ⟨Λ'', rest, k, h⟩⟩ := hk <;> subst h
  · have hok := kopfS_okS hG hr
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueck S O' U passes R e hperm σ ρ)⟩
  · have hok := okS_ende_cons (kopfS_okS hG hr)
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2.1)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_rueckCons S O' U passes R e hperm rest σ ρ)⟩
  · have hok := okS_dann_cons (kopfS_okS hG hr)
    exact ⟨popS_ens hO hRL hQ hS hsp hK hG hr e (erg_stabil (hFS _) e hok.2.1)
        (ens_stabil (hFS _) hperm) (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ),
      popS_inv hO hRL hQ hS hsp hI hG hr e (fun i hi hs => inv_stabil (hFS _) hperm hi hs)
        (fun O' R U σ => semH_dannRet S O' U passes R e hperm rest k σ ρ)⟩

/-- A completed saved value replays at the current world. Owed invariant
    guards are residual signature locks; no saved/current memory equality is used. -/
theorem kopfS_saved_inv (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hI : ∀ f, InvGutS P passes Q S f) (hFS : ∀ f, FussS P S lok f)
    {G : RufRahmenG D} {W : World D} (hG : KopfS P O passes Q S lok G W)
    {l : Bool} {Γ : Ctx} {ρ : Env D Γ} (v : ErgVal D (vertragVon D G.f).erg)
    (vor : World D)
    (hr : G.rest = ⟨l, Γ, (vertragVon D G.f).ende, ρ, .zurueckgekehrt ⟨.inl v, vor⟩⟩) :
    InvAmRueck P G.f W := by
  obtain ⟨H, HA, HU, σ, hreq, hf, hv, _, hfa, hra, hqa, _, hfu, hiu, _, hg, _, heq⟩ := hG
  have h1 := heq (rufAusV H) (orakelAus O HA) (umweltAus S sp HU) (rufAusV_passt hf)
    (orakelAus_passt O hfa) (umweltAus_passt S sp hfu) (gleichRS_orakelAus O HA)
  rw [hr] at h1 hg
  simp only [semH, weiterH] at h1
  obtain ⟨σ', hex, hsg⟩ := zErgG_gleich_zurueck (ZErgG.folgt_zurueck h1)
  have hInv := (hI G.f) (orakelAus O HA) (orakelAus_rahmen hO hra)
    (regLokal_orakelAus hRL HA) (orakelAus_vertragOP (axVertragOP_of_O _ hQ) hqa)
    (umweltAus S sp HU) (umweltAus_ok hS hsp hiu)
    (rufAusV H) (rufAusV_rahmen hv) (rufAusV_ohneVorbedingung hv.1) G.s0 G.rho hreq σ' v hex
  intro i hi hs
  have h3 := hInv i hi hs
  unfold InvHaelt at h3 ⊢
  rw [← eval_gleichAuf (P.invariante i)
    (fun _ h => inv_stabil (hFS _) (List.Perm.refl _) hi hs h)
    ((gleichAuf_SG hsg).trans hg) .nil]
  exact h3

end Ende

/-! ## 2a. A start function may not end in a reason

A reason return (`retGrund`) hands a failure to the CALLER, which the
typing forces to handle it (`bindCallElse` with its `else` block; a call
that ignores reasons needs `gruende = 0`). A thread's start frame has no
caller: a reason there is a failure nobody handles, no `ensures` is
claimed for it (`rufAt` checks neither `ensures` nor invariants at a
reason return), and `StartEndeG` said nothing (verdict
`URTEIL-MUSE-2026-09-14.md` §5: a start function with `ensures false`
whose body fails with a reason met every premise).

**The decision: start functions declare no reasons** (`StartOhneGrund`,
decidable per start). Then no start frame can stand at a reason return --
`retGrund` needs an element of `Fin (gruende f)` and the bottom frame of a
thread always runs its start function (`wurzelFn_erreichbar`) -- so every
plain completion of a start function is a VALUE return, where `StartEndeG`
checks `ensures` and the owed invariants (`keinStartGrundG`; with
`FertigG`: `fertig_wert`, `Verklemmung.lean`). The alternative -- let a
reason return of a start function check its owed invariants -- would
demand at a thread's root what `rufAt` does not demand of any other reason
return, and still leave its `ensures` unchecked. -/

/-- **The start functions declare no reasons.** -/
def StartOhneGrund (init : Faden → Σ f : D.Fn, Env D (D.params f)) : Prop :=
  ∀ t, D.gruende (init t).1 = 0

/-- The function of a thread's bottom frame. -/
def wurzelFn (z : RufFadenG D) : D.Fn := (z.stapel.getLast?.getD z.kopf).f

/-- No rule of G changes the function of the bottom frame. -/
theorem wurzelFn_schritt {P : Programm D} {O : Orakel D} {pa : Nat} {M M' : RufMaschineG D}
    {u : Faden} (hs : RufSchrittG P O pa M u M') : wurzelFn (M'.faeden u) = wurzelFn (M.faeden u) := by
  rcases schrittMerk hs with ⟨hst, hf, _⟩ | ⟨g, c', rho, s0, hst, hcf, _, _⟩ |
      ⟨caller, rst, hpop, hst, hf, _⟩
  · unfold wurzelFn; rw [hst]
    cases (M.faeden u).stapel.getLast? with
    | none => exact hf
    | some F => rfl
  · unfold wurzelFn; rw [hst, List.getLast?_cons]
    cases (M.faeden u).stapel.getLast? with
    | none => exact hcf
    | some F => rfl
  · unfold wurzelFn; rw [hst, hpop, List.getLast?_cons]
    cases rst.getLast? with
    | none => exact hf
    | some F => rfl

/-- **The bottom frame of every thread runs its start function**, on every
    reachable machine. -/
theorem wurzelFn_erreichbar {P : Programm D} {O : Orakel D} {pa : Nat} {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : ∀ t, wurzelFn (M.faeden t) = (init t).1 := by
  induction hr with
  | start => intro t; rw [start_faden]; rfl
  | schritt M M' u _ hs ih =>
      intro t
      by_cases htu : t = u
      · subst htu
        rw [wurzelFn_schritt hs]
        exact ih t
      · rw [rufSchrittG_fremd hs t htu]
        exact ih t

/-- Every reason-return channel: ordinary source heads, scoped source heads,
    and saved reasons during or after canonical cleanup. -/
def GrundKopf {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) : Prop :=
  ∃ g : Fin V.gruende,
    (∃ hperm : Λ.Perm V.ende,
      r = .ende (.retWhy g hperm) ∨ (∃ rest, r = .ende (.cons (.retWhy g hperm) rest)) ∨
      (∃ (Λ'' : List (Res D)) (rest : Block D V l Γ Λ Λ'') (k : GRest D V l Γ Λ''),
        r = .dann (.cons (.retWhy g hperm) rest) k)) ∨
    (∃ R, r.scopedGrund = some (g, R)) ∨
    (match r with
      | .zurueckgekehrt ⟨.inr reason, _⟩ | .aufraeumen ⟨.inr reason, _⟩ _ => reason = g
      | _ => False)

/-- **No start frame stands at a reason return.** -/
def KeinStartGrundG (M : RufMaschineG D) : Prop :=
  ∀ (t : Faden), (M.faeden t).stapel = [] →
    ∀ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (ρ : Env D Γ)
      (r : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ),
      (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, r⟩ → ¬ GrundKopf r

/-- **Start functions without reasons never end in one**, on every
    reachable machine. -/
theorem keinStartGrundG {P : Programm D} {O : Orakel D} {pa : Nat} {sp : Speicher D}
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} (hG : StartOhneGrund init) {M : RufMaschineG D}
    (hr : RufErreichbarG P O pa (RufStartG P sp init) M) : KeinStartGrundG M := by
  intro t hst l Γ Λ ρ r _ ⟨g, _⟩
  have hw := wurzelFn_erreichbar hr t
  unfold wurzelFn at hw
  rw [hst] at hw
  have h0 : (vertragVon D (M.faeden t).kopf.f).gruende = 0 := by
    show D.gruende (M.faeden t).kopf.f = 0
    have e : (M.faeden t).kopf.f = (init t).1 := hw
    rw [e]
    exact hG t
  have hg : g.val < (vertragVon D (M.faeden t).kopf.f).gruende := g.2
  omega

/-! ## 3. The theorems at one budget (lemmas) -/

/- **The flagship with the start functions' completion, generic in the
    local carriers, AT ONE `forever` BUDGET.** The conclusion of
    `ziel_ort_sperre_invL` AND `StartEndeG`: at every finished thread (empty
    stack, head at a `return`) the start function's `ensures` and owed
    invariants hold. A lemma: the goal statement is `ziel_ort_ende` (§4),
    over every budget. -/

end Gabbro.Grammatik
