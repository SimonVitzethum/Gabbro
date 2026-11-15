/- Image boundaries inside lowered blocks, with the machine's continuation retained. -/
module
public import Stage0.Senke.Bild.Rek.DannRueck
public import Stage0.Senke.Bild.Rek.Eintritt
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- The image at the first instruction of a remaining block. The frame records the
    pending releases, protected slots and offsets of both loop exits. Unlike an
    end-block boundary, this boundary also has a normal fallthrough continuation. -/
def BodyFrame.RandBIR (B : BodyFrame D) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D (vertragVon D B.f) l Γ Λ Λ') (pc : Runner.W) (m : Runner.Mem)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  ∃ (c : List II) (top : Nat),
    lowB (reserved := B.reserved) (sc := B.sc) B.passes B.A B.L (functionFrame B.P B.f)
      (B.cens, B.tens) B.pr B.ex b = some (c, top) ∧
    top + B.cap ≤ B.Ks ∧ 16 * c.length < 2 ^ 31 ∧
    PreS B.L m pc B.fp B.K (frei Γ B.reserved) c ρ B.reserved ∧ B.lo ≤ frei Γ B.reserved ∧
    Umf B.L B.A B.C B.dv m B.fp B.Ks B.K B.H ∧
    Kopf B.L B.f m B.fp B.K B.rp B.cfp B.ρ0 B.P B.σ0 ∧ WeltAt m B.L σ ∧
    (∀ j ∈ B.pr, j < frei Γ B.reserved) ∧ HeldIn B.H Λ (vertragVon D B.f).boden

/-- A block boundary on both sides. The code address is inside the emitted body;
    `k` retains the source continuation, including context shrinking after a bind. -/
def RandDannL (B : BodyFrame D) (thr : Faden) (stapel : List (RufRahmenG D))
    (rho : Env D (D.params B.f)) (s0 : World D) (Agl : D.Lock → Prop)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (b : Block D (vertragVon D B.f) l Γ Λ Λ')
    (k : GRest D (vertragVon D B.f) l Γ Λ') (pc : Runner.W) (m : Runner.Mem)
    (M : RufMaschineG D) (σ : World D) (ρ : Env D Γ) : Prop :=
  B.RandBIR b pc m σ ρ ∧ RandDannGL thr stapel B.f rho s0 Agl b k M σ ρ

/-- Move both loop exits past a suffix of `n` instructions. This changes no frame
    storage, handler, protected slot or pending release. -/
def BodyFrame.suffix (B : BodyFrame D) (n : Nat) : BodyFrame D :=
  { B with
    ex := exPlus B.ex n }

theorem BodyFrame.Ok.suffix {B : BodyFrame D} (h : B.Ok) (n : Nat) : (B.suffix n).Ok :=
  ⟨h.spec, h.addr, h.lo0, h.ens, h.scH, h.win⟩

/-- Reads change only the trace; a block boundary holds every such read world. -/
theorem BodyFrame.randBIR_lese {B : BodyFrame D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {b : Block D (vertragVon D B.f) l Γ Λ Λ'} {pc : Runner.W} {m : Runner.Mem}
    {σ : World D} {ρ : Env D Γ} (h : B.RandBIR b pc m σ ρ)
    (Λ0 : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) : B.RandBIR b pc m (σ.lese Λ0 os) ρ := by
  obtain ⟨c, top, hl, ht, hs, hp, hlo, hu, hk, hw, hpr, hH⟩ := h
  exact ⟨c, top, hl, ht, hs, hp, hlo, hu, hk, hw, hpr, hH⟩

/-- The common prefix of every direct block call. Extracting this record follows
    `lowB`; entering a callee then uses one proof for plain, bound and fallible calls. -/
def BlockCallSite (B : BodyFrame D) {Γ : Ctx} {Λ : List (Res D)} (g : D.Fn)
    (args : Args D Γ Λ (D.params g)) (pc : Runner.W) (m : Runner.Mem)
    (σ : World D) (ρ : Env D Γ) : Prop :=
  ∃ (ca : List II) (ta : Nat),
    lowA B.L (reserved := B.reserved) args (frei Γ B.reserved + FB) = some (ca, ta) ∧
    callTop g (frei Γ B.reserved) ta + B.cap ≤ B.Ks ∧
    PreS B.L m pc B.fp B.K (frei Γ B.reserved) (callC B.A g (frei Γ B.reserved) ca) ρ B.reserved ∧
    Umf B.L B.A B.C B.dv m B.fp B.Ks B.K B.H ∧
    WeltAt m B.L σ ∧
    HeldIn B.H Λ (vertragVon D B.f).boden

/-- A bound call starts with exactly the same argument and call-tail code as a plain call. -/
theorem BodyFrame.randBIR_bindCall_site {B : BodyFrame D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ}
    {hr : D.gruende g = 0} {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandBIR (.bindCall g args he hp hr rest) pc m σ ρ) : BlockCallSite B g args pc m σ ρ := by
  obtain ⟨c, top, hl, ht, _, pre, _, hu, _, hw, _, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, _, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨ca, ta, hca, by omega, pre.left.left, hu, hw, hH⟩

/-- The fallible binder has the same call prefix; status dispatch follows its return. -/
theorem BodyFrame.randBIR_bindCallElse_site {B : BodyFrame D} {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ}
    {hr : 0 < D.gruende g}
    {err : Endblock D (vertragVon D B.f) l (.why (D.gruende g) :: Γ) (nach D g Λ)}
    {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ : World D} {ρ : Env D Γ}
    (h : B.RandBIR (.bindCallElse g args he hp hr err rest) pc m σ ρ) : BlockCallSite B g args pc m σ ρ := by
  obtain ⟨c, top, hl, ht, _, pre, _, hu, _, hw, _, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨ca, ta⟩, hca, ⟨ce, te⟩, _, ⟨cr, tr⟩, _, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have pre' : PreS B.L m pc B.fp B.K (frei Γ B.reserved)
      (callC B.A g (frei Γ B.reserved) ca ++
        (receiveC (D.signatur g) (frei Γ B.reserved) ++
          ([ci 19 (frei Γ B.reserved + FB + contextWords (D.params g) +
            returnWords (D.erg g) (D.gruende g)) (16 * (cr.length + 2)) 0] ++
            (cr ++ ([ci 18 (16 * (ce.length + 1)) 0 0] ++ ce))))) ρ B.reserved := by
    simpa only [elseC, List.append_assoc, Deklaration.params, Deklaration.erg, Deklaration.gruende,
      Int.natCast_add, Int.ofNat_one] using pre
  simp only [elseTop] at ht
  exact ⟨ca, ta, hca, by omega, pre'.left, hu, hw, hH⟩

end Gabbro.Stage0.Senke.BildLauf
