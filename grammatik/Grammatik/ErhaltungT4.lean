/-
  File:       Grammatik/ErhaltungT4.lean
  Subject:    Bridge lemmas from the T4 per-form correspondence lemmas
              (`CFormen.lean`, `CFormenI.lean`, `CFormenM.lean`,
              `CFormenH.lean`) to the ruling-table obligations of
              `Erhaltung.lean`.

  Claim (in one sentence):
    For every census slot of `Erhaltung.lean` (`OffeneForm`, 31 slots)
    whose admitted C shape has a T4 correspondence lemma, the bridge
    conjoins that lemma's correspondence with the slot's decided table
    row; slots without C semantics stay listed as uncovered with the
    reason, in the header table below.

  Measurement (all 31 slots, lemma names grep-verified 2026-09-13):
    COVERED (bridge below): logUndOder (`ecorr_und`, `ecorr_oder`),
      bitNicht (`ecorr_bnot`), boolLit (`ecorr_wahr`, `ecorr_falsch`),
      boolTyp (`truth_b2i`, `ecorr_wahr`), deref (`ev_ld`),
      cSizeof (`ev_sizeofQuot`), cConst (`constTab_read`,
      `ro_store_stuck`), adressVon (`ptrTo_named`), voidTyp
      (`retCorr_none`), bedingt (`scorr_ite`, adapter: the generator
      replaces `?:` by `if`), zeigerIndex (`ecorr_byteGuard`),
      pfeilZugriff (`ecorr_slotNamed`), zusammZuweisung
      (`scorr_plusGleich`), schrittStmt (`scorr_plusGleich`, adapter:
      the generator normalises `++` to `+= 1`), syscallStub
      (`scorr_axiomCall`, adapter: the stub is the `.ext` call whose
      assumption shape is `AxCorr`), cEnum (`ecorr_lit`, adapter:
      enum constants elaborate to integer literals).
    UNCOVERED (no C semantics, hence no lemma to bridge from):
      zeigerArithmetik (the price is a refusal; evaluation lemmas cover
      only the in-bounds shape), cInclude, cTypedef, cDefine, cAttribut,
      cInline, typOfErw, wennGnuC, statikAssert (preamble, aliases,
      macros, attributes, compile-time-only, no evaluation),
      doubleTyp, floatTyp (no floats in the C semantics: `CIT`/`CVal`
      are integer-only), schleifeStmt (`retry` is explicitly not
      covered, `CFormenI.lean:2170`), abbruchStmt, fortStmt (no
      `StmtCorr` lemma produces bare `.brk`/`.cont`; `scorr_leave`
      lowers to `.goto`, break/continue live only inside generated
      skeletons), unerreichbarBuiltin (no `Exec` rule, no lemma).
-/
import Grammatik.Erhaltung
import Grammatik.CFormenH

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The `logUndOder` row stands decided in the table (data, by `decide`). -/
theorem logUndOder_steht :
    EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid) :=
  ⟨by decide, by decide⟩

variable {X : TVCtx D} {Γ : Ctx} {Λ : List (Res D)} (K : CEnvLay D Γ)

/-- Bridge (`logUndOder`, `&&`): short-circuit conjunction corresponds,
    and its ruling row stands decided. -/
theorem bridge_logUndOder_und {ca cb : CX} {a b : Expr D Γ Λ .bool}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.land ca cb) (.und a b) ∧
      EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid) :=
  ⟨ecorr_und X K ha hb, logUndOder_steht⟩

/-- Bridge (`logUndOder`, `||`): short-circuit disjunction corresponds,
    and its ruling row stands decided. -/
theorem bridge_logUndOder_oder {ca cb : CX} {a b : Expr D Γ Λ .bool}
    (ha : ExprCorr X K ca a) (hb : ExprCorr X K cb b) :
    ExprCorr X K (.lor ca cb) (.oder a b) ∧
      EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.logUndOder logUndOderEntscheid) :=
  ⟨ecorr_oder X K ha hb, logUndOder_steht⟩

/-- The `boolLit` row stands decided in the table (data, by `decide`). -/
theorem boolLit_steht :
    EntscheidZiel.luecke OffeneForm.boolLit (.aufListe "generous reading: boolean literals") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.boolLit (.aufListe "generous reading: boolean literals")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`boolLit`, `true`): the literal `1` corresponds, and the row stands. -/
theorem bridge_boolLit_wahr :
    ExprCorr X K (.lit 1) (Expr.wahr (D := D) (Γ := Γ) (Λ := Λ)) ∧
      EntscheidZiel.luecke OffeneForm.boolLit (.aufListe "generous reading: boolean literals") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.boolLit (.aufListe "generous reading: boolean literals")) :=
  ⟨ecorr_wahr X K, boolLit_steht⟩

/-- Bridge (`boolLit`, `false`): the literal `0` corresponds, and the row stands. -/
theorem bridge_boolLit_falsch :
    ExprCorr X K (.lit 0) (Expr.falsch (D := D) (Γ := Γ) (Λ := Λ)) ∧
      EntscheidZiel.luecke OffeneForm.boolLit (.aufListe "generous reading: boolean literals") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.boolLit (.aufListe "generous reading: boolean literals")) :=
  ⟨ecorr_falsch X K, boolLit_steht⟩

/-- The `boolTyp` row stands decided in the table (data, by `decide`). -/
theorem boolTyp_steht :
    EntscheidZiel.luecke OffeneForm.boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`boolTyp`): `_Bool` values are `0`/`1` (`truth_b2i`), and the row stands.
    Adapter: the C type is erased to the value convention at the semantics. -/
theorem bridge_boolTyp (b : Bool) :
    truth (.int (b2i b)) = some b ∧
      EntscheidZiel.luecke OffeneForm.boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.boolTyp (.aufListe "generous reading: <stdbool.h> for _Bool")) :=
  ⟨truth_b2i b, boolTyp_steht⟩

/-- The `cEnum` row stands decided in the table (data, by `decide`). -/
theorem cEnum_steht :
    EntscheidZiel.luecke OffeneForm.cEnum (.aufListe "closed alternative list as int") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.cEnum (.aufListe "closed alternative list as int")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`cEnum`): enum constants correspond as integer literals, and the row stands.
    Adapter: enum constants elaborate to integer literals before the C semantics. -/
theorem bridge_cEnum (n : Int) :
    ExprCorr X K (.lit n) (Expr.lit (D := D) (Γ := Γ) (Λ := Λ) n) ∧
      EntscheidZiel.luecke OffeneForm.cEnum (.aufListe "closed alternative list as int") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.cEnum (.aufListe "closed alternative list as int")) :=
  ⟨ecorr_lit X K n, cEnum_steht⟩

/-- The `deref` row stands decided in the table (data, by `decide`). -/
theorem deref_steht :
    EntscheidZiel.luecke OffeneForm.deref (.aufListe "plain dereference") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.deref (.aufListe "plain dereference")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`deref`): a plain load evaluates from the pointer value, and the row stands. -/
theorem bridge_deref {L : CLayout} {orc : DevOrc} {fr : Nat} {p : CX} {τ : CTy}
    {st st1 : CSt} {ρ : CLok} {q : CPtr} {v : CVal}
    (hp : ev L orc fr p st ρ = some (.ptr q, st1))
    (hl : bLoad L st1 q τ = some v) :
    ev L orc fr (.ld p τ) st ρ = some (v, st1) ∧
      EntscheidZiel.luecke OffeneForm.deref (.aufListe "plain dereference") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.deref (.aufListe "plain dereference")) :=
  ⟨ev_ld hp hl, deref_steht⟩

/-- The `bitNicht` row stands decided in the table (data, by `decide`). -/
theorem bitNicht_steht :
    EntscheidZiel.luecke OffeneForm.bitNicht (.aufListe "double-cast width rule") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.bitNicht (.aufListe "double-cast width rule")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`bitNicht`): `~` at an unsigned type is the double-cast width
    rule the emitter writes, and the row stands. -/
theorem bridge_bitNicht (t : CIT) (hts : t.sgn = false) {l1 h1 : Int} {cx : CX}
    (h0 : 0 ≤ l1) (hw : h1 < 2 ^ t.bits) {a : Expr D Γ Λ (.int l1 h1)}
    (ha : ExprCorr X K cx a) (hta : t.holds l1 h1) :
    ExprCorr X K (.cast t (.cpl t.promote (.cast t cx)))
      (Expr.bnot t.bits h0 hw a) ∧
      EntscheidZiel.luecke OffeneForm.bitNicht (.aufListe "double-cast width rule") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.bitNicht (.aufListe "double-cast width rule")) :=
  ⟨ecorr_bnot X K t hts h0 hw ha hta, bitNicht_steht⟩

/-- The `cSizeof` row stands decided in the table (data, by `decide`). -/
theorem cSizeof_steht :
    EntscheidZiel.luecke OffeneForm.cSizeof (.aufListe "layout-derived compile-time count; operands never evaluated") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.cSizeof (.aufListe "layout-derived compile-time count; operands never evaluated")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`cSizeof`): the layout quotient evaluates to the element
    count without touching the operands, and the row stands. -/
theorem bridge_cSizeof (L : CLayout) (orc : DevOrc) (fr : Nat) (t : CIT) (n es : Nat)
    (hes : 0 < es) (hsz : ((n * es : Nat) : Int) ≤ 2 ^ 64 - 1)
    (hes' : (es : Int) ≤ 2 ^ 64 - 1) (hn : (n : Int) ≤ t.hi)
    (st : CSt) (ρ : CLok) :
    ev L orc fr (sizeofQuot t (n * es) es) st ρ = some (.int n, st) ∧
      EntscheidZiel.luecke OffeneForm.cSizeof (.aufListe "layout-derived compile-time count; operands never evaluated") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.cSizeof (.aufListe "layout-derived compile-time count; operands never evaluated")) :=
  ⟨ev_sizeofQuot L orc fr t n es hes hsz hes' hn st ρ, cSizeof_steht⟩

/-- The `cConst` row stands decided in the table (data, by `decide`). -/
theorem cConst_steht :
    EntscheidZiel.luecke OffeneForm.cConst (.aufListe "read-only qualifier") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.cConst (.aufListe "read-only qualifier")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`cConst`, read direction): a read-only table cell loads its
    recorded value, and the row stands. -/
theorem bridge_cConst_lese (L : CLayout) (orc : DevOrc) (fr : Nat) (c : Nat) (τ : CTy)
    (vals : List Int)
    (hL : L (.ro c) = some { lay := arrLay τ vals.length, kind := .readonly, base := 0 })
    (st : CSt) (hlive : st.live (.ro c) = true)
    (hmem : ∀ k (hk : k < vals.length), st.mem (.ro c) (k * τ.size) = .int vals[k])
    (ρ : CLok) (ci : CX) (k : Nat) (hk : k < vals.length) (st1 : CSt)
    (hi : ev L orc fr ci st ρ = some (.int k, st1)) (hs : SameML st st1) :
    ev L orc fr (.ld (.idx (.addr (.ro c)) ci vals.length τ.size) τ) st ρ =
      some (.int vals[k], st1) ∧
      EntscheidZiel.luecke OffeneForm.cConst (.aufListe "read-only qualifier") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.cConst (.aufListe "read-only qualifier")) :=
  ⟨constTab_read L orc fr c τ vals hL st hlive hmem ρ ci k hk st1 hi hs, cConst_steht⟩

/-- Bridge (`cConst`, refusal direction): a store to a read-only block is
    stuck, and the row stands. -/
theorem bridge_cConst_schreib (L : CLayout) (st : CSt) (c : Nat) (B : BlkLay)
    (hB : L (.ro c) = some B) (hk : B.kind = .readonly) (o : Int) (τ : CTy) (v : CVal) :
    bStore L st ⟨.ro c, o⟩ τ v = none ∧
      EntscheidZiel.luecke OffeneForm.cConst (.aufListe "read-only qualifier") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.cConst (.aufListe "read-only qualifier")) :=
  ⟨ro_store_stuck L st c B hB hk o τ v, cConst_steht⟩

/-- The `adressVon` row stands decided in the table (data, by `decide`). -/
theorem adressVon_steht :
    EntscheidZiel.luecke OffeneForm.adressVon (.aufListe "provenance-carrying address") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.adressVon (.aufListe "provenance-carrying address")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`adressVon`): the named table storage denotes table `t`'s
    object, and the row stands. Adapter: `PtrTo` is the provenance
    statement, not the full address-of UB story. -/
theorem bridge_adressVon (t : D.Tab) :
    PtrTo X K (.addr (.tab (X.EL.tnr t))) t ∧
      EntscheidZiel.luecke OffeneForm.adressVon (.aufListe "provenance-carrying address") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.adressVon (.aufListe "provenance-carrying address")) :=
  ⟨ptrTo_named X K t, adressVon_steht⟩

/-- The `voidTyp` row stands decided in the table (data, by `decide`). -/
theorem voidTyp_steht :
    EntscheidZiel.luecke OffeneForm.voidTyp (.aufListe "empty result and parameter types as types; silence casts as deliberate") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.voidTyp (.aufListe "empty result and parameter types as types; silence casts as deliberate")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`voidTyp`): an empty result corresponds to no C value, and the row stands. -/
theorem bridge_voidTyp {v : ErgVal D none} :
    RetCorr X.EL none v none ∧
      EntscheidZiel.luecke OffeneForm.voidTyp (.aufListe "empty result and parameter types as types; silence casts as deliberate") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.voidTyp (.aufListe "empty result and parameter types as types; silence casts as deliberate")) :=
  ⟨retCorr_none rfl v, voidTyp_steht⟩

/-- The `bedingt` row stands decided in the table (data, by `decide`). -/
theorem bedingt_steht :
    EntscheidZiel.luecke OffeneForm.bedingt bedingtEntscheid ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.bedingt bedingtEntscheid) :=
  ⟨by decide, by decide⟩

/-- Bridge (`bedingt`): the replacement `if` corresponds, and the row stands.
    Adapter: the generator replaces `?:` by `if`, so the correspondence runs
    through `scorr_ite`; `ev_condT`/`ev_condF` describe the never-emitted
    `.cond` shape. -/
theorem bridge_bedingt (m : Nat) {V : Vertrag D} {l : Bool} {Λ' : List (Res D)}
    {c : Expr D Γ Λ .bool} {t e : Block D V l Γ Λ Λ'}
    {cc : CX} {ct ce : CS}
    (hc : ExprCorr X K cc c) (ht : BlockSem X m K t ct) (he : BlockSem X m K e ce) :
    StmtCorr X m K (Stmt.ite c t e) (.ite cc ct ce) ∧
      EntscheidZiel.luecke OffeneForm.bedingt bedingtEntscheid ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.bedingt bedingtEntscheid) :=
  ⟨scorr_ite X m K hc ht he, bedingt_steht⟩

/-- The `zeigerIndex` row stands decided in the table (data, by `decide`). -/
theorem zeigerIndex_steht :
    EntscheidZiel.luecke OffeneForm.zeigerIndex zeigerIndexEntscheid ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.zeigerIndex zeigerIndexEntscheid) :=
  ⟨by decide, by decide⟩

/-- Bridge (`zeigerIndex`): the bound-guarded byte read corresponds, and the
    row stands. This is the admitted in-bounds shape; the per-site duty to
    stay in bounds is the checker's, the outside case is the UB row. -/
theorem bridge_zeigerIndex (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (hgt : D.geist t = false) (hss : (X.EL.trec t).ssize = 1)
    (hoff : (X.EL.trec t).off (X.EL.fnr t f) = 0) (hty : X.EL.slotTy t f = .int false .w8)
    (hN : D.count t ≤ 2 ^ 64 - 1) {ci : CX} {i : Expr D Γ Λ (.index (D.count t))}
    (hL : darf D t Λ) (hi : ExprCorr X K ci i) :
    ExprCorr X K
      (.cond CIT.i32 (.cmp .lt CIT.u64 (.cast CIT.u64 ci) (.lit (D.count t)))
        (.ld (.idx (.addr (.tab (X.EL.tnr t))) (.cast CIT.u64 ci) (X.EL.trec t).count 1)
          (.int false .w8))
        .trap)
      (Expr.slot t f i hL) ∧
      EntscheidZiel.luecke OffeneForm.zeigerIndex zeigerIndexEntscheid ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.zeigerIndex zeigerIndexEntscheid) :=
  ⟨ecorr_byteGuard X K t f hf hgt hss hoff hty hN hL hi, zeigerIndex_steht⟩

/-- The `pfeilZugriff` row stands decided in the table (data, by `decide`). -/
theorem pfeilZugriff_steht :
    EntscheidZiel.luecke OffeneForm.pfeilZugriff (.aufListe "generous reading of field access") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.pfeilZugriff (.aufListe "generous reading of field access")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`pfeilZugriff`): the named slot field read corresponds, and the
    row stands. Adapter: `->` on the table storage is `slotA` plus a load. -/
theorem bridge_pfeilZugriff (t : D.Tab) (f : D.Feld t) (hgt : D.geist t = false) {ci : CX}
    {i : Expr D Γ Λ (.index (D.count t))} (hL : darf D t Λ) (hi : ExprCorr X K ci i) :
    ExprCorr X K (.ld (.slotA (.addr (.tab (X.EL.tnr t))) ci (X.EL.trec t).count
      (X.EL.trec t).ssize ((X.EL.trec t).off (X.EL.fnr t f))) (X.EL.slotTy t f))
      (Expr.slot t f i hL) ∧
      EntscheidZiel.luecke OffeneForm.pfeilZugriff (.aufListe "generous reading of field access") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.pfeilZugriff (.aufListe "generous reading of field access")) :=
  ⟨ecorr_slotNamed X K t f hgt hL hi, pfeilZugriff_steht⟩

/-- The `zusammZuweisung` row stands decided in the table (data, by `decide`). -/
theorem zusammZuweisung_steht :
    EntscheidZiel.luecke OffeneForm.zusammZuweisung (.aufListe "generous reading of assignment") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.zusammZuweisung (.aufListe "generous reading of assignment")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`zusammZuweisung`, `+=`): the compound assignment corresponds,
    and the row stands. -/
theorem bridge_zusammZuweisung (m : Nat) {V : Vertrag D} {l : Bool}
    (hK : K.okB = true) {lo hi lo' hi' : Int} (x : Var Γ (.int lo hi))
    {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} (t : CIT) {τc : CTy}
    (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi) (he : ExprCorr X K ce e)
    (hta : t.holds lo hi) (htb : t.holds lo' hi') (htr : t.holds (lo + lo') (hi + hi'))
    (hd : declOk (.int lo hi) τc = true) :
    StmtCorr X m K (Stmt.plusGleich (V := V) (l := l) x e h1 h2)
      (.set (K.loc x) τc (.bin .add t (.var (K.loc x)) ce)) ∧
      EntscheidZiel.luecke OffeneForm.zusammZuweisung (.aufListe "generous reading of assignment") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.zusammZuweisung (.aufListe "generous reading of assignment")) :=
  ⟨scorr_plusGleich X m K hK x t h1 h2 he hta htb htr hd, zusammZuweisung_steht⟩

/-- The `schrittStmt` row stands decided in the table (data, by `decide`). -/
theorem schrittStmt_steht :
    EntscheidZiel.luecke OffeneForm.schrittStmt (.aufListe "++ to += 1; exchange CAS untouched") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.schrittStmt (.aufListe "++ to += 1; exchange CAS untouched")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`schrittStmt`): the normalised `+= 1` corresponds, and the row stands.
    Adapter: the generator normalises `++` to `+= 1`, so the correspondence
    runs through `scorr_plusGleich`; `cas_success`/`cas_failure` cover the
    untouched exchange-CAS leg. -/
theorem bridge_schrittStmt (m : Nat) {V : Vertrag D} {l : Bool}
    (hK : K.okB = true) {lo hi lo' hi' : Int} (x : Var Γ (.int lo hi))
    {e : Expr D Γ Λ (.int lo' hi')} {ce : CX} (t : CIT) {τc : CTy}
    (h1 : lo ≤ lo + lo') (h2 : hi + hi' ≤ hi) (he : ExprCorr X K ce e)
    (hta : t.holds lo hi) (htb : t.holds lo' hi') (htr : t.holds (lo + lo') (hi + hi'))
    (hd : declOk (.int lo hi) τc = true) :
    StmtCorr X m K (Stmt.plusGleich (V := V) (l := l) x e h1 h2)
      (.set (K.loc x) τc (.bin .add t (.var (K.loc x)) ce)) ∧
      EntscheidZiel.luecke OffeneForm.schrittStmt (.aufListe "++ to += 1; exchange CAS untouched") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.schrittStmt (.aufListe "++ to += 1; exchange CAS untouched")) :=
  ⟨scorr_plusGleich X m K hK x t h1 h2 he hta htb htr hd, schrittStmt_steht⟩

/-- The `syscallStub` row stands decided in the table (data, by `decide`). -/
theorem syscallStub_steht :
    EntscheidZiel.luecke OffeneForm.syscallStub (.aufListe "generated stub; the kernel behind it is the named assumption") ∈ tafel ∧
      entschieden (EntscheidZiel.luecke OffeneForm.syscallStub (.aufListe "generated stub; the kernel behind it is the named assumption")) :=
  ⟨by decide, by decide⟩

/-- Bridge (`syscallStub`): the foreign stub call corresponds under the
    stub assumption, and the row stands. Adapter: the stub is the `.ext`
    call whose assumption shape is `AxCorr`; the kernel behind the stub is
    the named hardware assumption, never a proved premise. -/
theorem bridge_syscallStub (m : Nat) {V : Vertrag D} {l : Bool} (a : D.Ax)
    (args : Args D Γ Λ (D.aparams a)) (h : D.aerg a = none)
    (hw : ∀ t, D.aschreibt a t = true → V.schreibt t = true)
    (hg : ∀ g, D.agschreibt a g = true → V.gschreibt g = true)
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) {n : Nat} {ps : List (Nat × CTy)}
    {Ka : CEnvLay D (D.aparams a)} {cargs : List CX} (hax : AxCorr X.EL X.O X.XR a n ps Ka)
    (hA : ArgsTo X K args cargs ps Ka) :
    StmtCorr X m K (Stmt.axiomCall (l := l) a args h hw hg hd hgd) (.ext n cargs none) ∧
      EntscheidZiel.luecke OffeneForm.syscallStub (.aufListe "generated stub; the kernel behind it is the named assumption") ∈ tafel ∧
        entschieden (EntscheidZiel.luecke OffeneForm.syscallStub (.aufListe "generated stub; the kernel behind it is the named assumption")) :=
  ⟨scorr_axiomCall X K m a args h hw hg hd hgd hax hA, syscallStub_steht⟩

/-
CUTS:
* No adapter from simulation to refusal: the 15 uncovered slots name an
  emitter/checker refusal or a trust item without C evaluation, which no
  evaluation lemma can prove (see the header table).
* No adapter from simulation to table data in the interesting direction:
  every `..._steht` leg is `decide` on `tafel`; the correspondence leg
  cannot prove it and does not need to (`tafel_geschlossen` already
  closes `satz_tafel`). The bridge is adequacy of the price, not proof
  of the row.
* No per-run certificate linkage: binding emitted `/* gabbro-site */`
  markers to `CorrSite` rows is the recomputer's job (cut C1); the
  `markerStimmtB` direction from image to rows is not stated here.
-/

#print axioms Gabbro.Grammatik.logUndOder_steht
#print axioms Gabbro.Grammatik.bridge_logUndOder_und
#print axioms Gabbro.Grammatik.bridge_logUndOder_oder
#print axioms Gabbro.Grammatik.boolLit_steht
#print axioms Gabbro.Grammatik.bridge_boolLit_wahr
#print axioms Gabbro.Grammatik.bridge_boolLit_falsch
#print axioms Gabbro.Grammatik.boolTyp_steht
#print axioms Gabbro.Grammatik.bridge_boolTyp
#print axioms Gabbro.Grammatik.cEnum_steht
#print axioms Gabbro.Grammatik.bridge_cEnum
#print axioms Gabbro.Grammatik.deref_steht
#print axioms Gabbro.Grammatik.bridge_deref
#print axioms Gabbro.Grammatik.bitNicht_steht
#print axioms Gabbro.Grammatik.bridge_bitNicht
#print axioms Gabbro.Grammatik.cSizeof_steht
#print axioms Gabbro.Grammatik.bridge_cSizeof
#print axioms Gabbro.Grammatik.cConst_steht
#print axioms Gabbro.Grammatik.bridge_cConst_lese
#print axioms Gabbro.Grammatik.bridge_cConst_schreib
#print axioms Gabbro.Grammatik.adressVon_steht
#print axioms Gabbro.Grammatik.bridge_adressVon
#print axioms Gabbro.Grammatik.voidTyp_steht
#print axioms Gabbro.Grammatik.bridge_voidTyp
#print axioms Gabbro.Grammatik.bedingt_steht
#print axioms Gabbro.Grammatik.bridge_bedingt
#print axioms Gabbro.Grammatik.zeigerIndex_steht
#print axioms Gabbro.Grammatik.bridge_zeigerIndex
#print axioms Gabbro.Grammatik.pfeilZugriff_steht
#print axioms Gabbro.Grammatik.bridge_pfeilZugriff
#print axioms Gabbro.Grammatik.zusammZuweisung_steht
#print axioms Gabbro.Grammatik.bridge_zusammZuweisung
#print axioms Gabbro.Grammatik.schrittStmt_steht
#print axioms Gabbro.Grammatik.bridge_schrittStmt
#print axioms Gabbro.Grammatik.syscallStub_steht
#print axioms Gabbro.Grammatik.bridge_syscallStub

end Gabbro.Grammatik
