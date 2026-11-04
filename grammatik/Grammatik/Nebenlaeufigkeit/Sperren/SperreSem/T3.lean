/- Part 3 of 4 of `SperreSem` (split by instrumente/teile/lean-teilen.py; the umbrella `SperreSem.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreSem.T2
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

theorem zErgG_gleich_grund {V : Vertrag D} {l : Bool} {Γ : Ctx} {o : EndAusgang V l Γ}
    {σ : World D} {r : Fin V.gruende} (h : (zErgG o).gleich (.why σ r)) :
    ∃ σ', o = .why σ' r ∧ SG σ' σ := by
  cases o with
  | why σ' r' =>
      obtain ⟨hs, hr⟩ := h
      subst hr
      exact ⟨σ', rfl, hs⟩
  | _ => simp only [ZErgG.gleich, zErgG] at h

/-! ## 3. The frame semantics of every residue, with lock invariants

  `weiterH`/`semH` are `weiterZ`/`semV` (`ZielOrtVollSem.lean`) over
  `execStmtH`; the one new case is the release marker `frei L`, which runs
  the release check `freiH`. -/

section Weiter

variable (S : SperrInv D) (O : Orakel D) (U : Umwelt D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) {V : Vertrag D}

/-- **How a residue continues from an outcome**, with lock invariants. -/
def weiterH : {l : Bool} → {Γ : Ctx} → {Λ : List (Res D)} → GRest D V l Γ Λ →
    Ausgang V l Γ → ZErgG V
  | _, _, _, .ende e, o =>
      match o with
      | .ok σ ρ => zErgG (execEndH S O U passes R e σ ρ)
      | .zurueck σ v => .zurueck σ v
      | .why σ r => .why σ r
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .dann b k, o => weiterH k (laufA (fun σ ρ => execBlockH S O U passes R b σ ρ) o)
  | _, _, _, .schrumpf k, o => weiterH k o.schrumpf
  | _, _, _, .frei L k, o => weiterH k (freiH S L o)
  | _, _, _, .trav _ inv body ks k, o =>
      weiterH k (laufA (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) ks) o)
  | _, _, _, .travRest _ inv body ks k, o =>
      match o with
      | .ok σ ρ =>
          weiterH k (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) ks σ
            ρ.tail)
      | .next _ σ ρ =>
          weiterH k (traverseLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) ks σ
            ρ.tail)
      | .leave _ σ ρ =>
          weiterH k (if (leseB inv σ ρ.tail).2 = true then .ok (leseB inv σ ρ.tail).1 ρ.tail
            else .logik .schleife)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .why σ r => weiterH k (.why σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, Λ, .verbrauch t member edge inv bound mass body rest k, o =>
      weiterH k (laufA (verbrauchLauf t (fun σ ρ => execBlockH S O U passes R body σ ρ)
        (leseB inv) (verbrauchSel t member edge)
        (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n)) bound rest) o)
  | _, _, Λ, .verbrauchRest t member edge inv bound mass body rest vor k, o =>
      match o with
      | .ok σ ρ =>
          let mm := (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n)) σ ρ.tail
          if 0 ≤ mm.2 ∧ mm.2 ≤ bound ∧ mm.2 < vor then
            weiterH k (verbrauchLauf t (fun σ ρ => execBlockH S O U passes R body σ ρ)
              (leseB inv) (verbrauchSel t member edge)
              (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n)) bound rest mm.1 ρ.tail)
          else weiterH k (.logik .schleife)
      | .next _ σ ρ =>
          let mm := (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n)) σ ρ.tail
          if 0 ≤ mm.2 ∧ mm.2 ≤ bound ∧ mm.2 < vor then
            weiterH k (verbrauchLauf t (fun σ ρ => execBlockH S O U passes R body σ ρ)
              (leseB inv) (verbrauchSel t member edge)
              (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n)) bound rest mm.1 ρ.tail)
          else weiterH k (.logik .schleife)
      | .leave _ σ ρ =>
          let mm := (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n)) σ ρ.tail
          if 0 ≤ mm.2 ∧ mm.2 ≤ bound ∧ mm.2 < vor then
            weiterH k (if (leseB inv mm.1 ρ.tail).2 = true then .ok (leseB inv mm.1 ρ.tail).1 ρ.tail
              else .logik .schleife)
          else weiterH k (.logik .schleife)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .why σ r => weiterH k (.why σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, _, .wieder n bis body ueber k, o =>
      weiterH k (laufA (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
        (fun σ ρ => execBlockH S O U passes R ueber σ ρ) n) o)
  | _, _, _, .wiederRest n bis body ueber k, o =>
      match o with
      | .ok σ ρ => weiterH k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB bis)
          (fun σ ρ => execBlockH S O U passes R ueber σ ρ) n σ ρ)
      | .next _ σ ρ => weiterH k (retryLauf (fun σ ρ => execBlockH S O U passes R body σ ρ)
          (leseB bis) (fun σ ρ => execBlockH S O U passes R ueber σ ρ) n σ ρ)
      | .leave _ σ ρ => weiterH k (.ok σ ρ)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .why σ r => weiterH k (.why σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, _, .ewig a n inv body k, o =>
      weiterH k (laufA (foreverLauf a (fun σ ρ => execBlockH S O U passes R body σ ρ) (leseB inv) n) o)
  | _, _, _, .ewigRest a n inv body k, o =>
      match o with
      | .ok σ ρ => weiterH k (foreverLauf a (fun σ ρ => execBlockH S O U passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .next _ σ ρ => weiterH k (foreverLauf a (fun σ ρ => execBlockH S O U passes R body σ ρ)
          (leseB inv) n σ ρ)
      | .leave _ σ ρ => weiterH k (.ok σ ρ)
      | .zurueck σ v => weiterH k (.zurueck σ v)
      | .why σ r => weiterH k (.why σ r)
      | .logik e => weiterH k (.logik e)
      | .hardware e => weiterH k (.hardware e)
  | _, _, _, .wartet _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterH k o
  | _, _, _, .wartetSonst _ _ _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterH k o
  | _, _, _, .abbruch k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterH k o
  | _, _, _, .rueckBereit _ k, o =>
      match o with
      | .ok _ _ => .sonst
      | o => weiterH k o
  | _, _, _, .zurueckgekehrt a, o =>
      match o with
      | .ok σ _ =>
          match a.1 with
          | .inl v => .zurueck σ v
          | .inr r => .why σ r
      | .zurueck σ v => .zurueck σ v
      | .why σ r => .why σ r
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .aufraeumen a remaining, o =>
      match o with
      | .ok σ _ =>
          if scopesInvH S remaining σ then
            let σ := remaining.foldl World.gibt σ
            match a.1 with
            | .inl v => .zurueck σ v
            | .inr r => .why σ r
          else .logik .schleife
      | .zurueck σ v => .zurueck σ v
      | .why σ r => .why σ r
      | .logik e => .logik e
      | _ => .sonst
  | _, _, _, .leer, o =>
      match o with
      | .zurueck σ v => .zurueck σ v
      | .why σ r => .why σ r
      | .logik e => .logik e
      | _ => .sonst

/-- The frame semantics of a residue with lock invariants: run it from `σ`,
    `ρ`. -/
def semH {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (r : GRest D V l Γ Λ) (σ : World D)
    (ρ : Env D Γ) : ZErgG V :=
  weiterH S O U passes R r (.ok σ ρ)

variable {l : Bool} {Γ : Ctx}

theorem execBlockH_cons_laufA {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (σ : World D) (ρ : Env D Γ) :
    execBlockH S O U passes R (.cons s rest) σ ρ =
      laufA (fun σ ρ => execBlockH S O U passes R rest σ ρ) (execStmtH S O U passes R s σ ρ) := by
  simp only [execBlockH]
  cases execStmtH S O U passes R s σ ρ <;> rfl

theorem semH_dann {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann b k) σ ρ =
      weiterH S O U passes R k (execBlockH S O U passes R b σ ρ) := by rfl

theorem semH_dann_cons {Λ Λ' Λ'' : List (Res D)} (s : Stmt D V l Γ Λ Λ')
    (rest : Block D V l Γ Λ' Λ'') (k : GRest D V l Γ Λ'') (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann (.cons s rest) k) σ ρ =
      weiterH S O U passes R (.dann rest k) (execStmtH S O U passes R s σ ρ) := by
  rw [semH_dann, execBlockH_cons_laufA]
  rfl

theorem weiterH_logik : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (e : Logik D), weiterH S O U passes R k (.logik e) = .logik e
  | _, _, _, .ende _, _ => rfl
  | _, _, _, .dann _ k, e => weiterH_logik k e
  | _, _, _, .schrumpf k, e => weiterH_logik k e
  | _, _, _, .frei _ k, e => weiterH_logik k e
  | _, _, _, .trav _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .travRest _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .wieder _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .wiederRest _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .ewig _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .ewigRest _ _ _ _ k, e => weiterH_logik k e
  | _, _, _, .wartet _ k, e => weiterH_logik k e
  | _, _, _, .wartetSonst _ _ _ k, e => weiterH_logik k e
  | _, _, _, .abbruch k, e => weiterH_logik k e
  | _, _, _, .rueckBereit _ k, e => weiterH_logik k e
  | _, _, _, .zurueckgekehrt _, e => rfl
  | _, _, _, .aufraeumen _ _, e => rfl
  | _, _, _, .leer, _ => rfl

theorem weiterH_zurueck : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (v : ErgVal D V.erg),
    (weiterH S O U passes R k (.zurueck σ v)).gleich (.zurueck σ v)
  | _, _, _, .ende _, _, _ => ZErgG.gleich_refl _
  | _, _, _, .dann _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .schrumpf k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .frei _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .trav _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .travRest _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wieder _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wiederRest _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .ewig _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .ewigRest _ _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wartet _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .wartetSonst _ _ _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .abbruch k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .rueckBereit _ k, σ, v => weiterH_zurueck k σ v
  | _, _, _, .zurueckgekehrt _, σ, v => ZErgG.gleich_refl _
  | _, _, _, .aufraeumen _ _, σ, v => ZErgG.gleich_refl _
  | _, _, _, .leer, _, _ => ZErgG.gleich_refl _

/-- A reason exit passes every residue unchanged up to the trace (the twin
    of `weiterH_zurueck`, 2026-09-14). -/
theorem weiterH_grund : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (k : GRest D V l Γ Λ)
    (σ : World D) (r : Fin V.gruende),
    (weiterH S O U passes R k (.why σ r)).gleich (.why σ r)
  | _, _, _, .ende _, _, _ => ZErgG.gleich_refl _
  | _, _, _, .dann _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .schrumpf k, σ, r => weiterH_grund k σ r
  | _, _, _, .frei _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .trav _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .travRest _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .verbrauch _ _ _ _ _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .verbrauchRest _ _ _ _ _ _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .wieder _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .wiederRest _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .ewig _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .ewigRest _ _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .wartet _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .wartetSonst _ _ _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .abbruch k, σ, r => weiterH_grund k σ r
  | _, _, _, .rueckBereit _ k, σ, r => weiterH_grund k σ r
  | _, _, _, .zurueckgekehrt _, σ, r => ZErgG.gleich_refl _
  | _, _, _, .aufraeumen _ _, σ, r => ZErgG.gleich_refl _
  | _, _, _, .leer, _, _ => ZErgG.gleich_refl _

/-- **An end block replacing a residue** (as `weiterZ_ende_folgt`). -/
theorem weiterH_ende_folgt {Λ : List (Res D)} (k : GRest D V l Γ Λ) (eo : EndAusgang V l Γ) :
    (weiterH S O U passes R k eo.zuAusgang).folgt (zErgG eo) := by
  cases eo with
  | zurueck σ v => exact ZErgG.folgt_of_gleich (weiterH_zurueck S O U passes R k σ v)
  | why σ r => exact ZErgG.folgt_of_gleich (weiterH_grund S O U passes R k σ r)
  | logik e => exact ZErgG.folgt_of_eq (weiterH_logik S O U passes R k e)
  | _ => exact ZErgG.folgt_sonst _

theorem EndAusgang.weiterOpt_zu {l : Bool} {Γ : Ctx} (e : Option Ty)
    (o : EndAusgang V l (ErgCtx Γ e)) :
    Ausgang.weiterOpt e o.zuAusgang = (EndAusgang.weiterOpt e o).zuAusgang := by
  cases e with
  | none => rfl
  | some τ => cases o <;> rfl

/-- `execBlockH` of an end block run as a block (`Endblock.alsBlock`) is
    the end block's own outcome (as `Endblock.execBlock_alsBlock`). -/
theorem Endblock.execBlockH_alsBlock :
    ∀ {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ),
      execBlockH S O U passes R e.alsBlock.2 σ ρ = (execEndH S O U passes R e σ ρ).zuAusgang
  | _, _, .ret _ _, _, _ => rfl
  | _, _, .retWhy _ _, _, _ => rfl
  | _, Λ, .retScoped e R, σ, _ => by
      by_cases h : scopesInvH S R.scopes (σ.lese Λ e.orte) = true
      · simp only [Endblock.alsBlock, execBlockH, execStmtH, execEndH, h, if_true]; rfl
      · simp only [Endblock.alsBlock, execBlockH, execStmtH, execEndH, h, if_false]; rfl
  | _, Λ, .retWhyScoped r R, σ, _ => by
      by_cases h : scopesInvH S R.scopes σ = true
      · simp only [Endblock.alsBlock, execBlockH, execStmtH, execEndH, h, if_true]; rfl
      · simp only [Endblock.alsBlock, execBlockH, execStmtH, execEndH, h, if_false]; rfl
  | _, _, .leave _, _, _ => rfl
  | _, _, .next _, _, _ => rfl
  | _, _, .cons s rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      cases execStmtH S O U passes R s σ ρ with
      | ok σ' ρ' => exact Endblock.execBlockH_alsBlock rest σ' ρ'
      | _ => rfl
  | _, _, .bind e rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      rw [Endblock.execBlockH_alsBlock rest]
      cases execEndH S O U passes R rest _ _ <;> rfl
  | _, _, .bindCall f args he hp hr rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rename_i r _
        exact (Fin.cast hr r).elim0
      · rfl
      · rfl
  | _, _, .bindCallElse f args he hp hr err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · cases execEndH S O U passes R err _ _ <;> rfl
      · rfl
      · rfl
  | _, _, .bindAxiom a args he hw hg hd hgd rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindAxiomElse a args he hr hw hg hd hgd err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · cases execEndH S O U passes R err _ _ <;> rfl
      · rfl
  | _, _, .bindAxiomOpt e a args he _ _ _ rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        exact EndAusgang.weiterOpt_zu e _
      · rfl
  | _, _, .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        exact EndAusgang.weiterOpt_zu e _
      · cases execEndH S O U passes R err _ _ <;> rfl
      · rfl
  | _, _, .regRead r hk rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · split
        · rw [Endblock.execBlockH_alsBlock rest]
          cases execEndH S O U passes R rest _ _ <;> rfl
        · rfl
      · rfl
  | _, _, .regReadElse r hk z sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · split
        · rw [Endblock.execBlockH_alsBlock rest]
          cases execEndH S O U passes R rest _ _ <;> rfl
        · rfl
      · rfl
  | _, _, .awaits g pl hp hL hat rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .bindCallInd p args he hp hr rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      rename_i f hf _
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rename_i r _
        exact keinGrundSig hf hr r
      · rfl
      · rfl
  | _, _, .bindCallIndElse p args he hp hr err rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH, indSonst, indSonstE]
      split
      rename_i f hf _
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · cases execEndH S O U passes R err _ _ <;> rfl
      · rfl
      · rfl
  | _, _, .narrow e lo' hi' sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .narrowRequired e lo' hi' rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .exchange g neu hw hL rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      rw [Endblock.execBlockH_alsBlock rest]
      cases execEndH S O U passes R rest _ _ <;> rfl
  | _, _, .ite c t e, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · exact Endblock.execBlockH_alsBlock t _ _
      · rfl

  | _, _, .float op a b lo hi rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .floatLit q lo hi rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .floatOf e lo hi rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl
  | _, _, .floatNarrow e lo hi sonst rest, σ, ρ => by
      simp only [Endblock.alsBlock, execBlockH, execEndH]
      split
      · rw [Endblock.execBlockH_alsBlock rest]
        cases execEndH S O U passes R rest _ _ <;> rfl
      · rfl

/-- Past `abbruch`, an end outcome continues as without it. -/
theorem weiterH_abbruch_zu {Λ Λk : List (Res D)} (k : GRest D V l Γ Λk) (eo : EndAusgang V l Γ) :
    weiterH S O U passes R (.abbruch (Λ := Λ) k) eo.zuAusgang =
      weiterH S O U passes R k eo.zuAusgang := by
  cases eo <;> rfl

/-- **The residue of an `else` branch** (`.dann e.alsBlock.2 (.abbruch k)`)
    means the end block's outcome continued by `k`: a `leave`/`next` in
    it reaches the loop in `k`. -/
theorem semH_alsBlock {Λ Λk : List (Res D)} (e : Endblock D V l Γ Λ) (k : GRest D V l Γ Λk)
    (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.dann e.alsBlock.2 (.abbruch k)) σ ρ =
      weiterH S O U passes R k (execEndH S O U passes R e σ ρ).zuAusgang := by
  rw [semH_dann, Endblock.execBlockH_alsBlock, weiterH_abbruch_zu]

/-- The base of the `endeForm` continuation passes an end outcome on as it is. -/
theorem weiterH_leer_zu {Λ : List (Res D)} (eo : EndAusgang V l Γ) :
    weiterH S O U passes R (.leer (Λ := Λ)) eo.zuAusgang = zErgG eo := by
  cases eo <;> rfl

/-- **An end block unfolded into block position** (`endeForm`) means the end block. -/
theorem semH_endeForm {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (σ : World D) (ρ : Env D Γ) :
    semH S O U passes R (.ende e) σ ρ =
      semH S O U passes R (.dann e.alsBlock.2 (.abbruch (Λk := Λ) .leer)) σ ρ := by
  rw [semH_alsBlock, weiterH_leer_zu]
  rfl

/-- `execArmsH` runs the arm `armWahlG` selects. -/
theorem execArmsH_wahl {Λ Λ' : List (Res D)} :
    ∀ {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs) (v : Wert D (.sum cs))
      (σ : World D) (ρ : Env D Γ),
    execArmsH S O U passes R arms v σ ρ =
      (execBlockH S O U passes R (armWahlG arms v).2.1 σ
        (armEnv (armWahlG arms v).2.2 ρ)).schrumpfArm (armWahlG arms v).1
  | _, .nil, ⟨⟨k, hk⟩, _⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨⟨0, _⟩, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨⟨n + 1, h⟩, nutz⟩, σ, ρ => by
      simp only [execArmsH, armWahlG]
      exact execArmsH_wahl rest _ σ ρ

/-- `execGrundH` runs the arm `grundWahlG` selects. -/
theorem execGrundH_wahl {Λ Λ' : List (Res D)} :
    ∀ {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n) (r : Fin n) (σ : World D) (ρ : Env D Γ),
    execGrundH S O U passes R arms r σ ρ = execBlockH S O U passes R (grundWahlG arms r) σ ρ
  | _, .nil, ⟨k, hk⟩, _, _ => (Nat.not_lt_zero k hk).elim
  | _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _, .cons _ rest, ⟨k + 1, h⟩, σ, ρ => by
      simp only [execGrundH, grundWahlG]
      exact execGrundH_wahl rest _ σ ρ

theorem execGrundH_wahlW {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n)
    (r : Wert D (.why n)) (σ : World D) (ρ : Env D Γ) :
    execGrundH S O U passes R arms r σ ρ = execBlockH S O U passes R (grundWahlG arms r) σ ρ :=
  execGrundH_wahl S O U passes R arms r σ ρ

end Weiter
/-! ## 4. The residue step lemmas, one per rule of G -/


end Gabbro.Grammatik
