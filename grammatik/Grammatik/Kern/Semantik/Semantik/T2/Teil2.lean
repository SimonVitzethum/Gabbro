module

public import Grammatik.Kern.Semantik.Semantik.T1
public import Grammatik.Kern.Semantik.Semantik.T2.Teil1
public import Grammatik.Kern.Syntax.Typen.Fall

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
variable {V : Vertrag D}
variable (P : Programm D) (O : Orakel D)
variable (passes : Nat)
section Rumpf
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

mutual

def execStmt {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Stmt D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .assignSlot t f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignThru p t _ f i e _ _, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ i.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ (eval σ i σ ρ).n f (eval σ e σ ρ)) ρ
  | .assignSlotRef r t _ _ f e _ _, σ, ρ =>
      let σ := σ.lese Λ (r.orte ++ e.orte)
      .ok (σ.schreibSlot t Λ ((eval σ r σ ρ).zelle : Int) f (eval σ e σ ρ)) ρ
  | .assignGlob g e _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .putBytes t f hf n i _ _ e _ _, σ, ρ =>
      let σ := σ.lese Λ (i.orte ++ e.orte)
      .ok (σ.schreibBytes t f hf Λ (eval σ i σ ρ).n (zahlZuBytes n (eval σ e σ ρ).n)) ρ
  | .assignVar x e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok σ (ρ.set x (eval σ e σ ρ))
  | .shift t f hτ i von nach hn _ _ _, σ, ρ =>
      let σ := σ.lese Λ (.inl t :: i.orte)
      let k := (eval σ i σ ρ).n
      if (hτ ▸ σ.slots t k f : Zahl _ _).n = von
      then .ok (σ.schreibSlot t Λ k f (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))) ρ
      else .logik .vorzustand
  | .ite c t e, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlock t σ ρ else execBlock e σ ρ
  | .onOption o p a, σ, ρ =>
      let σ := σ.lese Λ o.orte
      match eval σ o σ ρ with
      | Option.some k => (execBlock p σ (.cons k ρ)).schrumpf
      | Option.none => execBlock a σ ρ
  | .onTag v arms, σ, ρ =>
      let σ := σ.lese Λ v.orte
      execArms arms (eval σ v σ ρ) σ ρ
  | .onWhy r arms, σ, ρ =>
      let σ := σ.lese Λ r.orte
      execGrund arms (eval σ r σ ρ) σ ρ
  | .call f args _ hr, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' _ => .ok σ' ρ
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callInd p args _ hr, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' _ => .ok σ' ρ
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .callIndElse p args he _ hr err, σ, ρ =>
      indSonst R p args he hr (σ.lese Λ (p.orte ++ args.orte)) ρ
        (fun σ' _ => .ok σ' ρ)
        (fun σ' r => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang)
  | .locks L _ body, σ, ρ => (execBlock body (σ.nimmt L) ρ).mapWelt (·.gibt L)
  | .breaking _ body, σ, ρ => execBlock body σ ρ
  | .traverse t inv body, σ, ρ =>
      traverseLauf (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (alleIndizes (D.count t)) σ ρ
  /- C11 consuming traversal: every round selects, in the CURRENT world, the
      least remaining member that is minimal w.r.t. `edge` (`verbrauchSel`
      over `alleIndizes`: first minimal index in ascending order), checks
      `inv`, reads `mass`, and runs `body` on the selected index; the next
      round re-selects in the post-body world. The loop ends when no member
      is left; a cyclic edge with members left, a failed `inv`, and a
      post-body measure that does not strictly fall inside `0 .. bound` are
      the writer's logic (`.logik .schleife`), like a failed `decreases` at
      `traverse`. Fuel bounds the run by the domain size plus the measure
      span; `edge j k` means "`j` precedes `k`" (the candidate is bound
      second). -/
  | .consumeTraverse t member edge inv bound mass body, σ, ρ =>
      verbrauchLauf t (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ)))
        (verbrauchSel t member edge)
        (fun σ ρ => let σ := σ.lese Λ mass.orte; (σ, (eval σ mass σ ρ).n))
        bound ((D.count t).toNat + bound.toNat + 1) σ ρ
  | .retry n bis body ueberlauf, σ, ρ =>
      retryLauf (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ bis.orte; (σ, wahr? (eval σ bis σ ρ)))
        (fun σ ρ => execBlock ueberlauf σ ρ) n σ ρ
  | .forever a inv body, σ, ρ =>
      foreverLauf a (fun σ ρ => execBlock body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ inv.orte; (σ, wahr? (eval σ inv σ ρ))) passes σ ρ
  | .axiomCall a args _ _ _ _ _, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some _) => .ok σ' ρ
      | (_, Option.none) => .hardware (.annahme a)
  | .axiomCallElse _ a args _ _ _ _ _ err, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl _)) => .ok σ' ρ
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | (_, Option.none) => .hardware (.annahme a)
  | .regWrite r _ e, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let _ := O.regSchreib r (roh (eval σ e σ ρ))
      .ok σ ρ
  | .transition r _ m _ _ maske bits, σ, ρ =>
      let σ := σ.fragt (.inr (.inl m))
      let alt := O.regLies m σ
      let _ := O.regSchreib r (((alt.toNat &&& (Nat.xor maske.toNat (2 ^ 64 - 1))) ||| bits.toNat : Nat) : Int)
      .ok σ ρ
  | .publish g e _ _ _ _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .ok (σ.schreibGlob g Λ (eval σ e σ ρ)) ρ
  | .advances _ _ _ _, σ, ρ => .ok σ ρ
  | .retires _ _ _ _, σ, ρ => .ok σ ρ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retWhy r _, σ, _ => .why σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  /- Release crossed scopes innermost first, after evaluating the result. -/
  | .retScoped e cleanup, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck (cleanup.scopes.foldl World.gibt σ) (evalErg σ e σ ρ)
  | .retWhyScoped r cleanup, σ, _ => .why (cleanup.scopes.foldl World.gibt σ) r

def execBlock {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} : Block D V l Γ Λ Λ' → World D → Env D Γ → Ausgang V l Γ
  | .nil, σ, ρ => .ok σ ρ
  | .cons s rest, σ, ρ =>
      match execStmt s σ ρ with
      | .ok σ' ρ' => execBlock rest σ' ρ'
      | o => o
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execBlock rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallIndElse p args he _ hr err rest, σ, ρ =>
      indSonst R p args he hr (σ.lese Λ (p.orte ++ args.orte)) ρ
        (fun σ' v => (execBlock rest σ' (.cons v ρ)).schrumpf)
        (fun σ' r => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang)
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execBlock rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomOpt e a args he _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => Ausgang.weiterOpt e (execBlock rest σ' (ergEnv e (he ▸ v) ρ))
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) =>
          Ausgang.weiterOpt e (execBlock rest σ' (ergEnv e (he ▸ v) ρ))
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf.zuAusgang
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execBlock rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execBlock rest σ (.cons v ρ)).schrumpf
          else (execEnd sonst σ ρ).zuAusgang
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inr g))
      if O.sichtbar g σ then
        let σ := σ.lese Λ [.inr g]
        (execBlock rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := σ.lese Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execBlock rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlock rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else (execEnd sonst σ ρ).zuAusgang
  | .check c sonst rest, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execBlock rest σ ρ else (execEnd sonst σ ρ).zuAusgang
  | .float op a b lo hi rest, σ, ρ =>
      let σ := σ.lese Λ (a.orte ++ b.orte)
      match gleitPasst lo hi (gleitRechne op (eval σ a σ ρ).x (eval σ b σ ρ).x) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatLit q lo hi rest, σ, ρ =>
      match gleitPasst lo hi (bruch q) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatOf e lo hi rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (gleitAusInt (eval σ e σ ρ).n) with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => .logik .bereich
  | .floatNarrow e lo hi sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      match gleitPasst lo hi (eval σ e σ ρ).x with
      | Option.some v => (execBlock rest σ (.cons v ρ)).schrumpf
      | Option.none => (execEnd sonst σ ρ).zuAusgang
  /- C11 required narrowing: in range runs the rest; out of range is the
      appended capacity case of `Logik`, excluded by the caller's duty. -/
  | .narrowRequired e lo' hi' rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execBlock rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else .logik .kapazitaet

def execEnd {l : Bool} {Γ : Ctx} {Λ : List (Res D)} : Endblock D V l Γ Λ → World D → Env D Γ → EndAusgang V l Γ
  | .ret e _, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck σ (evalErg σ e σ ρ)
  | .retWhy r _, σ, _ => .why σ r
  | .leave h, σ, ρ => .leave h σ ρ
  | .next h, σ, ρ => .next h σ ρ
  | .cons s rest, σ, ρ =>
      match execStmt s σ ρ with
      | .ok σ' ρ' => execEnd rest σ' ρ'
      | .zurueck σ' v => .zurueck σ' v
      | .why σ' r => .why σ' r
      | .leave h σ' ρ' => .leave h σ' ρ'
      | .next h σ' ρ' => .next h σ' ρ'
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bind e rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      (execEnd rest σ (.cons (eval σ e σ ρ) ρ)).schrumpf
  | .bindCall f args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why _ r => keinGrund hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallElse f args he _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match R f σ (evalArgs σ args σ ρ) with
      | .ok σ' v => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | .why σ' r => (execEnd err σ' (.cons r ρ)).schrumpf
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindAxiom a args he _ _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomElse a args he _ _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) => (execEnd rest σ' (.cons (ergWert he v) ρ)).schrumpf
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomOpt e a args he _ _ _ rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwort O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some v) => EndAusgang.weiterOpt e (execEnd rest σ' (ergEnv e (he ▸ v) ρ))
      | (_, Option.none) => .hardware (.annahme a)
  | .bindAxiomOptElse e a args he _ _ _ _ err rest, σ, ρ =>
      let σ := σ.lese Λ args.orte
      match axiomAntwortSonst O a σ (evalArgs σ args σ ρ) with
      | (σ', Option.some (Sum.inl v)) =>
          EndAusgang.weiterOpt e (execEnd rest σ' (ergEnv e (he ▸ v) ρ))
      | (σ', Option.some (Sum.inr r)) => (execEnd err σ' (.cons r ρ)).schrumpf
      | (_, Option.none) => .hardware (.annahme a)
  | .regRead r _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          if D.rzusage r v then (execEnd rest σ (.cons v ρ)).schrumpf
          else .hardware (.geraet r)
      | Option.none => .hardware (.register r)
  | .regReadElse r _ zusage sonst rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inl r))
      match einpassen O.zeiger (D.rtyp r) (O.regLies r σ) with
      | Option.some v =>
          let σ := σ.lese Λ zusage.orte
          if wahr? (eval σ zusage σ (.cons v ρ)) then (execEnd rest σ (.cons v ρ)).schrumpf
          else execEnd sonst σ ρ
      | Option.none => .hardware (.register r)
  | .awaits g _ _ _ _ rest, σ, ρ =>
      let σ := σ.fragt (.inr (.inr g))
      if O.sichtbar g σ then
        let σ := σ.lese Λ [.inr g]
        (execEnd rest σ (.cons (σ.globs g) ρ)).schrumpf
      else .hardware (.sichtbarkeit D.a10)
  | .bindCallInd p args he _ hr rest, σ, ρ =>
      let σ := σ.lese Λ (p.orte ++ args.orte)
      let ⟨f, hf⟩ := eval σ p σ ρ
      match R f σ (umsig hf (evalArgs σ args σ ρ)) with
      | .ok σ' v => (execEnd rest σ' (.cons (ergWert (ergSig hf he) v) ρ)).schrumpf
      | .why _ r => keinGrundSig hf hr r
      | .logik e => .logik e
      | .hardware e => .hardware e
  | .bindCallIndElse p args he _ hr err rest, σ, ρ =>
      indSonstE R p args he hr (σ.lese Λ (p.orte ++ args.orte)) ρ
        (fun σ' v => (execEnd rest σ' (.cons v ρ)).schrumpf)
        (fun σ' r => (execEnd err σ' (.cons r ρ)).schrumpf)
  | .narrow e lo' hi' sonst rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execEnd rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else execEnd sonst σ ρ
  | .exchange g neu _ _ rest, σ, ρ =>
      let σ := σ.lese Λ (.inr g :: neu.orte)
      let alt := σ.globs g
      (execEnd rest (σ.schreibGlob g Λ (eval σ neu σ (.cons alt ρ))) (.cons alt ρ)).schrumpf
  | .ite c t e, σ, ρ =>
      let σ := σ.lese Λ c.orte
      if wahr? (eval σ c σ ρ) then execEnd t σ ρ else execEnd e σ ρ
  /- Checked return releases crossed scopes in their recorded order. -/
  | .retScoped e cleanup, σ, ρ =>
      let σ := σ.lese Λ e.orte
      .zurueck (cleanup.scopes.foldl World.gibt σ) (evalErg σ e σ ρ)
  | .retWhyScoped r cleanup, σ, _ => .why (cleanup.scopes.foldl World.gibt σ) r
  /- C11 required narrowing at the top level of a body: in range runs the
      rest; out of range is `Logik.kapazitaet`. -/
  | .narrowRequired e lo' hi' rest, σ, ρ =>
      let σ := σ.lese Λ e.orte
      let v := eval σ e σ ρ
      if h : lo' ≤ v.n ∧ v.n ≤ hi' then (execEnd rest σ (.cons ⟨v.n, h.1, h.2⟩ ρ)).schrumpf
      else .logik .kapazitaet

def execArms {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)} :
    Arms D V l Γ Λ Λ' cs → Wert D (.sum cs) → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨⟨0, _⟩, nutz⟩, σ, ρ => (execBlock b σ (armEnv (Fall.toNutzlast _ _ _ _ nutz) ρ)).schrumpfArm _
  | .cons _ rest, ⟨⟨i + 1, h⟩, nutz⟩, σ, ρ =>
      execArms rest ⟨⟨i, Nat.lt_of_succ_lt_succ h⟩, nutz⟩ σ ρ

def execGrund {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    GrundArms D V l Γ Λ Λ' n → Fin n → World D → Env D Γ → Ausgang V l Γ
  | .cons b _, ⟨0, _⟩, σ, ρ => execBlock b σ ρ
  | .cons _ rest, ⟨i + 1, h⟩, σ, ρ => execGrund rest ⟨i, Nat.lt_of_succ_lt_succ h⟩ σ ρ

end

end Rumpf
end Gabbro.Grammatik
