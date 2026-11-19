module

public import Grammatik.Logik.Invarianten.Frag.Symbolic.Encoding
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Snapshot.Base
public import Grammatik.Logik.Invarianten.Frag.Symbolic.Current

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot

structure Encoding (names : List (Observation D)) (start : Nat) (symbols : SymEnv D Nat Γ)
    (τ : Ty) (value : World D → World D → Env D Γ → Wert D τ) where
  payload : Symbolic.Payload D τ
  correct : ∀ valuation old world actual, Realizes start names valuation old →
    symbols.Realizes valuation world actual →
    Symbolic.Represents valuation world τ payload (value old world actual)

theorem Encoding.bool_iff {symbols : SymEnv D Nat Γ}
    {value : World D → World D → Env D Γ → Wert D .bool}
    (encoded : Encoding names start symbols .bool value)
    (valuation : Assignment Nat) (old world : World D) (actual : Env D Γ)
    (frozen : Realizes start names valuation old) (realized : symbols.Realizes valuation world actual) :
    wahr? (value old world actual) = true ↔ encoded.payload.denote (values valuation world) :=
  encoded.correct valuation old world actual frozen realized

def Encoding.current (encoded : Symbolic.Encoding symbols τ value) :
    Encoding names start symbols τ (fun _ world actual => value world actual) where
  payload := encoded.payload
  correct := fun valuation _ world actual _ realized => encoded.correct valuation world actual realized

def observation (names : List (Observation D)) (start : Nat) (symbols : SymEnv D Nat Γ)
    (τ : Ty) (key : Observation D) (value : World D → Wert D τ)
    (same : ∀ world, assignment world key = scalarValue τ (value world)) :
    Except Refusal (Encoding names start symbols τ (fun old _ _ => value old)) :=
  match found : lookup start names key with
  | none => .error (.outsideFragment "old memory observation has no allocated entry key")
  | some index =>
    match τ, value, same with
    | .int _ _, value, same => .ok {
        payload := .var (.inr index)
        correct := fun valuation old _ _ frozen _ =>
          (lookup_sound names start key index found valuation old frozen).trans (same old) }
    | .str _, value, same => .ok {
        payload := .var (.inr index)
        correct := fun valuation old _ _ frozen _ =>
          (lookup_sound names start key index found valuation old frozen).trans (same old) }
    | .bool, value, same => .ok {
        payload := .eq (.var (.inr index)) (.konst 1)
        correct := fun valuation old _ _ frozen _ => by
          change value old = true ↔ valuation index = 1
          rw [(lookup_sound names start key index found valuation old frozen).trans (same old)]
          cases actual : value old <;> simp [scalarValue, actual, wahr?] <;> rfl }
    | _, _, _ => .error (.unsupported "old memory needs a scalar observation")

def Encoding.constantIndex {symbols : SymEnv D Nat Γ}
    {value : World D → World D → Env D Γ → Wert D (.int lo hi)}
    (encoded : Encoding names start symbols (.int lo hi) value) :
    Except Refusal { index : Int // ∀ valuation old world actual,
      Realizes start names valuation old → symbols.Realizes valuation world actual →
      (value old world actual).n = index } :=
  match found : encoded.payload.constant? with
  | none => .error .crossEntry
  | some index => .ok ⟨index, fun valuation old world actual frozen realized =>
      (encoded.correct valuation old world actual frozen realized).symm.trans
        (LTerm.constant?_sound found (values valuation world))⟩

def concreteEncoding (names : List (Observation D)) (start : Nat)
    (expression : Expr D Γ Λ τ) (symbols : SymEnv D Nat Γ) :
    Except Refusal (Encoding names start symbols τ (fun old world actual => eval old expression world actual)) := do
  let independent ← Vertraege.Pruefer.currentOnly expression
  let encoded ← Symbolic.concreteEncoding expression symbols
  .ok {
    payload := encoded.payload
    correct := fun valuation old world actual _ realized => by
      rw [independent.down old world actual]
      exact encoded.correct valuation world actual realized }

def allEncoding (names : List (Observation D)) (start : Nat) (symbols : SymEnv D Nat Γ)
    (items : List α) (predicate : α → World D → World D → Env D Γ → Bool)
    (compile : ∀ item, Except Refusal (Encoding names start symbols .bool (predicate item))) :
    Except Refusal (Encoding names start symbols .bool (fun old world actual =>
      items.all (fun item => predicate item old world actual))) :=
  match items with
  | [] => .ok { payload := .tru, correct := fun _ _ _ _ _ _ => ⟨fun _ => trivial, fun _ => rfl⟩ }
  | head :: tail => do
      let first ← compile head
      let rest ← allEncoding names start symbols tail predicate compile
      .ok {
        payload := .and first.payload rest.payload
        correct := fun valuation old world actual frozen realized => Bool.and_eq_true_iff.trans (and_congr
          (first.bool_iff valuation old world actual frozen realized)
          (rest.bool_iff valuation old world actual frozen realized)) }

/-- `exists` over a finite index list: the disjunction of the per-item encodings. -/
def anyEncoding (names : List (Observation D)) (start : Nat) (symbols : SymEnv D Nat Γ)
    (items : List α) (predicate : α → World D → World D → Env D Γ → Bool)
    (compile : ∀ item, Except Refusal (Encoding names start symbols .bool (predicate item))) :
    Except Refusal (Encoding names start symbols .bool (fun old world actual =>
      items.any (fun item => predicate item old world actual))) :=
  match items with
  | [] => .ok { payload := .fls, correct := fun _ _ _ _ _ _ => ⟨fun h => Bool.false_ne_true h, fun h => h.elim⟩ }
  | head :: tail => do
      let first ← compile head
      let rest ← anyEncoding names start symbols tail predicate compile
      .ok {
        payload := .or first.payload rest.payload
        correct := fun valuation old world actual frozen realized => Bool.or_eq_true_iff.trans (or_congr
          (first.bool_iff valuation old world actual frozen realized)
          (rest.bool_iff valuation old world actual frozen realized)) }

end Gabbro.Grammatik.Invarianten.Frag.Symbolic.Snapshot
