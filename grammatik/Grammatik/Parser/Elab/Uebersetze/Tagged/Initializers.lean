module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

mutual
/-- A tagged initializer checks payload presence, then uses the canonical typed
    constant reader for the complete selected value. -/
def uSumKonst (consts : List (String × Int)) (sums : List USum) (sm : USum) :
    SKonstWert → Except String UKonst
  | .one (.variable name) =>
    match sm.cases.findIdx? (fun c => strEq c.1 name), sm.cases.find? (fun c => strEq c.1 name) with
    | some i, some (_, none) => .ok (.fall i .null)
    | some _, some (_, some _) => .error "missing tagged payload in static initializer"
    | _, _ => .error ("case unknown: " ++ name)
  | .one (.call name [value]) =>
    match sm.cases.findIdx? (fun c => strEq c.1 name), (sm.cases.find? (fun c => strEq c.1 name)).bind (·.2) with
    | some i, some τ => (uKonst consts sums (some τ) (.one value)).map (.fall i)
    | _, _ => .error "missing or extra tagged payload in static initializer"
  | _ => .error "static initialiser without G form"
termination_by value => 2 * sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals omega
/-- Constants use their declared type throughout nested tagged and array values.
    The later value decoder still checks exact shape, ranges and string bounds. -/
def uKonst (consts : List (String × Int)) (sums : List USum) (expected : Option Ty) :
    SKonstWert → Except String UKonst
  | value =>
    match expected, hvalue : value with
    | some (.sum cs), _ =>
      match sums.find? (fun sm => sm.spec = cs) with
      | some sm => uSumKonst consts sums sm value
      | none => .error "unknown tagged type in static initializer"
    | some (.int lo hi), .one e =>
      match uKonstWert lo hi [] consts 64 e with
      | some z => .ok (.zahl z)
      | none => .error "static initialiser outside its declared range"
    | _, .one (.lit 0) => .ok .null
    | _, .one (.call "None" []) => .ok .null
    | _, .one (.lit k) => .ok (.zahl (Int.ofNat k))
    | _, .one (.un "-" (.lit k)) => .ok (.zahl (-(Int.ofNat k)))
    | _, .one .tru => .ok (.wahr true)
    | _, .one .fls => .ok (.wahr false)
    | _, .one (.variable c) => (uSuch "const" consts c).map .zahl
    | _, .one (.ext .text [text] []) =>
      .ok (.text (text.toUTF8.toList.map (fun b => Int.ofNat b.toNat)))
    | some (.arr element _), .rows ks => uKonstReihe consts sums (some element) ks
    | _, .rows ks => uKonstReihe consts sums none ks
    | _, .one _ => .error "static initialiser without G form"
termination_by value => 2 * sizeOf value + 1
decreasing_by
  all_goals simp_wf
  all_goals dsimp only [value] at hvalue
  all_goals rw [hvalue]
  all_goals simp_wf
  all_goals simp only [wfParam]
  all_goals omega
/-- Read all array elements under their declared element type. -/
def uKonstReihe (consts : List (String × Int)) (sums : List USum) (element : Option Ty) :
    List SKonstWert → Except String UKonst
  | [] => .ok .nil
  | k :: ks =>
    match uKonst consts sums element k, uKonstReihe consts sums element ks with
    | .ok a, .ok r => .ok (.cons a r)
    | .error e, _ | _, .error e => .error e
termination_by values => 2 * sizeOf values
decreasing_by all_goals simp_wf; omega
end

end Gabbro.Grammatik.Parser.Uebersetze
