module

public import Grammatik.Parser.Elab.Uebersetze.Teil11

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

namespace USum

/-- Resolve every present payload, preserving case order and absent payloads. A failed
    resolution refuses the whole declaration rather than omitting a field or case. -/
def resolveCases {α β : Type} (resolve : α → Except String β) :
    List (String × Option α) → Except String (List (String × Option β))
  | [] => .ok []
  | (name, none) :: rest =>
    match resolveCases resolve rest with
    | .error e => .error e
    | .ok cs => .ok ((name, none) :: cs)
  | (name, some ty) :: rest =>
    match resolve ty with
    | .error e => .error e
    | .ok value =>
      match resolveCases resolve rest with
      | .error e => .error e
      | .ok cs => .ok ((name, some value) :: cs)

/-- Successful resolution preserves every case name and its payload-presence bit. -/
theorem resolveCases_shape {α β : Type} (resolve : α → Except String β)
    (cs : List (String × Option α)) {out : List (String × Option β)}
    (h : resolveCases resolve cs = .ok out) :
    out.map (fun c => (c.1, c.2.isSome)) = cs.map (fun c => (c.1, c.2.isSome)) := by
  induction cs generalizing out with
  | nil =>
    simp only [resolveCases] at h
    cases h
    rfl
  | cons c cs ih =>
    obtain ⟨name, payload⟩ := c
    cases payload with
    | none =>
      cases hr : resolveCases resolve cs with
      | error e => simp only [resolveCases, hr] at h; cases h
      | ok tail =>
        simp only [resolveCases, hr] at h
        cases h
        exact congrArg (fun xs => (name, false) :: xs) (ih hr)
    | some ty =>
      cases ht : resolve ty with
      | error e => simp only [resolveCases, ht] at h; cases h
      | ok value =>
        cases hr : resolveCases resolve cs with
        | error e => simp only [resolveCases, ht, hr] at h; cases h
        | ok tail =>
          simp only [resolveCases, ht, hr] at h
          cases h
          exact congrArg (fun xs => (name, true) :: xs) (ih hr)

/-- Change the payload representation through one checked resolver. -/
def resolve {α β : Type} (resolvePayload : α → Except String β)
    (schema : USum α) : Except String (USum β) :=
  match resolveCases resolvePayload schema.cases with
  | .error e => .error e
  | .ok cs => .ok { name := schema.name, cases := cs }

theorem resolve_shape {α β : Type} (resolvePayload : α → Except String β)
    (schema : USum α) {out : USum β} (h : schema.resolve resolvePayload = .ok out) :
    out.name = schema.name ∧
      out.cases.map (fun c => (c.1, c.2.isSome)) =
        schema.cases.map (fun c => (c.1, c.2.isSome)) := by
  unfold resolve at h
  cases hr : resolveCases resolvePayload schema.cases with
  | error e => rw [hr] at h; cases h
  | ok cs =>
    rw [hr] at h
    cases h
    exact ⟨rfl, resolveCases_shape resolvePayload schema.cases hr⟩

end USum

/-- Read complete payload types with the canonical parser, including nested groups.
    Reading a schema does not enable its execution as a kernel sum. -/
def uSumFaelle : Nat → List Token → Except String (List (String × Option STyp))
  | 0, _ => .error "tagged type too long"
  | _, [] => .ok []
  | f + 1, .ident n :: .zeichen "," :: rest =>
    match uSumFaelle f rest with
    | .error e => .error e
    | .ok cs => .ok ((n, none) :: cs)
  | _ + 1, [.ident n] => .ok [(n, none)]
  | f + 1, .ident n :: .zeichen "(" :: rest =>
    match parseTyp f rest with
    | .error _ => .error "tagged case without G form"
    | .ok (ty, .zeichen ")" :: rest2) =>
      match rest2 with
      | [] => .ok [(n, some ty)]
      | .zeichen "," :: rest3 =>
        match uSumFaelle f rest3 with
        | .error e => .error e
        | .ok cs => .ok ((n, some ty) :: cs)
      | _ => .error "tagged case without G form"
    | .ok _ => .error "tagged case without G form"
  | _ + 1, _ => .error "tagged case without G form"

/-- Collect tagged declarations before resolving payload types. This retains the complete
    `STyp` tree, including types the current kernel cannot yet carry as sum payloads. -/
def uSumSchemas : List SItemTief → Except String (List (USum STyp))
  | [] => .ok []
  | .typeT ["tagged"] n [] [] (.some (.raw txt)) :: rest =>
    match lex txt with
    | .error _ => .error "tagged type without G form"
    | .ok toks0 =>
      let toks := toks0.filter (fun k => match k with | .ende => false | _ => true)
      match toks with
      | .zeichen "{" :: inner =>
        match inner.reverse with
        | .zeichen "}" :: rev =>
          match uSumFaelle 10000 rev.reverse with
          | .error e => .error e
          | .ok cs =>
            if cs.isEmpty then .error "tagged type without cases"
            else if (cs.map (·.1)).Nodup then
              match uSumSchemas rest with
              | .error e => .error e
              | .ok schemas =>
                if schemas.any (fun s => strEq s.name n) then .error "duplicate tagged type name"
                else .ok ({ name := n, cases := cs } :: schemas)
            else .error "duplicate tagged case name"
        | _ => .error "tagged type without G form"
      | _ => .error "tagged type without G form"
  | .typeT modifiers _ _ _ _ :: rest =>
    if modifiers.any (strEq "tagged") then .error "tagged declaration without G form"
    else uSumSchemas rest
  | _ :: rest => uSumSchemas rest

/-- The current numeric payload gate validates the base before reading its bounds.
    In particular, a range annotation cannot turn a bool, record or unknown name into an integer.
    All numeric names, aliases and bounds still use the canonical result-type reader. -/
def uSumPayload (alias : List (String × (Int × Int))) : STyp → Except String (Int × Int)
  | .atom name => uErgBereich alias (.atom name)
  | ty@(.range base _ _ _) =>
    match uSumPayload alias base with
    | .error e => .error e
    | .ok _ => uErgBereich alias ty
  | ty => .error ("tagged payload without G form: " ++ sTypText ty)

/-- Admission to the current numeric kernel. Typed schemas reach this explicit gate;
    unsupported payloads never become payload-free variants or fabricated ranges. -/
def uSums (alias : List (String × (Int × Int))) (items : List SItemTief) :
    Except String (List USum) :=
  match uSumSchemas items with
  | .error e => .error e
  | .ok schemas => schemas.mapM (USum.resolve (uSumPayload alias))

end Gabbro.Grammatik.Parser.Uebersetze
