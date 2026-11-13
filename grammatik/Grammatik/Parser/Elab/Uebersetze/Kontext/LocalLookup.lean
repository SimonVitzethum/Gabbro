module
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil3
@[expose] public section
namespace Gabbro.Grammatik.Parser.Uebersetze

private theorem param_find (names : List String) (p : String) (k : Nat) :
    uParamNrAux names k p =
      match names.findIdx? (strEq · p) with
      | none => .error ("name unknown: " ++ p)
      | some j => .ok (k + j) := by
  induction names generalizing k with
  | nil => rfl
  | cons name names ih =>
    rw [uParamNrAux, List.findIdx?_cons]
    cases same : strEq name p with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, if_false, ih]
      cases names.findIdx? (strEq · p) with
      | none => rfl
      | some j => simp only [Option.map_some]; congr 1; omega

def uParamNrFast (ctx : UCtx) (p : String) : Except String Nat :=
  readMemo (α := String) ctx.lookupMemo (fun memo => memo.names.names) ctx.names
    (fun memo _ => match memo.names.find p with
      | none => .error ("name unknown: " ++ p)
      | some j => .ok j)
    (fun _ => uParamNrAux ctx.names 0 p) (by
      intro memo same
      rw [Tafel.Positions.find, same, param_find]
      cases ctx.names.findIdx? (strEq · p) <;> simp only [Nat.zero_add] <;> rfl)

@[csimp] theorem uParamNr_eq_fast : @uParamNr = @uParamNrFast := by
  funext ctx p
  show _ = readMemo (α := String) _ _ _ _ _ _
  rw [readMemo_eq]
  rfl

@[reducible] def uLocalPosition (ctx : UCtx) (name : String) : Option Nat :=
  ctx.names.findIdx? (strEq · name)

def uLocalPositionFast (ctx : UCtx) (name : String) : Option Nat :=
  readMemo (α := String) ctx.lookupMemo (fun memo => memo.names.names) ctx.names
    (fun memo _ => memo.names.find name) (fun _ => ctx.names.findIdx? (strEq · name))
    (by intro memo same; rw [Tafel.Positions.find, same])

@[csimp] theorem uLocalPosition_eq_fast : @uLocalPosition = @uLocalPositionFast := by
  funext ctx name
  show _ = readMemo (α := String) _ _ _ _ _ _
  rw [readMemo_eq]

/-- Specification projections retain their old list definitions. -/
@[reducible] def uLocalCount (ctx : UCtx) : Nat := ctx.names.length

def uLocalCountFast (ctx : UCtx) : Nat :=
  readMemo (α := String) ctx.lookupMemo (fun memo => memo.names.names) ctx.names
    (fun memo _ => memo.names.size) (fun _ => ctx.names.length) (by
      intro memo same
      rw [memo.names.size_eq, same])

@[csimp] theorem uLocalCount_eq_fast : @uLocalCount = @uLocalCountFast := by
  funext ctx
  show _ = readMemo (α := String) _ _ _ _ _ _
  rw [readMemo_eq]

@[reducible] def uKindAt (ctx : UCtx) (j : Nat) : Except String UParamArt :=
  uArtBei ctx.kinds j

private theorem kind_get (kinds : List UParamArt) (j : Nat) :
    uArtBei kinds j = match kinds[j]? with
      | none => .error "parameter outside"
      | some kind => .ok kind := by
  induction kinds generalizing j with
  | nil => rfl
  | cons kind kinds ih => cases j with
    | zero => rfl
    | succ j => exact ih j

def uKindAtFast (ctx : UCtx) (j : Nat) : Except String UParamArt :=
  readMemo (α := UParamArt) ctx.lookupMemo (fun memo => memo.kinds.liste) ctx.kinds
    (fun memo _ => match Tafel.Stack.get (α := UParamArt) memo.kinds j with
      | none => .error "parameter outside"
      | some kind => .ok kind)
    (fun _ => uArtBei ctx.kinds j) (by
      intro memo same
      rw [Tafel.Stack.get, same, kind_get]
      rfl)

@[csimp] theorem uKindAt_eq_fast : @uKindAt = @uKindAtFast := by
  funext ctx j
  show _ = readMemo (α := UParamArt) _ _ _ _ _ _
  rw [readMemo_eq]

@[reducible] def uTypeAt (ctx : UCtx) (j : Nat) : Option Ty := ctx.types[j]?

def uTypeAtFast (ctx : UCtx) (j : Nat) : Option Ty :=
  readMemo (α := Ty) ctx.lookupMemo (fun memo => memo.types.liste) ctx.types
    (fun memo _ => Tafel.Stack.get (α := Ty) memo.types j) (fun _ => ctx.types[j]?) (by
      intro memo same
      rw [Tafel.Stack.get, same])

@[csimp] theorem uTypeAt_eq_fast : @uTypeAt = @uTypeAtFast := by
  funext ctx j
  show _ = readMemo (α := Ty) _ _ _ _ _ _
  rw [readMemo_eq]

/-- Replacing a cache cannot change a context, including contexts returned by elaboration. -/
theorem UCtx.memo_eq (ctx : UCtx) (memo : Merk ULookupMemo) :
    {ctx with lookupMemo := memo} = ctx := by
  have same : memo = ctx.lookupMemo := Merk.gleich _ _
  rw [same]

/-- Persist the three stacks across a binding. Arbitrary record updates are validated
    separately for each list, so a changed type never reuses old type information. -/
def UCtx.pushMemo (ctx after : UCtx) (name : String) (kind : UParamArt) (ty : Ty)
    (names : after.names = name :: ctx.names) (kinds : after.kinds = kind :: ctx.kinds)
    (types : after.types = ty :: ctx.types) : Merk ULookupMemo :=
  ctx.lookupMemo.map fun memo =>
    let ns := Tafel.Positions.cons name (Tafel.Positions.fit ctx.names memo.names)
    let ks := Tafel.Stack.cons (α := UParamArt) kind
      (Tafel.Stack.fit (α := UParamArt) ctx.kinds memo.kinds)
    let ts := Tafel.Stack.cons (α := Ty) ty (Tafel.Stack.fit (α := Ty) ctx.types memo.types)
    { memo with
      names := ns.rebase after.names (by
        change after.names = name :: (Tafel.Positions.fit ctx.names memo.names).names
        rw [names, Tafel.Positions.fit_names])
      kinds := Tafel.Stack.rebase (α := UParamArt) ks after.kinds (by
        change after.kinds = kind :: (Tafel.Stack.fit (α := UParamArt) ctx.kinds memo.kinds).liste
        rw [kinds, Tafel.Stack.fit_liste])
      types := Tafel.Stack.rebase (α := Ty) ts after.types (by
        change after.types = ty :: (Tafel.Stack.fit (α := Ty) ctx.types memo.types).liste
        rw [types, Tafel.Stack.fit_liste]) }

def UCtx.cacheBinding (ctx after : UCtx) (name : String) (kind : UParamArt) (ty : Ty)
    (names : after.names = name :: ctx.names) (kinds : after.kinds = kind :: ctx.kinds)
    (types : after.types = ty :: ctx.types) : UCtx :=
  {after with lookupMemo := ctx.pushMemo after name kind ty names kinds types}

theorem UCtx.cacheBinding_eq (ctx after : UCtx) (name : String) (kind : UParamArt) (ty : Ty)
    (names : after.names = name :: ctx.names) (kinds : after.kinds = kind :: ctx.kinds)
    (types : after.types = ty :: ctx.types) :
    ctx.cacheBinding after name kind ty names kinds types = after :=
  after.memo_eq _

def UCtx.headMemo (ctx : UCtx) : Merk UHeadMemo :=
  ctx.lookupMemo.lies (fun memo => memo.heads) (fun _ _ => Merk.gleich _ _)

@[reducible] def uHeadFind (_ctx : UCtx) (heads : List UFnKopf) (name : String) : Option UFnKopf :=
  heads.find? (fun head => strEq head.name name)

def uHeadFindFast (ctx : UCtx) (heads : List UFnKopf) (name : String) : Option UFnKopf :=
  readMemo (α := UFnKopf) ctx.headMemo UHeadMemo.heads heads
    (fun memo _ => memo.table.tafel.finde name) (fun _ => heads.find? (fun head => strEq head.name name))
    (by intro memo same; rw [memo.table.finde_eq, same])

@[csimp] theorem uHeadFind_eq_fast : @uHeadFind = @uHeadFindFast := by
  funext ctx heads name
  show _ = readMemo (α := UFnKopf) _ _ _ _ _ _
  rw [readMemo_eq]

@[reducible] def uHeadAt (_ctx : UCtx) (heads : List UFnKopf) (j : Nat) : Option UFnKopf := heads[j]?

def uHeadAtFast (ctx : UCtx) (heads : List UFnKopf) (j : Nat) : Option UFnKopf :=
  readMemo (α := UFnKopf) ctx.headMemo UHeadMemo.heads heads
    (fun memo _ => memo.array[j]?) (fun _ => heads[j]?)
    (by intro memo same; rw [memo.array_eq, same, List.getElem?_toArray])

@[csimp] theorem uHeadAt_eq_fast : @uHeadAt = @uHeadAtFast := by
  funext ctx heads j
  show _ = readMemo (α := UFnKopf) _ _ _ _ _ _
  rw [readMemo_eq]

@[reducible] def uHeadPosition (_ctx : UCtx) (heads : List UFnKopf) (name : String) : Option Nat :=
  heads.findIdx? (fun head => strEq head.name name)

def uHeadPositionFast (ctx : UCtx) (heads : List UFnKopf) (name : String) : Option Nat :=
  readMemo (α := UFnKopf) ctx.headMemo UHeadMemo.heads heads
    (fun memo _ => memo.positions.find name)
    (fun _ => heads.findIdx? (fun head => strEq head.name name)) (by
      intro memo same
      rw [Tafel.Positions.find, memo.positions_eq, same, List.findIdx?_map]
      rfl)

@[csimp] theorem uHeadPosition_eq_fast : @uHeadPosition = @uHeadPositionFast := by
  funext ctx heads name
  show _ = readMemo (α := UFnKopf) _ _ _ _ _ _
  rw [readMemo_eq]

end Gabbro.Grammatik.Parser.Uebersetze
