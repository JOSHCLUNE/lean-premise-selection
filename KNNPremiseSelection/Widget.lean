import Lean

open Lean Elab Tactic Widget Server

def Array.chooseM [Alternative m] [Monad m] (f : α → m β) (xs : Array α) : m (Array β) := do
  let mut acc := #[]
  for x in xs do
    if let some y ← optional <| f x then
      acc := acc.push y
  return acc


namespace KNNPremiseSelection

/-
@[widget_module]
def premiseSelectionWidget : UserWidgetDefinition := {
  name := "Premise Selection"
  javascript := include_str ".." / "widget" / "dist" / "index.js"
}
-/

structure Item where
  name : Name
  score : Int
  deriving ToJson, FromJson, Inhabited

def itemToString : Item → String
  | ⟨n, s⟩ => s!"({n}, {s})"

def itemToMessageData : Item → MessageData
  | ⟨n, s⟩ => m!"({n}, {s})"


instance : ToString Item := ⟨itemToString⟩

instance : ToMessageData Item := ⟨itemToMessageData⟩

structure WidgetProps where
  items : Array Item
  stx : Lsp.Range
  uri: Lsp.DocumentUri
  deriving ToJson, FromJson, Inhabited

inductive ItemResult where
  | error (cmd? : Option String) (error : String)
  | noChange (cmd : String)
  | change (cmd : String) (target : CodeWithInfos)
  | done (cmd : String)
  deriving RpcEncodable, Inhabited

structure ItemData extends Item where
  expr? : Option CodeWithInfos := none
  error?: Option String := none
  result? : Option ItemResult := none
  deriving RpcEncodable, Inhabited

structure GetItemArgs where
  item : Item
  pos : Lean.Lsp.Position
  deriving ToJson, FromJson, Inhabited

instance : Alternative RequestM where
  failure _ := throw <| RequestError.internalError "failure"
  orElse a b c := OrElse.orElse (a c) (fun _ => b () c)

def mkFun (constName : Name) : MetaM (Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => Lean.Meta.mkFreshLevelMVar
  let f := mkConst constName us
  return f

def mapRoot (f : Name → Name) : Name → Name
  | .anonymous             => .anonymous
  | n@(.str .anonymous _) => f n
  | n@(.num .anonymous _) => f n
  | .str n x             => .str (mapRoot f n) x
  | .num n x             => .num (mapRoot f n) x

/-- Some of the suggestions don't have their names capitalised.
This is a temporary hack to try capitalising.
-/
def capitalizeFirstLetter : Name → Name :=
  mapRoot .capitalize



def createPPConst (n : Name) : MetaM (Name × CodeWithInfos) := do
  let e ← mkFun n
  let p ← ppExprTagged e
  return (n,p)

def ors [Alternative M] : (xs : List (M α))  → M α
  | [] => failure
  | (h :: t) => h <|> (ors t)

def createConst (n : Name): MetaM Name := do
  let _ ← mkFun n
  return n

def resolveConst (n : Name) : MetaM Name :=
  [n, capitalizeFirstLetter n] |>.map createConst |> ors

def tryApply (n : Name): TacticM (TSyntax `tactic) := do
  let ident := mkIdent n
  let s ← `(tactic| apply $ident)
  evalTactic s
  return s

def trySimp (n : Name) : TacticM (TSyntax `tactic) := do
  let ident := mkIdent n
  let s ← `(tactic| simp only [$ident:term])
  -- annoying UX: really hard to discover that the ':term' needed to be added on above line.
  evalTactic s
  return s



def tryRw (n : Name) : TacticM (TSyntax `tactic) := do
  let ident := mkIdent n
  let s ← `(tactic| rw [$ident:term])
  -- annoying UX: really hard to discover that the ':term' needed to be added on above line.
  evalTactic s
  return s


def isDone : TacticM Bool := do
  let gs ← Tactic.getUnsolvedGoals
  return gs.isEmpty

def trySimps (ns : Array Name) : TacticM (TSyntax `tactic) := do
  let idents := ns.map mkIdent
  let s ← `(tactic| simp only  [ $[$idents:term],* ])
  evalTactic s
  guard (← isDone)
  return s

def innerTryItem (item : Item) : TacticM ItemData := do
    let n := item.name
    let (n, ppc) ← createPPConst n
    try
      let targ ← Tactic.getMainTarget
      let s ← (tryApply n) <|> (tryRw n) <|> (trySimp n )
      let ppt ← Lean.PrettyPrinter.ppTactic s
      let cmd := ppt.pretty
      let result : ItemResult ← (do
        if ← isDone then
          return ItemResult.done cmd
        else
          let result ← Tactic.getMainTarget
          if result == targ then
            return ItemResult.noChange cmd
          let result ← ppExprTagged result
          return ItemResult.change cmd result)
      return {item with name := n, expr? := ppc, result? := some result}
    catch
      e =>
        let msg ← e.toMessageData.toString
        return {item with name := n, expr? := ppc, result? := some <| ItemResult.error none msg}

def tryItem (item : Item) : TacticM ItemData := do
  try
    innerTryItem item
  catch
    e =>
      let msg ← e.toMessageData.toString
      return {item with error? := some msg}

def withLctx (g : MVarId) (m : MetaM α): MetaM α := do
    let some mvarDecl := (← getMCtx).findDecl? g
      | throwError "unknown goal {g.name}"
    let lctx := mvarDecl.lctx
    let lctx := lctx.sanitizeNames.run' { options := (← getOptions) }
    Meta.withLCtx lctx mvarDecl.localInstances m


def runTacticM (snap : Snapshots.Snapshot) (goals : GoalsAtResult) (t : TacticM α) : RequestM α := do
  let rc ← readThe RequestContext
  let { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter, .. } := goals
  let mctx := if useAfter then ti.mctxAfter else ti.mctxBefore
  let gs := if useAfter then ti.goalsAfter else ti.goalsBefore
  let g1 := gs[0]!
  let (e, _) ←
    t
    |>.run {elaborator := .anonymous}
    |>.run { goals := gs }
    |>.run'
    |> withLctx g1
    |>.run' {} {mctx := mctx}
    |> snap.runCoreM rc.doc.meta
    -- omg
  return e


open Lean Server RequestM in
@[server_rpc_method]
def getItem (args : GetItemArgs) : RequestM (RequestTask (ItemData)) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos args.pos
  withWaitFindSnapAtPos args.pos fun snap => do
    let g :: _ := snap.infoTree.goalsAt? doc.meta.text pos
      | throw <| RequestError.internalError "no goals"
    runTacticM snap g (do
      try
          tryItem args.item
      catch
        | e =>
          let msg ← e.toMessageData.toString
          return {args.item with error? := some msg}
    )

def syntaxToLspRange [MonadFileMap M] [Monad M] (stx : Syntax): M Lsp.Range := do
  let fm ← getFileMap
  let pos    := stx.getPos?.getD 0 |> fm.utf8PosToLspPos
  let endPos := (fm.utf8PosToLspPos <$> stx.getTailPos?) |>.getD pos
  return Lsp.Range.mk pos endPos


def saveWidget (stx : Syntax) (xs : Array Item) : TacticM Unit := do
  let fn ← getFileName
  let uri := System.Uri.pathToUri fn
  let r : Lsp.Range ← syntaxToLspRange stx
  let ps : WidgetProps := {items := xs, stx := r, uri}
  throwError "saveWidget not updated"
  -- savePanelWidgetInfo `PremiseSelection.premiseSelectionWidget (toJson ps) stx
  -- return ()

end KNNPremiseSelection
