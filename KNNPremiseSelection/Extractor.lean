import Lean
import Mathlib.Control.Monad.Writer
import KNNPremiseSelection.StatementFeatures
import KNNPremiseSelection.ProofSource

namespace KNNPremiseSelection

open Lean Lean.Elab Lean.Elab.Term Lean.Elab.Command Lean.Meta System

/-- Holds the name, features and premises of a single theorem. -/
structure TheoremPremises where
  name              : Name
  features          : StatementFeatures
  argumentsFeatures : Array StatementFeatures
  premises          : Multiset Name

instance : ToJson TheoremPremises where
  toJson data :=
    Json.mkObj [
      ("name",              toJson data.name),
      ("features",          toJson data.features),
      ("argumentsFeatures", toJson data.argumentsFeatures),
      ("premises",          toJson data.premises)
    ]

instance : ToString TheoremPremises where
  toString := Json.pretty ∘ toJson

/-- Used to choose the feature format: nameCounts and/or bigramCounts and/or
trigramCounts -/
structure FeatureFormat where
  n : Bool := true
  b : Bool := true
  t : Bool := true
deriving Inhabited

/-- Structure to put together all the user options: max expression depth, filter
user premises and feature format. -/
structure UserOptions where
  minDepth : UInt32        := 0
  maxDepth : UInt32        := 255
  noAux    : Bool          := false
  source   : Bool          := false
  math     : Bool          := false
  format   : FeatureFormat := default
deriving Inhabited

/-- Features used for training. All the features (arguments and theorem) should
be put together in a sequence tagged with `T` for theorem or `H` for
hypotheses.  -/
def getFeatures (tp : TheoremPremises) (format : FeatureFormat) : String :=
  Id.run <| do
    let statementF := tp.features
    let argsF := tp.argumentsFeatures
    let mut result : Array String := #[]
    if format.n then
      result := result ++ statementF.nameCounts.toTFeatures ++
        argsF.concatMap (Multiset.toHFeatures ∘ StatementFeatures.nameCounts)
    if format.b then
      result := result ++ statementF.bigramCounts.toTFeatures ++
        argsF.concatMap (Multiset.toHFeatures ∘ StatementFeatures.bigramCounts)
    if format.t then
      result := result ++ statementF.trigramCounts.toTFeatures ++
        argsF.concatMap (Multiset.toHFeatures ∘ StatementFeatures.trigramCounts)
    return " ".intercalate result.data

/-- Premises are simply concatenated. -/
def getLabels (tp : TheoremPremises) : String :=
  let thmName := tp.name.toString
  thmName ++ " : " ++ (" ".intercalate (tp.premises.toList.map toString))

section CoreExtractor

/-- Given a name `n`, if it qualifies as a premise, it returns `[n]`, otherwise
it returns the empty list. -/
private def getTheoremFromName (n : Name) : MetaM (Multiset Name) := do
  -- Get all consts whose type is of type Prop.
  if let some cinfo := (← getEnv).find? n then
    if (← inferType cinfo.type).isProp then
      pure (Multiset.singleton n)
    else
      pure Multiset.empty
  else pure Multiset.empty

private def getTheoremFromExpr (e : Expr) : MetaM (Multiset Name) := do
  if let .const n _ := e then getTheoremFromName n else pure Multiset.empty

private def visitPremise (e : Expr) : WriterT (Multiset Name) MetaM Unit := do
  getTheoremFromExpr e >>= tell

private def extractPremises (e : Expr) : MetaM (Multiset Name) := do
  let ((), premises) ← WriterT.run <| forEachExpr visitPremise e
  pure premises

/-- Given a `ConstantInfo` that holds theorem data, it finds the premises used
in the proof and constructs an object of type `PremisesData` with all. -/
private def extractPremisesFromConstantInfo
  (minDepth : UInt32 := 0) (maxDepth : UInt32 := 255)
  : ConstantInfo → MetaM (Option TheoremPremises)
  | ConstantInfo.thmInfo { name := n, type := ty, value := v, .. } => do
      let (thmFeats, argsFeats) ← getThmAndArgsFeatures ty
      -- Heuristic that can be used to ignore simple theorems and to avoid long
      -- executions for deep theorems.
      if minDepth <= v.approxDepth && v.approxDepth < maxDepth then
        pure <| TheoremPremises.mk n thmFeats argsFeats (← extractPremises v)
      else
        pure none
  | _ => pure none

end CoreExtractor

section Variants

/-- Same as `extractPremisesFromConstantInfo` but take an idenitfier and gets
its information from the environment. -/
def extractPremisesFromId
  (minDepth : UInt32 := 0) (maxDepth : UInt32 := 255) (id : Name)
  : MetaM (Option TheoremPremises) := do
  if let some cinfo := (← getEnv).find? id then
    extractPremisesFromConstantInfo minDepth maxDepth cinfo
  else pure none

/-- Extract and print premises from a single theorem. -/
def extractPremisesFromThm
  (minDepth : UInt32 := 0) (maxDepth : UInt32 := 255) (stx : Syntax)
  : MetaM (Array TheoremPremises) := do
  let mut thmData : Array TheoremPremises := #[]
  for name in ← resolveGlobalConst stx do
    if let some data ← extractPremisesFromId minDepth maxDepth name then
      thmData := thmData.push data
  return thmData

/-- Extract and print premises from all the theorems in the context. -/
def extractPremisesFromCtx (minDepth : UInt32 := 0) (maxDepth : UInt32 := 255)
  : MetaM (Array TheoremPremises) := do
  let mut ctxData : Array TheoremPremises := #[]
  for (_, cinfo) in (← getEnv).constants.toList do
    let data? ← extractPremisesFromConstantInfo minDepth maxDepth cinfo
    if let some data := data? then
      ctxData := ctxData.push data
  return ctxData

end Variants

section FromImports

open IO IO.FS

/-- Given a way to insert `TheoremPremises`, this function goes through all
the theorems in a module, extracts the premises filtering them appropriately
and inserts the resulting data. -/
private def extractPremisesFromModule
  (insert : TheoremPremises → IO Unit)
  (moduleName : Name) (moduleData : ModuleData)
  (minDepth maxDepth : UInt32) (noAux source math : Bool := false)
  : MetaM Unit := do
  dbg_trace s!"Extracting premises from {moduleName}."
  let mut filter : Name → Multiset Name → MetaM (Multiset Name × Bool) :=
    fun _ ns => pure (ns, false)
  -- Source filter.
  if source then
    if let some modulePath ← proofSourcePath moduleName then
      -- If source premises and path found, then create a filter looking at
      -- proof source. If no proof source is found, no filter is applied.
      let data ← IO.FS.readFile modulePath
      let proofsJson :=
        match Json.parse data with
        | Except.ok json => json
        | Except.error _ => Json.null
      filter := fun thmName premises => do
        if let some source ← proofSource thmName proofsJson then
          return (filterUserPremises premises source, true)
        else return (premises, false)
  -- Math-only filter.
  else if math then
    let allNamesPath := "data/math_names"
    filter := fun _ premises => do
      let mut filteredPremises : Multiset Name := ∅
      for (premise, count) in premises do
        let output ← IO.Process.output {
          cmd := "grep",
          args := #["-x", premise.toString, allNamesPath] }
        if output.exitCode == 0 && !output.stdout.isEmpty then
          filteredPremises := filteredPremises.insert premise count
      return (filteredPremises, true)

  -- Go through all theorems in the module, filter premises and write.
  let mut countFoundAndNotEmpty := 0
  let mut countFound := 0
  let mut countTotal := 0
  for cinfo in moduleData.constants do
    -- dbg_trace "for-loop iteration in extractPremisesFromModule (cinfo.name: {cinfo.name})"
    let data? ← extractPremisesFromConstantInfo minDepth maxDepth cinfo
    if let some data := data? then
      countTotal := countTotal + 1
      if countTotal > 1000 then
        throwError "countTotal unacceptably high for module {moduleName}"
      let mut filteredPremises : Multiset Name := ∅
      let (filterResult, found) ← filter data.name data.premises
      filteredPremises := filterResult
      if noAux || source || math then
        filteredPremises ← noAuxFilter filteredPremises
      if !source && !filteredPremises.isEmpty then
        countFoundAndNotEmpty := countFoundAndNotEmpty + 1
        let filteredData := { data with premises := filteredPremises }
        dbg_trace "About to insert filteredData"
        insert filteredData
      if source then
        if found then
          countFound := countFound + 1
        if found && !filteredPremises.isEmpty then
          countFoundAndNotEmpty := countFoundAndNotEmpty + 1
          let filteredData := { data with premises := filteredPremises }
          insert filteredData
  if source then
    dbg_trace s!"Total : {countTotal}"
    dbg_trace s!"Found in source : {countFound}"
    dbg_trace s!"Found and not empty : {countFoundAndNotEmpty}"
  else
    dbg_trace s!"Total : {countTotal}"
    dbg_trace s!"Not empty : {countFoundAndNotEmpty}"
  return ()
  where
    blackList : List String := ["._", "_private.", "_Private."]

    noAuxFilter (premises : Multiset Name) : MetaM (Multiset Name) := do
      let mut result : Multiset Name := ∅
      for (p, c) in premises do
        if !(blackList.any (·.isSubstrOf p.toString)) then
          result := result.insert p c
      return result

/-- Call `extractPremisesFromModule` with an insertion mechanism that writes
to the specified files for labels and features. -/
def extractPremisesFromModuleToFiles
  (moduleName : Name) (moduleData : ModuleData)
  (labelsPath featuresPath : FilePath) (userOptions : UserOptions := default)
  : MetaM Unit := do
  let labelsExists ← labelsPath.pathExists
  let featuresExists ← featuresPath.pathExists
  if labelsExists && featuresExists then
    dbg_trace s!"{labelsPath} and {featuresPath} already exist."
    pure ()
  else
    let labelsHandle ← Handle.mk labelsPath Mode.append
    let featuresHandle ← Handle.mk featuresPath Mode.append

    let insert : TheoremPremises → IO Unit := fun data => do
      labelsHandle.putStrLn (getLabels data)
      featuresHandle.putStrLn (getFeatures data userOptions.format)

    let minDepth := userOptions.minDepth
    let maxDepth := userOptions.maxDepth
    let noAux := userOptions.noAux
    let source := userOptions.source
    let math := userOptions.math
    extractPremisesFromModule
      insert moduleName moduleData minDepth maxDepth noAux source math

/-- Go through the whole module and find the defininions that appear in the
corresponding source file. This was used to generate `math_names`. -/
def extractUserDefinitionsFromModuleToFile
  (moduleName : Name) (moduleData : ModuleData) (outputPath : FilePath)
  : MetaM Unit := do
  let labelsHandle ← Handle.mk outputPath Mode.append
  for cinfo in moduleData.constants do
    if let some modulePath ← pathFromMathlibImport moduleName then
      let args := #[cinfo.name.toString, modulePath.toString]
      let output ← IO.Process.output { cmd := "grep", args := args }
      if output.exitCode == 0 && !output.stdout.isEmpty then
        labelsHandle.putStrLn cinfo.name.toString

/-- Looks through all the meaningful imports and applies
`extractPremisesFromModuleToFiles` to each of them. -/
def extractPremisesFromImportsToFiles
  (labelsPath featuresPath : FilePath) (userOptions : UserOptions := default)
  : MetaM Unit := do
  dbg_trace s!"Extracting premises from imports to {labelsPath}, {featuresPath}."

  let env ← getEnv
  let imports := env.imports.map (·.module)
  let moduleNamesArray := env.header.moduleNames
  let moduleDataArray := env.header.moduleData

  let mut count := 0
  for (moduleName, moduleData) in Array.zip moduleNamesArray moduleDataArray do
    let isMathImport := moduleName.getRoot == `Mathlib
    if imports.contains moduleName && isMathImport then
      count := count + 1
      extractPremisesFromModuleToFiles
        moduleName moduleData labelsPath featuresPath userOptions
      dbg_trace s!"count = {count}."

  pure ()

end FromImports

section Json

def extractPremisesFromCtxJson : MetaM Json :=
  toJson <$> extractPremisesFromCtx

def extractPremisesFromThmJson (stx : Syntax) : MetaM Json :=
  toJson <$> extractPremisesFromThm (stx := stx)

end Json

section Commands

private def runAndPrint [ToJson α] (f : MetaM α) : CommandElabM Unit :=
  liftTermElabM <| do dbg_trace s!"{Json.pretty <| toJson <| ← f}"

elab "extract_premises_from_thm " id:term : command =>
  runAndPrint <| extractPremisesFromThm (stx := id)

elab "extract_premises_from_ctx" : command =>
  runAndPrint <| extractPremisesFromCtx

syntax (name := extract_premises_to_files)
  "extract_premises_to_files" "l:" str "f:" str : command

@[command_elab «extract_premises_to_files»]
unsafe def elabExtractPremisesToFiles : CommandElab
| `(extract_premises_to_files l:$lp f:$fp) => liftTermElabM <| do
  let labelsPath ← evalTerm String (mkConst `String) lp.raw
  let featuresPath ← evalTerm String (mkConst `String) fp.raw
  extractPremisesFromImportsToFiles labelsPath featuresPath
| _ => throwUnsupportedSyntax

end Commands

end KNNPremiseSelection
