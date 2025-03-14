import Lean
import Hammer
import KNNPremiseSelection.Forest
import KNNPremiseSelection.StatementFeatures
import KNNPremiseSelection.Knn
import KNNPremiseSelection.Widget

namespace KNNPremiseSelection

open Lean Meta Elab Tactic Term

initialize registerTraceClass `suggestPremises.debug

def trainedForest :=
  loadFromFile "data/forest.source.nb.small"
  -- loadFromFile "util/train-and-predict-rf.extracted.+all.+n.+b.6745.forest.old"
  -- loadFromFile "util/train-and-predict-rf.extracted.+all.+n.+b.29541.forest"

syntax (name := suggestPremises) "suggest_premises" : tactic
syntax (name := showPremiseList) "show_premise_list" : tactic
syntax (name := createAutoCall) "create_auto_call" : tactic

syntax (name := suggestPremisesKnn) "suggest_premises_knn" : tactic
syntax (name := showPremiseListKnn) "show_premise_list_knn" : tactic
syntax (name := createAutoCallKnn) "create_auto_call_knn" : tactic

def getGoalFeatures : TacticM (List String) := do
  let target ← getMainTarget
  let hyps ← withMainContext <| do
    let mut hyps := []
    let ctx ← getLCtx
    for h in ctx do
      let hyp ← inferType h.type
      hyps := hyps ++ [hyp]
    return hyps

  let targetFeatures ← getStatementFeatures target
  let hypsFeatures ← getArgsFeatures hyps

  let features := Array.toList <| targetFeatures.toTFeatures ++
    hypsFeatures.flatMap StatementFeatures.toHFeatures
  return features

def getGoalFeaturesOfMVarId (m : MVarId) : MetaM (List String) := m.withContext do
  let mType ← inferType $ Expr.mvar m
  let mType ← instantiateMVars mType
  let mut hyps := []
  let ctx ← getLCtx
  for h in ctx do
    let hyp ← inferType h.type
    hyps := hyps ++ [hyp]
  let targetFeatures ← getStatementFeatures mType
  let hypsFeatures ← getArgsFeatures hyps
  let features := Array.toList <| targetFeatures.toTFeatures ++
    hypsFeatures.flatMap StatementFeatures.toHFeatures
  return features

-- Note: Use only lowercase for the names here
def blacklist := [
  "iff.trans",
  "iff.mp", "iff.mpr",
  "eq.trans",
  "eq.symm",
  "rfl",
  "or.elim",
  -- Additional items not part of original blacklist
  "propext",
  "iff.rfl",
  "congrarg",
  "or.caseson", "or.inl", "or.inr",
  "exists.caseson", "exists.intro",
  "funext",
  "iff_self",
  "eq_self",
  "iff.symm", "iff.intro",
  "and.intro", "and.left", "and.right",
  "of_eq_true", "eq_true",
  "eq_false", "eq_false'"
]

def scoreThreshold := 1

@[tactic suggestPremises]
def suggestPremisesTactic : Tactic := fun stx => do
  let features ← getGoalFeatures
  let e := unlabeled features
  let p := rankingWithScores (← trainedForest) e
  let p :=
    p.filter (fun (name, score) => score > scoreThreshold && blacklist.all (· ≠ name.toLower))
  let p : List Item ← p.filterMapM (fun (name, score) => (do
    let name ← KNNPremiseSelection.resolveConst name.toName
    return (some {name, score})
  ) <|> (pure none))
  let p := p.toArray
  saveWidget stx p
  return ()

-- For testing purposes
def whitelist := [
  "sub_le_iff_le_add",
  "sub_add_cancel",
  "abs_add"
]

@[tactic showPremiseList]
def evalShowPremiseList : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  let features ← getGoalFeatures
  let e := unlabeled features
  let p := rankingWithScores (← trainedForest) e
  let p :=
    p.filter (fun (name, score) => score > scoreThreshold && blacklist.all (· ≠ name.toLower)) -- whitelist.contains name)
  let p : List Item ← p.filterMapM (fun (name, score) => (do
    let name ← KNNPremiseSelection.resolveConst name.toName
    return (some {name, score})
  ) <|> (pure none))
  IO.println s!"Item List: {p}"
  IO.println s!"Time to construct item list: {(← IO.monoMsNow) - startTime}ms"
  return ()

@[tactic showPremiseListKnn]
def evalShowPremiseListKnn : Tactic := fun stx => do
  let startTime ← IO.monoMsNow
  let features ← getGoalFeatures
  let train_features_file := "/Users/joshClune/Desktop/lean-premise-selection/data/extracted.+all.+n.+b.train.features"
  let train_labels_file := "/Users/joshClune/Desktop/lean-premise-selection/data/extracted.+all.+n.+b.train.labels"
  IO.println "About to load train_data..."
  let train_data ← loadLabeled train_features_file train_labels_file
  IO.println "Loaded train_data!"
  let p := predictOneWithScore train_data 100 (HashSet.ofList features)
  -- let p := p.filter (fun (name, _) => whitelist.contains name) -- For testing (when I test this, also remove `initSeg` line from Knn.lean)
  IO.println s!"Item List: {p}"
  IO.println s!"Time to construct item list: {(← IO.monoMsNow) - startTime}ms"
  return ()

@[tactic createAutoCall]
def evalCreateAutoCall : Tactic
| `(createAutoCall | create_auto_call%$stxRef) => withMainContext do
  let features ← getGoalFeatures
  let e := unlabeled features
  let p := rankingWithScores (← trainedForest) e
  let p :=
    p.filter (fun (name, score) => score > scoreThreshold && blacklist.all (· ≠ name.toLower))
  let p : List Ident ← p.filterMapM (fun (name, _) => (do
    let name ← KNNPremiseSelection.resolveConst name.toName
    return (some (mkIdent name))
  ) <|> (pure none))
  let pStx : TSyntaxArray ``Auto.hintelem ← p.toArray.mapM (fun ident => `(Auto.hintelem| $ident:term))
  let suggestion ← `(tactic| auto [$pStx,*])
  IO.println s!"Item Ident List: {p}"
  IO.println s!"pStx: {pStx}"
  IO.println s!"suggestion: {suggestion}"
  Lean.Meta.Tactic.TryThis.addSuggestion stxRef suggestion (← getRef) (header := "Try this:\n")
  return ()
| _ => throwUnsupportedSyntax

@[tactic createAutoCallKnn]
def evalCreateAutoCallKnn : Tactic
| `(createAutoCallKnn | create_auto_call_knn%$stxRef) => withMainContext do
  let features ← getGoalFeatures
  let train_features_file := "/Users/joshClune/Desktop/lean-premise-selection/data/extracted.+all.+n.+b.train.features"
  let train_labels_file := "/Users/joshClune/Desktop/lean-premise-selection/data/extracted.+all.+n.+b.train.labels"
  IO.println "About to load train_data..."
  let train_data ← loadLabeled train_features_file train_labels_file
  IO.println "Loaded train_data!"
  let p := predictOne train_data 100 (HashSet.ofList features)
  let p : List Ident ← p.filterMapM (fun name => (do
    if blacklist.all (· ≠ name.toLower) then
      let name ← KNNPremiseSelection.resolveConst name.toName
      return (some (mkIdent name))
    else
      return none
  ) <|> (pure none))
  let pStx : TSyntaxArray ``Auto.hintelem ← p.toArray.mapM (fun ident => `(Auto.hintelem| $ident:term))
  let suggestion ← `(tactic| auto [$pStx,*])
  IO.println s!"Item Ident List: {p}"
  IO.println s!"pStx: {pStx}"
  IO.println s!"suggestion: {suggestion}"
  Lean.Meta.Tactic.TryThis.addSuggestion stxRef suggestion (← getRef) (header := "Try this:\n")
  return ()
| _ => throwUnsupportedSyntax

elab "print_smt_features" : tactic => do
  let t ← getMainTarget
  let hyps_features ← withMainContext (do
    let ctx ← getLCtx
    let mut features : StatementFeatures := ∅
    for h in ctx do
      let p ← inferType h.type
      if p.isProp then
        let fs ← getStatementFeatures h.type
        features := features ++ fs
    return features
  )
  let target_features ← getStatementFeatures t
  let features := hyps_features ++ target_features
  for (⟨n1, n2⟩, count) in features.bigramCounts do
    dbg_trace (s!"{n1}/{n2}", count)

def knnSelector (train_features_file train_labels_file : String) : PremiseSelection.Selector := fun goal config => do
  let maxSuggestions := Option.getD config.maxSuggestions 16
  let features ← getGoalFeaturesOfMVarId goal
  let train_data ← loadLabeled train_features_file train_labels_file
  let p := predictOneWithScore train_data maxSuggestions (HashSet.ofList features)
  let p ← p.filterMapM (fun (name, score) => (do
    if blacklist.all (· ≠ name.toLower) then
      pure $ some ⟨← KNNPremiseSelection.resolveConst name.toName, score⟩
    else
      return none
  ) <|> (pure none))
  return p.toArray

def forestSelector (trainedForestFile : String) : PremiseSelection.Selector := fun goal config => do
  let trainedForest ← loadFromFile trainedForestFile
  let maxSuggestions := Option.getD config.maxSuggestions 16
  let features ← getGoalFeaturesOfMVarId goal
  let e := unlabeled features
  let p := rankingWithScores trainedForest e
  let p :=
    p.filter (fun (name, score) => score > scoreThreshold && blacklist.all (· ≠ name.toLower)) -- whitelist.contains name)
  let p := p.take maxSuggestions
  let p : List PremiseSelection.Suggestion ← p.filterMapM (fun (name, score) => (do
    let name ← KNNPremiseSelection.resolveConst name.toName
    return (some ⟨name, Float.ofInt score⟩)
  ) <|> (pure none))
  return p.toArray

end KNNPremiseSelection
