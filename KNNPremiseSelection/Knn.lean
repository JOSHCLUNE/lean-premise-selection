import KNNPremiseSelection.Utils
import KNNPremiseSelection.Data

namespace KNNPremiseSelection

open Batteries

def similarity (fCounts : HashMap String Int) (nTheorems : Nat) (f1 f2 : Features) : Float :=
  let fI := HashSet.intersection f1 f2
  let trans l n := (Float.log (Float.ofInt l / Float.ofInt n)) ^ 2
  let count f := if fCounts.contains f then fCounts.find! f else 1
  let countTrans f := trans nTheorems (count f)
  let sum l := List.foldl (fun acc x => acc + x) 0 l
  let f1 := f1.toList.map countTrans
  let f2 := f2.toList.map countTrans
  let fI := fI.toList.map countTrans
  let (s1, s2, sI) := (sum f1, sum f2, sum fI)
  sI / (s1 + s2 - sI)

def predictOneWithScore (data : List Example) (nNeighbours : Nat) (f : Features) : List (String × Float) :=
  let allFeatures := (data.map (fun e => e.features.toList)).flattenUnordered
  let fCounts := freqs allFeatures
  let sim := similarity fCounts data.length f
  let simils := data.map (fun e => (sim e.features, e.label))
  let simils := simils.toArray.qsort (fun (x, _) (y, _) => x > y)
  let simils := simils.toList.initSeg nNeighbours
  let add s (tbl : HashMap String Float) p :=
    if tbl.contains p then tbl.insert p (tbl.find! p + s) else tbl.insert p s
  let addMany tbl sPs := let (s, ps) := sPs; ps.foldl (add s) tbl
  let premisesScores := simils.foldl addMany HashMap.empty
  let ranking := premisesScores.toList.sort (fun (_, x) (_, y) => x > y)
  ranking
  -- Note: The sort function in PremiseSelection/Utils.lean causes stack overflow
  /- Original code
  let simils := simils.sort (fun (x, _) (y, _) => x > y)
  let simils := simils.initSeg nNeighbours
  let add s (tbl : HashMap String Float) p :=
    if tbl.contains p then tbl.insert p (tbl.find! p + s) else tbl.insert p s
  let addMany tbl sPs := let (s, ps) := sPs; ps.foldl (add s) tbl
  let premisesScores := simils.foldl addMany HashMap.empty
  let ranking := premisesScores.toList.sort (fun (_, x) (_, y) => x > y)
  ranking.map (fun (x, _) => x)
  -/

def predictOne (data : List Example) (nNeighbours : Nat) (f : Features) : List String :=
  (predictOneWithScore data nNeighbours f).map (fun (x, _) => x)

def predict (trainData testData : List Example) (nNeighbours : Nat) :=
  let testData := testData.map Example.features
  let predictOne := predictOne trainData nNeighbours
  testData.mapParallel predictOne

end KNNPremiseSelection
