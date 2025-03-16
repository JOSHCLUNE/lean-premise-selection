#!/usr/bin/env bash

MODULE=$1
OUT_DIR=`realpath $2`
PARAMS=${@:3}
LABELS=$OUT_DIR/$MODULE.labels
FEATURES=$OUT_DIR/$MODULE.features
LEAN_EXTRACTOR=KNNPremiseSelection/ExtractorRunner.lean

export LEAN_PATH=.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/mathlib/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/batteries/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/Qq/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/aesop/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/importGraph/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/proofwidgets/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/plausible/.lake/build/lib
export LEAN_PATH=$LEAN_PATH:.lake/packages/LeanSearchClient/.lake/build/lib

lean --run --memory=4096 --timeout=100000000000 \
    $LEAN_EXTRACTOR \
    $LABELS \
    $FEATURES \
    <(echo $MODULE) \
    $PARAMS
