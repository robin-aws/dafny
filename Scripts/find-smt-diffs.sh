#!/bin/bash
set -e

git bisect start
git checkout $1
git bisect good
git checkout $2
git bisect bad
git bisect run python3 ../../GitHub/dafny/Scripts/smt-diff.py $1 local --program ../../GitHub/dafny/Test/comp/Arrays.dfy
