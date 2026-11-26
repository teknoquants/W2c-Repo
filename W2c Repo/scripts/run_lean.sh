#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# MIT License
# 
# Copyright (c) 2026 Roger Cooperman; A.E. Petrunina V.V.
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-3}"
mkdir -p .lake
staging=$(mktemp -d .lake/w2cr-records.XXXXXXXX)
trap 'rm -rf -- "$staging"' EXIT

# Keep the released record readable during a concurrent Python replay.
check_packet() {
  local source_file=$1
  local record_file=$2
  local fresh="$staging/checked.out"
  lake env lean --stdin < "$source_file" > "$fresh"
  if [[ -f "$record_file" ]]; then
    cmp "$record_file" "$fresh"
  else
    mv "$fresh" "$record_file"
  fi
}

python3 scripts/formal.py freeze
for unit in A B C D E F S; do
  check_packet "records/w2c-r/statement-round/$unit.lean" "records/w2c-r/statement-round/$unit.out"
done
python3 scripts/formal.py prepare
lake build
check_packet baseline/records/w2-v1/final.lean records/w2c-r/upstream.local.out
cmp baseline/records/w2-v1/final.local.out records/w2c-r/upstream.local.out
for unit in A B C D E F S; do
  check_packet "records/w2c-r/fill/$unit.lean" "records/w2c-r/fill/$unit.out"
done
check_packet packets/W2cR_final.lean records/w2c-r/final.local.out
python3 scripts/formal.py record
