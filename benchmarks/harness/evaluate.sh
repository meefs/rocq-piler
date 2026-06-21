#!/usr/bin/env bash
set -euo pipefail

# evaluate.sh — Check a completed .v file against its incomplete reference
# Usage: evaluate.sh <complete_file> --reference <incomplete_file> [-- coq_flags...]
# Output: JSON object with results to stdout

COMPLETE=""
INCOMPLETE=""
COQ_FLAGS=()

while [[ $# -gt 0 ]]; do
  case $1 in
    --reference) INCOMPLETE="$2"; shift 2 ;;
    --) shift; COQ_FLAGS=("$@"); break ;;
    *) [[ -z "$COMPLETE" ]] && COMPLETE="$1" || COQ_FLAGS+=("$1"); shift ;;
  esac
done

[[ -z "$COMPLETE" ]] && { echo '{"error":"Usage: evaluate.sh <complete> --reference <incomplete>"}'; exit 1; }

if [[ ! -f "$COMPLETE" ]]; then
  echo '{"error":"complete file not found","file":"'"$COMPLETE"'"}'
  exit 1
fi

# 1. Try to compile
coqc "${COQ_FLAGS[@]}" "$COMPLETE" >/dev/null 2>&1 && COMPILES=true || COMPILES=false

# Helper: extract theorem/lemma name → qed/admitted from a .v file
extract_statuses() {
  awk '
    /^[[:space:]]*(Theorem|Lemma)[[:space:]]/ {
      name = $2
      gsub(/:$/, "", name)
      waiting = 1
    }
    waiting && /Qed\./ {
      print name, "qed"
      waiting = 0
    }
    waiting && /Admitted\./ {
      print name, "admitted"
      waiting = 0
    }
  ' "$1"
}

# 2. Discover pairs from the INCOMPLETE (reference) file
declare -A REF_PAIRS  # base_name -> 1
if [[ -n "$INCOMPLETE" && -f "$INCOMPLETE" ]]; then
  while IFS=' ' read -r name status; do
    [[ -z "$name" ]] && continue
    if [[ "$name" == *_neg ]]; then
      base="${name%_neg}"
      REF_PAIRS["$base"]=1
    fi
  done <<< "$(extract_statuses "$INCOMPLETE")"
fi

# 3. Extract statuses from the COMPLETE file
declare -A COMPLETE_STATUS
while IFS=' ' read -r name status; do
  [[ -z "$name" ]] && continue
  COMPLETE_STATUS["$name"]="$status"
done <<< "$(extract_statuses "$COMPLETE")"

# 4. Evaluate pairs
PAIRS_JSON="{"
PAIRS_TOTAL=0
PAIRS_RESOLVED=0
SEPARATOR=""

if [[ ${#REF_PAIRS[@]} -gt 0 ]]; then
  for base in "${!REF_PAIRS[@]}"; do
    PAIRS_TOTAL=$((PAIRS_TOTAL + 1))
    pos="${COMPLETE_STATUS[$base]:-missing}"
    neg="${COMPLETE_STATUS[${base}_neg]:-missing}"

    if [[ "$pos" == "qed" ]]; then
      pair_result="proved"
      PAIRS_RESOLVED=$((PAIRS_RESOLVED + 1))
    elif [[ "$neg" == "qed" ]]; then
      pair_result="refuted"
      PAIRS_RESOLVED=$((PAIRS_RESOLVED + 1))
    else
      pair_result="neither"
    fi

    PAIRS_JSON="${PAIRS_JSON}${SEPARATOR}\"${base}\":\"${pair_result}\""
    SEPARATOR=","
  done
else
  # Fallback: no reference or no pairs found — count all qed theorems
  for name in "${!COMPLETE_STATUS[@]}"; do
    PAIRS_TOTAL=$((PAIRS_TOTAL + 1))
    [[ "${COMPLETE_STATUS[$name]}" == "qed" ]] && PAIRS_RESOLVED=$((PAIRS_RESOLVED + 1))
  done
fi
PAIRS_JSON="${PAIRS_JSON}}"

cat <<EOF
{
  "file": "$COMPLETE",
  "compiles": $COMPILES,
  "pairs_total": $PAIRS_TOTAL,
  "pairs_resolved": $PAIRS_RESOLVED,
  "pairs": $PAIRS_JSON
}
EOF
