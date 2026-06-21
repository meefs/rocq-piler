#!/usr/bin/env bash
set -euo pipefail

# batch.sh — Run benchmarks across a grid of models × problems × MCP profiles
# Usage: batch.sh [--models "m1,m2"] [--problems "p1,p2"] [--profiles "full,positional"] [--parallel N] [--timeout S]

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

DEFAULT_MODELS="deepseek/deepseek-v4-pro"
DEFAULT_PROFILES="full"
PARALLEL=1
TIMEOUT=1800

while [[ $# -gt 0 ]]; do
  case $1 in
    --models) MODELS="$2"; shift 2 ;;
    --problems) PROBLEMS="$2"; shift 2 ;;
    --profiles|--profile) PROFILES="$2"; shift 2 ;;
    --parallel) PARALLEL="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    -h|--help)
      echo "Usage: batch.sh [--models m1,m2] [--problems p1,p2] [--profiles full,positional,rocq-mcp] [--parallel N] [--timeout S]"
      echo ""
      echo "Models:   comma-separated (default: $DEFAULT_MODELS)"
      echo "Problems: comma-separated (default: all .v files in incomplete/)"
      echo "Profiles: comma-separated MCP profiles (default: $DEFAULT_PROFILES)"
      echo "Parallel: max concurrent runs (default: 1)"
      echo "Timeout:  per-run timeout in seconds (default: 1800)"
      exit 0 ;;
    *) echo "Unknown flag: $1" >&2; exit 1 ;;
  esac
done

MODELS="${MODELS:-$DEFAULT_MODELS}"
PROFILES="${PROFILES:-$DEFAULT_PROFILES}"

# Auto-discover problems from .v files if not specified
if [[ -z "${PROBLEMS:-}" ]]; then
  PROBLEMS=""
  for vf in "$BENCH_DIR"/incomplete/*.v; do
    [[ -f "$vf" ]] || continue
    name=$(basename "$vf" .v)
    PROBLEMS="${PROBLEMS:+$PROBLEMS,}$name"
  done
fi

IFS=',' read -ra MODEL_LIST <<< "$MODELS"
IFS=',' read -ra PROBLEM_LIST <<< "$PROBLEMS"
IFS=',' read -ra PROFILE_LIST <<< "$PROFILES"

TOTAL=$(( ${#MODEL_LIST[@]} * ${#PROBLEM_LIST[@]} * ${#PROFILE_LIST[@]} ))
echo "=== Benchmark Grid ==="
echo "Models:   ${MODEL_LIST[*]}"
echo "Problems: ${PROBLEM_LIST[*]}"
echo "Profiles: ${PROFILE_LIST[*]}"
echo "Runs:     $TOTAL (parallel=$PARALLEL, timeout=${TIMEOUT}s)"
echo "========================"
echo ""

RUN_NUM=0

run_one() {
  local model="$1" problem="$2" profile="$3"
  bash "$SCRIPT_DIR/run.sh" --model "$model" --problem "$problem" --profile "$profile" --timeout "$TIMEOUT" || true
}

if [[ $PARALLEL -le 1 ]]; then
  for model in "${MODEL_LIST[@]}"; do
    for problem in "${PROBLEM_LIST[@]}"; do
      for profile in "${PROFILE_LIST[@]}"; do
        RUN_NUM=$((RUN_NUM + 1))
        echo "--- Run $RUN_NUM/$TOTAL: $model × $problem × $profile ---"
        run_one "$model" "$problem" "$profile"
        echo ""
      done
    done
  done
else
  PIDS=()
  for model in "${MODEL_LIST[@]}"; do
    for problem in "${PROBLEM_LIST[@]}"; do
      for profile in "${PROFILE_LIST[@]}"; do
        RUN_NUM=$((RUN_NUM + 1))
        echo "--- Launching $RUN_NUM/$TOTAL: $model × $problem × $profile ---"
        run_one "$model" "$problem" "$profile" &
        PIDS+=($!)

        while [[ ${#PIDS[@]} -ge $PARALLEL ]]; do
          DONE=()
          for pid in "${PIDS[@]}"; do
            kill -0 "$pid" 2>/dev/null && DONE+=("$pid")
          done
          PIDS=("${DONE[@]}")
          [[ ${#PIDS[@]} -ge $PARALLEL ]] && sleep 5
        done
      done
    done
  done

  for pid in "${PIDS[@]}"; do
    wait "$pid" || true
  done
fi

echo ""
echo "=== Complete ==="
echo "Results in: $SCRIPT_DIR/results/"

if [[ -f "$SCRIPT_DIR/results/summary.jsonl" ]]; then
  echo ""
  echo "Summary:"
  jq -r '[.model, .problem, .profile, (.eval.compiles | tostring), (.eval.pairs_resolved | tostring) + "/" + (.eval.pairs_total | tostring), (.duration_s | tostring) + "s", "$" + (.cost | tostring)] | @tsv' \
    "$SCRIPT_DIR/results/summary.jsonl" | column -t -N "MODEL,PROBLEM,PROFILE,COMPILES,PAIRS,TIME,COST"
fi
