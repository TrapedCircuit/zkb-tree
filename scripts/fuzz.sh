#!/usr/bin/env bash
#
# Fuzz testing script for zkb-tree.
#
# Usage:
#   ./scripts/fuzz.sh              # run btree_ops with defaults (60s)
#   ./scripts/fuzz.sh btree 300    # btree_ops, 300s
#   ./scripts/fuzz.sh all 120      # all targets, 120s each
#
# Environment variables:
#   FUZZ_DURATION   - seconds per target (default: 60)
#   FUZZ_MAX_LEN    - max input length in bytes (default: 4096)
#   FUZZ_CORPUS_DIR - custom corpus directory (default: managed by cargo-fuzz)
#   FUZZ_COV        - set to "1" to generate coverage reports after fuzzing

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

TARGET_FILTER="${1:-all}"
FUZZ_DURATION="${2:-${FUZZ_DURATION:-60}}"
FUZZ_MAX_LEN="${FUZZ_MAX_LEN:-4096}"
EXTRA_ARGS="${3:-}"

GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

info()  { echo -e "${GREEN}[+]${NC} $*"; }
warn()  { echo -e "${YELLOW}[!]${NC} $*"; }
error() { echo -e "${RED}[x]${NC} $*"; }

# ---------------------------------------------------------------------------
# Prerequisites
# ---------------------------------------------------------------------------

check_tool() {
    if ! command -v "$1" &>/dev/null; then
        error "$1 not found. Installing..."
        cargo install "$2"
    fi
}

check_tool cargo-fuzz cargo-fuzz

# ---------------------------------------------------------------------------
# libfuzzer targets (cargo-fuzz)
# ---------------------------------------------------------------------------

LIBFUZZER_TARGETS=()
case "$TARGET_FILTER" in
    btree|all) LIBFUZZER_TARGETS=(btree_ops) ;;
    *)         LIBFUZZER_TARGETS=("$TARGET_FILTER") ;;
esac

FAILED=0

for target in "${LIBFUZZER_TARGETS[@]}"; do
    info "Fuzzing ${target} (libfuzzer) for ${FUZZ_DURATION}s, max_len=${FUZZ_MAX_LEN} ..."

    CORPUS_ARGS=""
    if [[ -n "${FUZZ_CORPUS_DIR:-}" ]]; then
        mkdir -p "${FUZZ_CORPUS_DIR}/${target}"
        CORPUS_ARGS="-- ${FUZZ_CORPUS_DIR}/${target}"
    fi

    set +e
    cargo fuzz run "$target" \
        --fuzz-dir fuzz \
        -- \
        -max_total_time="$FUZZ_DURATION" \
        -max_len="$FUZZ_MAX_LEN" \
        $EXTRA_ARGS \
        2>&1 | tee "/tmp/fuzz_${target}.log"
    EXIT_CODE=${PIPESTATUS[0]}
    set -e

    if [[ $EXIT_CODE -ne 0 ]]; then
        error "${target} FAILED (exit code ${EXIT_CODE})"
        FAILED=1

        ARTIFACT=$(grep -o 'Test unit written to .*' "/tmp/fuzz_${target}.log" | sed 's/Test unit written to //' || true)
        if [[ -n "$ARTIFACT" ]]; then
            error "Crash artifact: ${ARTIFACT}"
        fi
    else
        RUNS=$(grep -o 'Done [0-9]* runs' "/tmp/fuzz_${target}.log" | grep -o '[0-9]*' || echo "?")
        info "${target} OK — ${RUNS} runs in ${FUZZ_DURATION}s"
    fi
    echo
done

# ---------------------------------------------------------------------------
# Coverage (optional)
# ---------------------------------------------------------------------------

if [[ "${FUZZ_COV:-0}" == "1" ]]; then
    info "Generating coverage reports..."
    for target in "${LIBFUZZER_TARGETS[@]}"; do
        info "Coverage for ${target}..."
        cargo fuzz coverage "$target" --fuzz-dir fuzz 2>&1 || warn "Coverage failed for ${target}"
    done
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

echo
echo "========================================"
if [[ $FAILED -eq 0 ]]; then
    info "All fuzz targets passed."
else
    error "Some fuzz targets failed. Check logs above."
    exit 1
fi
