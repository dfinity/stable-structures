#!/usr/bin/env bash
set -Eexuo pipefail

# This script runs `canbench` in a given directory and outputs a comment
# intended to be posted on the pull request.

# Path to run `canbench` from.
CANISTER_PATH=$1

# The name of the CI job.
CANBENCH_JOB_NAME=$2

# Must match the file path specified in the GitHub Action.
COMMENT_MESSAGE_PATH=/tmp/canbench_result_${CANBENCH_JOB_NAME}

# GitHub CI is expected to have the main branch checked out in this folder.
MAIN_BRANCH_DIR=_canbench_main_branch

CANBENCH_OUTPUT=/tmp/canbench_output.txt

CANBENCH_RESULTS_FILE="$CANISTER_PATH/canbench_results.yml"
MAIN_BRANCH_RESULTS_FILE="$MAIN_BRANCH_DIR/$CANBENCH_RESULTS_FILE"

CANBENCH_RESULTS_CSV_FILE="/tmp/canbench_results_${CANBENCH_JOB_NAME}.csv"

# Install canbench.
cargo install --version 0.1.14 canbench

# Verify that the canbench results file exists.
if [ ! -f "$CANBENCH_RESULTS_FILE" ]; then
    echo "$CANBENCH_RESULTS_FILE not found. Did you forget to run \`canbench --persist [--csv]\`?"
    exit 1
fi

# Check if the canbench results file is up to date.
pushd "$CANISTER_PATH"
canbench --less-verbose --hide-results --show-summary --csv > $CANBENCH_OUTPUT
cp "./canbench_results.csv" "$CANBENCH_RESULTS_CSV_FILE"
if grep -q "(regress\|(improved by \|(new)" "$CANBENCH_OUTPUT"; then
  UPDATED_MSG="**❌ \`$CANBENCH_RESULTS_FILE\` is not up to date**
  If the performance change is expected, run \`canbench --persist [--csv]\` to update the benchmark results."

  # Results are outdated; fail the job.
  echo "EXIT_STATUS=1" >> "$GITHUB_ENV"
else
  UPDATED_MSG="✅ \`$CANBENCH_RESULTS_FILE\` is up to date";

  # Results are up to date; job succeeds.
  echo "EXIT_STATUS=0" >> "$GITHUB_ENV"
fi
popd

# Get the latest commit hash
commit_hash=$(git rev-parse HEAD)
time=$(date -u +"%Y-%m-%d %H:%M:%S UTC")

# Print output with correct formatting
echo "# \`canbench\` 🏋 (dir: $CANISTER_PATH) $commit_hash $time" > "$COMMENT_MESSAGE_PATH"

# Check for performance changes relative to the main branch.
if [ -f "$MAIN_BRANCH_RESULTS_FILE" ]; then
  # Replace the current results with the main branch results.
  mv "$MAIN_BRANCH_RESULTS_FILE" "$CANBENCH_RESULTS_FILE"

  # Run canbench to compare results with the main branch.
  pushd "$CANISTER_PATH"
  canbench --less-verbose --hide-results --show-summary --csv > "$CANBENCH_OUTPUT"
  cp "./canbench_results.csv" "$CANBENCH_RESULTS_CSV_FILE"
  popd
fi

CSV_RESULTS_FILE_MSG="📦 \`canbench_results_$CANBENCH_JOB_NAME.csv\` available in [artifacts](${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}/actions/runs/${GITHUB_RUN_ID})"

# Append the update status and benchmark output to the comment.
{
  echo "$UPDATED_MSG"
  echo "$CSV_RESULTS_FILE_MSG"
  echo ""
  echo "\`\`\`"
  cat "$CANBENCH_OUTPUT"
  echo "\`\`\`"
} >> "$COMMENT_MESSAGE_PATH"

# Output the comment to stdout.
cat "$COMMENT_MESSAGE_PATH"
