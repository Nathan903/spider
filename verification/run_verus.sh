#!/usr/bin/env bash
set -euo pipefail
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
export PATH="$HOME/tools/verus/source/target-verus/release:$PATH"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
verus --triggers-mode silent --time --time-expanded "$SCRIPT_DIR/c6_task_state_machine.rs" -o /tmp/c6_task_state_machine "$@"
