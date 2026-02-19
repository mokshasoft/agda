#!/bin/bash
# Run dead code analysis on an Agda project using the locally built agda
#
# Usage: ./run-dead-code.sh <entry-point> <file.agda> [project-dir]
#
# Examples:
#   ./run-dead-code.sh Module.main path/to/Module.agda
#   ./run-dead-code.sh Once.Backend.X86v3.Dispatcher.run-ir Once/Backend/X86v3/Dispatcher.agda /path/to/project

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
AGDA_BIN="$SCRIPT_DIR/dist-newstyle/build/x86_64-linux/ghc-9.12.2/Agda-2.9.0/x/agda/build/agda/agda"

if [ $# -lt 2 ]; then
    echo "Usage: $0 <entry-point> <file.agda> [project-dir]"
    echo ""
    echo "Arguments:"
    echo "  entry-point  Qualified name of the entry point (e.g., Module.main)"
    echo "  file.agda    Path to the Agda file to check"
    echo "  project-dir  Optional: project directory (defaults to file's directory)"
    echo ""
    echo "Example:"
    echo "  $0 Once.Backend.X86v3.Dispatcher.run-ir Once/Backend/X86v3/Dispatcher.agda /path/to/formal"
    exit 1
fi

ENTRY_POINT="$1"
AGDA_FILE="$2"
PROJECT_DIR="${3:-$(dirname "$AGDA_FILE")}"

# Find standard library in nix store
STD_LIB=$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1)

if [ -z "$STD_LIB" ]; then
    echo "Warning: standard-library.agda-lib not found in /nix/store"
    echo "Running without nix standard library..."

    cd "$PROJECT_DIR"
    "$AGDA_BIN" --dead-code="$ENTRY_POINT" "$AGDA_FILE"
else
    echo "Using standard library: $STD_LIB"

    # Find project's .agda-lib file
    PROJECT_LIB=$(find "$PROJECT_DIR" -maxdepth 1 -name "*.agda-lib" 2>/dev/null | head -1)

    cd "$PROJECT_DIR"

    if [ -n "$PROJECT_LIB" ]; then
        echo "Using project library: $PROJECT_LIB"
        "$AGDA_BIN" \
            --library-file=<(echo "$STD_LIB"; echo "$PROJECT_LIB") \
            --no-write-interfaces \
            --dead-code="$ENTRY_POINT" \
            "$AGDA_FILE"
    else
        "$AGDA_BIN" \
            --library-file=<(echo "$STD_LIB") \
            --no-write-interfaces \
            --dead-code="$ENTRY_POINT" \
            "$AGDA_FILE"
    fi
fi
