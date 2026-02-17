#!/bin/bash
# Release script for Specl.
# Updates workspace version, commits, and creates an annotated tag.
#
# Usage: ./scripts/release.sh <version>
# Example: ./scripts/release.sh 0.2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$PROJECT_DIR/.." && pwd)"

if [ $# -ne 1 ]; then
    echo "Usage: $0 <version>"
    echo "Example: $0 0.2.0"
    exit 1
fi

VERSION="$1"

if ! echo "$VERSION" | grep -qE '^[0-9]+\.[0-9]+\.[0-9]+$'; then
    echo "Error: version must be semver format X.Y.Z (got: $VERSION)"
    exit 1
fi

cd "$REPO_ROOT"

if [ -n "$(git status --porcelain)" ]; then
    echo "Error: working tree is not clean"
    git status --short
    exit 1
fi

BRANCH=$(git rev-parse --abbrev-ref HEAD)
if [ "$BRANCH" != "main" ]; then
    echo "Error: must be on main branch (currently on: $BRANCH)"
    exit 1
fi

CARGO_TOML="$PROJECT_DIR/Cargo.toml"

# Read current version from workspace.package.version
OLD_VERSION=$(grep -A5 '^\[workspace\.package\]' "$CARGO_TOML" | grep '^version' | sed 's/.*"\(.*\)".*/\1/')
echo "Updating version: $OLD_VERSION -> $VERSION"

# Update workspace.package.version
sed -i.bak "s/^version = \"$OLD_VERSION\"/version = \"$VERSION\"/" "$CARGO_TOML"

# Update internal crate dependency versions in workspace.dependencies
sed -i.bak "s/version = \"$OLD_VERSION\" }/version = \"$VERSION\" }/" "$CARGO_TOML"

rm -f "$CARGO_TOML.bak"

echo "Running cargo check..."
cd "$PROJECT_DIR"
cargo check --workspace

echo "Committing..."
cd "$REPO_ROOT"
git add specl/Cargo.toml
git commit -m "chore(release): v$VERSION"
git tag -a "v$VERSION" -m "v$VERSION"

echo ""
echo "Release v$VERSION prepared."
echo "Run the following to publish:"
echo "  git push && git push --tags"
