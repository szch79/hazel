#!/usr/bin/env bash
# List the upstream Lean releases published after the toolchain in
# `lean-toolchain`, oldest first, one `<tag><TAB><publish date>` per line.
# Hazel bumps through them one at a time in exactly this order, patch
# releases of an older line included.
#
# Usage: scripts/pending-releases.sh [toolchain-file]
# Set GITHUB_TOKEN to lift the unauthenticated GitHub API rate limit.
set -euo pipefail

file=${1:-lean-toolchain}
current=$(sed -e 's/^leanprover\/lean4://' "$file" | tr -d '[:space:]')

auth=()
if [[ -n ${GITHUB_TOKEN:-} ]]; then
  auth=(-H "Authorization: Bearer $GITHUB_TOKEN")
fi

releases=$(curl -fsSL ${auth[@]+"${auth[@]}"} -H 'Accept: application/vnd.github+json' \
  'https://api.github.com/repos/leanprover/lean4/releases?per_page=100') ||
  { echo "pending-releases: cannot fetch the upstream releases" >&2; exit 1; }

python3 -I -c '
import json, sys
current = sys.argv[1]
releases = sorted((r for r in json.load(sys.stdin) if not r["draft"]),
                  key=lambda r: r["published_at"])
tags = [r["tag_name"] for r in releases]
if current not in tags:
    sys.exit(f"pending-releases: {current} is not among the recent upstream releases")
for r in releases[tags.index(current) + 1:]:
    print(r["tag_name"] + "\t" + r["published_at"][:10])
' "$current" <<<"$releases"
