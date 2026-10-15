#!/usr/bin/env bash
# Bump Hazel to the next upstream Lean release, and only that one.
#
# Takes the first release from `scripts/pending-releases.sh`, writes it to
# `lean-toolchain`, and runs the CI sequence.  It then commits, tags, pushes
# main and the tag, and waits until the tag's Release workflow has published
# the GitHub release.  Run it again for the release after that.  No tag is
# pushed before the previous release exists, so the GitHub releases stay in
# upstream order.
#
# Usage:
#   scripts/bump-toolchain.sh                    bump to the next release
#   scripts/bump-toolchain.sh --list             list pending releases
#   scripts/bump-toolchain.sh --resume -m BODY   finish a bump whose build
#                                                failed, after fixing it
#
# On `--resume`, BODY becomes the commit body and should explain the fix.
# Stage any new files first; changes to tracked files are picked up.
# Set GITHUB_TOKEN to lift the unauthenticated GitHub API rate limit.
set -euo pipefail

repo=szch79/hazel
cd "$(git rev-parse --show-toplevel)"

mode=start
body=
while (($#)); do
  case $1 in
    --list) mode=list ;;
    --resume) mode=resume ;;
    -m) body=${2:?-m needs a commit body}; shift ;;
    *) echo "usage: $0 [--list | --resume -m BODY]" >&2; exit 2 ;;
  esac
  shift
done

die() { echo "bump-toolchain: $*" >&2; exit 1; }

api() {
  local auth=()
  if [[ -n ${GITHUB_TOKEN:-} ]]; then
    auth=(-H "Authorization: Bearer $GITHUB_TOKEN")
  fi
  curl -fsSL ${auth[@]+"${auth[@]}"} -H 'Accept: application/vnd.github+json' \
    "https://api.github.com/repos/$repo/$1"
}

# Pending releases are counted from the committed toolchain, so a bump in
# progress still sees its own target first.
pending=$(scripts/pending-releases.sh <(git show HEAD:lean-toolchain))
if [[ -z $pending ]]; then
  echo "Up to date with upstream."
  exit 0
fi
if [[ $mode == list ]]; then
  echo "$pending"
  exit 0
fi
next=$(head -n 1 <<<"$pending" | cut -f 1)

[[ $(git branch --show-current) == main ]] || die "not on main"
git fetch -q origin main
[[ $(git rev-parse HEAD) == "$(git rev-parse origin/main)" ]] ||
  die "main differs from origin/main; pull or push first"
if git rev-parse -q --verify "refs/tags/$next" >/dev/null ||
    [[ -n $(git ls-remote --tags origin "refs/tags/$next") ]]; then
  die "tag $next already exists"
fi

if [[ $mode == start ]]; then
  [[ -z $(git status --porcelain --untracked-files=no) ]] ||
    die "the working tree has uncommitted changes"
  echo "leanprover/lean4:$next" > lean-toolchain
else
  [[ $(<lean-toolchain) == "leanprover/lean4:$next" ]] ||
    die "nothing to resume: lean-toolchain is not $next"
fi

echo "==> Building on $next (pending, in order: $(cut -f 1 <<<"$pending" | paste -sd ' ' -))"
# Keep in sync with the steps of .github/workflows/build.yml.
if ! { lake build Hazel HazelTest --wfail && lake build HazelTestFixtures && lake test; }; then
  die "the build fails on $next.  Fix it, then run: $0 --resume -m '<what the fix does>'"
fi

git add -u
if [[ -n $(git diff --cached --name-only -- . ':!lean-toolchain') && -z $body ]]; then
  die "the bump changes more than lean-toolchain; describe the fix with --resume -m BODY"
fi
msg=(-m "chore: bump toolchain to $next")
if [[ -n $body ]]; then
  msg+=(-m "$body")
fi
git commit -q "${msg[@]}"
git tag "$next"
git push -q origin main
git push -q origin "$next"
sha=$(git rev-parse HEAD)

echo "==> Pushed $next ($sha); waiting for its Release run"
deadline=$((SECONDS + 1800))
while :; do
  sleep 30
  state=$(api "actions/runs?head_sha=$sha&event=push" | python3 -I -c '
import json, sys
runs = [r for r in json.load(sys.stdin)["workflow_runs"]
        if r["name"] == "Release" and r["head_branch"] == sys.argv[1]]
print(runs[0]["status"] + " " + str(runs[0]["conclusion"]) if runs else "queued None")
' "$next") || state="unknown None"
  case $state in
    "completed success") break ;;
    completed*)
      die "the Release run for $next ended with '${state#completed }', so no release was published.
The build passed locally, so check https://github.com/$repo/actions for a transient
failure and re-run the workflow there.  Do not bump further until $next is released." ;;
  esac
  ((SECONDS < deadline)) || die "timed out waiting for the Release run for $next"
done
api "releases/tags/$next" >/dev/null || die "the Release run succeeded but no $next release exists"

echo "==> Released $next: https://github.com/$repo/releases/tag/$next"
remaining=$(tail -n +2 <<<"$pending" | cut -f 1 | paste -sd ' ' -)
if [[ -n $remaining ]]; then
  echo "Still pending, in order: $remaining.  Run $0 again for the next one."
fi
