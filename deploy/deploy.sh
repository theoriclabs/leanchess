#!/usr/bin/env bash
# Deploy the committed heads of leanchess, leandb, and leanreact to
# leanchess.org, and wait until the new deployment is serving.
#
# The Dockerfile builds from a context holding the three repositories side
# by side (see deploy/Dockerfile). This stages that context from symlinks,
# with the Dockerfile, .dockerignore, and railway.json at its root, so the
# build settings travel with the code instead of living in the dashboard.
# The three revisions go into the deployment's message.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
code="$(dirname "$here")"
service="${LEANCHESS_SERVICE:-leanchess}"
environment="${LEANCHESS_ENVIRONMENT:-production}"
url="${LEANCHESS_URL:-https://leanchess.org}"

revisions=""
for repo in leanchess leandb leanreact; do
  dir="$code/$repo"
  if [[ ! -d "$dir/.git" ]]; then
    echo "deploy: $dir is not a checkout" >&2
    exit 1
  fi
  if [[ -n "$(git -C "$dir" status --porcelain)" ]]; then
    echo "deploy: $repo has uncommitted or untracked changes; a deploy is built from commits" >&2
    exit 1
  fi
  revisions+="$repo@$(git -C "$dir" rev-parse --short=12 HEAD) "
done
revisions="${revisions% }"

ctx="$(mktemp -d)"
trap 'rm -rf "$ctx"' EXIT
cp "$here/deploy/Dockerfile" "$here/deploy/.dockerignore" "$here/deploy/railway.json" "$ctx/"
for repo in leanchess leandb leanreact; do
  ln -s "$code/$repo" "$ctx/$repo"
done

echo "deploy: $revisions"
upload="$(railway up "$ctx" --path-as-root --service "$service" --environment "$environment" \
  --detach --json -m "$revisions")"
id="$(printf '%s' "$upload" | python3 -c 'import json, sys; print(json.load(sys.stdin)["deploymentId"])')"
echo "deploy: deployment $id"

deadline=$(( $(date +%s) + 1200 ))
while :; do
  status="$(railway deployment list --service "$service" --environment "$environment" --json |
    python3 -c 'import json, sys; print(next((d["status"] for d in json.load(sys.stdin) if d["id"] == sys.argv[1]), "UNKNOWN"))' "$id")"
  case "$status" in
    SUCCESS) break ;;
    FAILED|CRASHED|REMOVED|SKIPPED)
      echo "deploy: $status; build logs: railway logs --build $id --lines 200" >&2
      exit 1 ;;
  esac
  if (( $(date +%s) > deadline )); then
    echo "deploy: still $status after 20 minutes" >&2
    exit 1
  fi
  sleep 15
done

health="$(curl -fsS "$url/healthz")"
echo "deploy: $status; $url/healthz $health"
