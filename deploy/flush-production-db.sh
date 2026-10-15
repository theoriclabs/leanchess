#!/usr/bin/env bash
# Deletes the production leanchess.sqlite (+ -shm/-wal) from the Railway
# volume and restarts the service so it opens a fresh, empty database.
#
# Must be run by a human at a terminal: the confirmation is read from a
# TTY, never from piped stdin, and it names the resolved environment.
set -euo pipefail

VOLUME="leanchess-volume"
SERVICE="leanchess"
ENVIRONMENT="${LEANCHESS_ENVIRONMENT:-production}"
URL="${LEANCHESS_URL:-https://leanchess.org}"

if [[ -t 0 ]]; then
  echo "Files currently on volume '$VOLUME' ($ENVIRONMENT):"
  railway volume files --volume "$VOLUME" --environment "$ENVIRONMENT" list /
else
  echo "flush: refusing: stdin is not a terminal. The confirmation cannot" >&2
  echo "be piped in; run this script by hand at a terminal." >&2
  exit 1
fi

command -v railway >/dev/null 2>&1 || { echo "railway CLI not found" >&2; exit 1; }

cat <<EOF
This will permanently delete leanchess.sqlite, leanchess.sqlite-shm, and
leanchess.sqlite-wal, and every leanchess.sqlite.before-migration-*
backup, from the '$VOLUME' volume of the '$SERVICE' service in
'$ENVIRONMENT', then restart the service so it starts with a fresh,
empty database. This cannot be undone.
EOF

read -r -p "Type 'flush' to proceed: " CONFIRM
if [[ "$CONFIRM" != "flush" ]]; then
  echo "Aborted, nothing deleted."
  exit 1
fi

for f in leanchess.sqlite leanchess.sqlite-shm leanchess.sqlite-wal; do
  echo "Deleting /$f ..."
  railway volume files --volume "$VOLUME" --environment "$ENVIRONMENT" delete "/$f" --yes || true
done

# Migration snapshots beside the file survive the loop above, and each
# one carries every user's token and the full game log. Delete them too,
# by whatever names the volume still lists.
backups="$(railway volume files --volume "$VOLUME" --environment "$ENVIRONMENT" list / || true)"
while IFS= read -r name; do
  [[ -n "$name" ]] || continue
  echo "Deleting /$name ..."
  railway volume files --volume "$VOLUME" --environment "$ENVIRONMENT" delete "/$name" --yes || true
done < <(printf '%s\n' "$backups" | grep -o 'leanchess\.sqlite\.before-migration-[0-9a-f]*' | sort -u)

echo "Restarting '$SERVICE' ..."
railway restart --service "$SERVICE" --environment "$ENVIRONMENT" --yes

echo "Waiting for $URL/healthz ..."
for _ in $(seq 1 12); do
  if curl -fsS "$URL/healthz" >/dev/null 2>&1; then
    echo "Done. The service is answering at $URL/healthz."
    railway volume files --volume "$VOLUME" --environment "$ENVIRONMENT" list /
    exit 0
  fi
  sleep 5
done
echo "flush: the service did not answer $URL/healthz within a minute" >&2
exit 1
