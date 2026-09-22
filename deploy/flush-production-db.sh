#!/usr/bin/env bash
# Deletes the production leanchess.sqlite (+ -shm/-wal) from the Railway
# volume and restarts the service so it opens a fresh, empty database.
#
# Must be run by a human: Railway's CLI refuses agent-initiated
# `railway volume files delete` calls outright.
set -euo pipefail

VOLUME="leanchess-volume"
SERVICE="leanchess"

command -v railway >/dev/null 2>&1 || { echo "railway CLI not found" >&2; exit 1; }

echo "Files currently on volume '$VOLUME':"
railway volume files --volume "$VOLUME" list /

cat <<EOF

This will permanently delete leanchess.sqlite, leanchess.sqlite-shm, and
leanchess.sqlite-wal from the '$VOLUME' volume, then restart the '$SERVICE'
service so it starts with a fresh, empty database. This cannot be undone.
EOF

read -r -p "Type 'flush' to proceed: " CONFIRM
if [[ "$CONFIRM" != "flush" ]]; then
  echo "Aborted, nothing deleted."
  exit 1
fi

for f in leanchess.sqlite leanchess.sqlite-shm leanchess.sqlite-wal; do
  echo "Deleting /$f ..."
  railway volume files --volume "$VOLUME" delete "/$f" --yes
done

echo "Restarting '$SERVICE' ..."
railway restart --service "$SERVICE" --yes

echo "Done. Verifying the volume is now empty of sqlite files:"
railway volume files --volume "$VOLUME" list /
