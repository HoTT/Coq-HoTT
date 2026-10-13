#!/usr/bin/env bash
# SessionStart hook: make sure a Docker daemon is running, so that bin/build
# (and the typecheck hook) work from the first edit. Fresh cloud containers
# come without a running daemon. The rocq/rocq-prover image is pulled on
# first use by `docker run`.

if docker info >/dev/null 2>&1; then
  exit 0
fi

if [ "$(id -u)" != 0 ] || ! command -v dockerd >/dev/null 2>&1; then
  echo "Docker daemon is not running and cannot be started here; bin/build will fail." >&2
  exit 0
fi

# Start a daemon unless one is already starting up.
if ! pgrep -x dockerd >/dev/null 2>&1; then
  nohup dockerd >"${TMPDIR:-/tmp}/dockerd.log" 2>&1 &
fi

for _ in $(seq 1 90); do
  if docker info >/dev/null 2>&1; then
    exit 0
  fi
  sleep 1
done

echo "Started dockerd, but it did not come up within 90 seconds; see ${TMPDIR:-/tmp}/dockerd.log." >&2
exit 0
