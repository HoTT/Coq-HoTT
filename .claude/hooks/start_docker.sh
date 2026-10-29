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

log="${TMPDIR:-/tmp}/dockerd.log"

wait_for_docker() {
  for _ in $(seq 1 "$1"); do
    if docker info >/dev/null 2>&1; then
      return 0
    fi
    sleep 1
  done
  return 1
}

# Start a daemon unless one is already starting up.
if ! pgrep -x dockerd >/dev/null 2>&1; then
  nohup dockerd >"$log" 2>&1 &
fi
wait_for_docker 45 && exit 0

# In some containers the containerd that dockerd manages itself does not come
# up in time. Fall back to running containerd separately.
if command -v containerd >/dev/null 2>&1; then
  pkill -x dockerd 2>/dev/null
  for _ in $(seq 1 20); do pgrep -x dockerd >/dev/null 2>&1 || break; sleep 1; done
  rm -f /var/run/docker.pid
  if ! pgrep -x containerd >/dev/null 2>&1; then
    nohup containerd >"${TMPDIR:-/tmp}/containerd.log" 2>&1 &
  fi
  for _ in $(seq 1 30); do [ -S /run/containerd/containerd.sock ] && break; sleep 1; done
  nohup dockerd --containerd=/run/containerd/containerd.sock >>"$log" 2>&1 &
  wait_for_docker 45 && exit 0
fi

echo "Started dockerd, but it did not come up; see $log." >&2
exit 0
