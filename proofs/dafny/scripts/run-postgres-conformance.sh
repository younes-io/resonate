#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$ROOT"

URL="${RESONATE_TEST_POSTGRES_URL:-}"
STARTED_DOCKER_MODE=""
DIRECT_CONTAINER_NAME="resonate-pg-conformance"
DIRECT_PGDATA=""

cleanup() {
  if [ "$STARTED_DOCKER_MODE" = "compose" ]; then
    docker compose down -v --remove-orphans >/dev/null 2>&1 || true
  elif [ "$STARTED_DOCKER_MODE" = "direct" ]; then
    docker rm -f "$DIRECT_CONTAINER_NAME" >/dev/null 2>&1 || true
    if [ -n "$DIRECT_PGDATA" ]; then
      rm -rf "$DIRECT_PGDATA" >/dev/null 2>&1 || true
    fi
  fi
}
trap cleanup EXIT

wait_for_postgres_container() {
  container_name="$1"

  for _ in $(seq 1 60); do
    if ! docker inspect "$container_name" >/dev/null 2>&1; then
      sleep 1
      continue
    fi

    container_status="$(docker inspect -f '{{.State.Status}}' "$container_name" 2>/dev/null || echo unknown)"
    if [ "$container_status" = "exited" ] || [ "$container_status" = "dead" ]; then
      echo "Docker Postgres container failed to start (status: $container_status)." >&2
      docker logs "$container_name" >&2 || true
      return 1
    fi

    if [ "$container_status" = "running" ] && docker exec "$container_name" pg_isready -U resonate -d resonate >/dev/null 2>&1; then
      echo "ready"
      return 0
    fi

    sleep 1
  done

  echo "Docker Postgres container did not become ready." >&2
  docker logs "$container_name" >&2 || true
  return 1
}

start_compose_postgres() {
  docker compose down -v --remove-orphans >/dev/null 2>&1 || true
  docker compose rm -sf postgres >/dev/null 2>&1 || true
  docker compose up -d --force-recreate --remove-orphans postgres >/dev/null
  wait_for_postgres_container "resonate-postgres-1"
}

start_direct_postgres() {
  DIRECT_PGDATA="$(mktemp -d "${TMPDIR:-/tmp}/resonate-pgdata.XXXXXX")"
  docker rm -f "$DIRECT_CONTAINER_NAME" >/dev/null 2>&1 || true
  docker run -d --rm \
    --name "$DIRECT_CONTAINER_NAME" \
    -e POSTGRES_USER=resonate \
    -e POSTGRES_PASSWORD=resonate \
    -e POSTGRES_DB=resonate \
    -p 55432:5432 \
    -v "$DIRECT_PGDATA:/var/lib/postgresql/data" \
    postgres:16-alpine >/dev/null
  wait_for_postgres_container "$DIRECT_CONTAINER_NAME"
}

if [ -z "$URL" ]; then
  if command -v docker >/dev/null 2>&1 && docker info >/dev/null 2>&1; then
    if start_compose_postgres; then
      STARTED_DOCKER_MODE="compose"
      URL="postgres://resonate:resonate@127.0.0.1:5432/resonate"
    else
      echo "Falling back to direct disposable Docker Postgres with host-mounted data directory..." >&2
      docker compose down -v --remove-orphans >/dev/null 2>&1 || true
      if start_direct_postgres; then
        STARTED_DOCKER_MODE="direct"
        URL="postgres://resonate:resonate@127.0.0.1:55432/resonate"
      else
        exit 1
      fi
    fi
  else
    echo "No RESONATE_TEST_POSTGRES_URL set and Docker is not available." >&2
    echo "Provide a live Postgres URL or start Docker, then rerun:" >&2
    echo "  proofs/dafny/scripts/run-postgres-conformance.sh" >&2
    exit 1
  fi
fi

export RESONATE_TEST_POSTGRES_URL="$URL"

cargo test persistence::persistence_postgres::tests:: -- --ignored --nocapture --test-threads=1
