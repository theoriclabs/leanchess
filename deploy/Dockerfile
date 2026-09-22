# One process: the fold, and the page that looks at it.
# Build context is the parent of leanchess, leandb, and leanreact.

FROM debian:bookworm-slim AS build

RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential ca-certificates curl git pkg-config libsqlite3-dev xz-utils \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL https://nodejs.org/dist/v22.19.0/node-v22.19.0-linux-x64.tar.xz \
      | tar -xJ -C /usr/local --strip-components=1

ENV ELAN_HOME=/usr/local/elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none \
    && elan toolchain install leanprover/lean4:v4.33.0 \
    && elan default leanprover/lean4:v4.33.0

WORKDIR /src
COPY leandb /src/leandb
COPY leanreact /src/leanreact
COPY leanchess /src/leanchess

WORKDIR /src/leanreact
RUN npm ci

WORKDIR /src/leanreact
RUN lake build LeanReact.Compiler

WORKDIR /src/leanchess
RUN lake build leanchess-api ui \
    && lake env lean ui/Generate.lean \
    && NODE_PATH=/src/leanreact/node_modules \
       /src/leanreact/node_modules/.bin/esbuild web/main.mjs \
         --bundle --format=esm --platform=browser --target=es2022 \
         --outfile=web/dist/app.js \
    && cp web/index.html web/style.css web/dist/

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates libgmp10 libsqlite3-0 libstdc++6 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=build /src/leanchess/.lake/build/bin/leanchess-api /usr/local/bin/leanchess-api
COPY --from=build /src/leanchess/web/dist /srv/web

ENV PORT=8080
EXPOSE 8080
CMD ["sh", "-c", "exec leanchess-api --host 0.0.0.0 --port ${PORT:-8080} --db ${DB_PATH:-/data/leanchess.sqlite} --web /srv/web"]
