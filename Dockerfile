# The daemon (`vaelii.host.serve`) as an image: one JVM owns one KB and serves it
# over HTTP.  Two stages, because Leiningen is a build tool — a runtime image
# carrying it would carry a dependency resolver and a network fetch into
# production, and the uberjar already is the self-contained artifact.

# ---- build ----------------------------------------------------------------
FROM eclipse-temurin:25-jdk AS build

RUN apt-get update \
 && apt-get install -y --no-install-recommends curl ca-certificates \
 && rm -rf /var/lib/apt/lists/*

# The launcher at a tag, checked against its sha256: the workflows run 2.12.0, because
# 2.13.0's launcher self-installs an unpublished snapshot jar.  A new version takes the
# digest of that tag's `bin/lein` with it.
ARG LEIN_VERSION=2.12.0
ARG LEIN_SHA256=f8e1266c0c78c08bd4af6e111889ecc316c9dd56d1e8645bbee6c1703d351bc3
RUN curl -fsSL "https://raw.githubusercontent.com/technomancy/leiningen/${LEIN_VERSION}/bin/lein" \
      -o /usr/local/bin/lein \
 && echo "${LEIN_SHA256}  /usr/local/bin/lein" | sha256sum -c - \
 && chmod +x /usr/local/bin/lein \
 && lein version

WORKDIR /build

# `--build-arg PROFILES=+with-postgres,+with-sqlite` adds the published siblings
# (project.clj's `+with-` profiles) to the jar, so the image opens `:pg-*` and
# `:sqlite` KBs; `+with-foreign` adds the foreign-format readers.  Empty builds the
# engine alone.
ARG PROFILES=""

# `project.clj` and `project-env.clj` alone, and resolve against them, so that
# editing a source file does not re-resolve the whole dependency graph on every build.
# Everything in `:dependencies` and the `+with-` profiles come from Clojars or Maven
# Central, so this layer needs no local artifact and no checkout.
COPY project.clj project-env.clj ./
RUN lein ${PROFILES:+with-profile "$PROFILES"} deps

COPY . .
# The standalone jar lands in target/uberjar/ whatever profiles are active, and the
# name carries the version — glob rather than spell a version that moves.
RUN lein ${PROFILES:+with-profile "$PROFILES"} uberjar \
 && mv target/uberjar/*-standalone.jar /build/vaelii.jar

# ---- run ------------------------------------------------------------------
FROM eclipse-temurin:25-jre AS run

# curl is here for HEALTHCHECK below and nothing else.
RUN apt-get update \
 && apt-get install -y --no-install-recommends curl \
 && rm -rf /var/lib/apt/lists/* \
 && useradd --system --create-home --home-dir /var/lib/vaelii \
            --shell /usr/sbin/nologin vaelii

COPY --from=build /build/vaelii.jar /app/vaelii.jar

# The class-loading cache the entry point reads (`-XX:AOTCache`).  A training run of
# the daemon itself — up on a scratch store until `/health` answers, then stopped, the
# cache written at its exit — so the cache holds what a start loads.  It is built here
# rather than in the build stage because a cache is valid only for the JVM build and the
# jar that made it, and these are the ones the container runs; the flags match the
# entry point's for the same reason.  A daemon over an empty store that reads it answers
# `/health` in 0.58 s against 1.61 s without (2026-09-28), for about 90 MB of image.
RUN java --enable-native-access=ALL-UNNAMED --sun-misc-unsafe-memory-access=allow \
         -XX:+UseCompactObjectHeaders -XX:AOTCacheOutput=/app/vaelii.aot \
         -cp /app/vaelii.jar clojure.main -m vaelii.host.serve 4299 /tmp/aot-train & \
    pid=$! \
 && for _ in $(seq 1 120); do curl -fsS http://127.0.0.1:4299/health && break; sleep 1; done \
 && kill "$pid" && wait "$pid"; \
    test -s /app/vaelii.aot && rm -rf /tmp/aot-train

# The store.  One container per directory: the `:disk` backend takes an exclusive
# file lock on open and a second opener is refused with `:disk-locked`, so
# scaling this service by replica count over one volume is a configuration error
# rather than throughput.
VOLUME /var/lib/vaelii
USER vaelii
EXPOSE 4200

# Unset, the engine installs no backend and Trove's own console backend prints at
# :info.  The image names a level, which installs the engine's one-line backend, and
# the operator can override it.
ENV VAELII_LOG_LEVEL=info

# No `-Xmx`.  A JVM in a container reads the cgroup limit, so the operator's
# `--memory` is the heap ceiling; a baked value would override it and be wrong at
# every size but the one it was written for.
#
# No collector flag either, and that is a measured answer rather than an omission.
# `lein perf` over two alternating passes at a fixed 6 GiB heap: the JDK default
# took 40.7-41.2 s at 1493-1510 MB peak RSS, generational ZGC 55.5-55.9 s at
# 6224-6258 MB — 36% slower holding 4.2x the resident set, and ZGC alone tripped
# the `:negation-arbitration` growth bound on both passes.  A concurrent collector
# earns its throughput cost on a live set of tens of gigabytes, and this engine's
# peak here is 1.5 GB — and in a container the resident set is what the memory limit
# is set against.  `lein with-profile +zgc` selects it for a JVM that has a reason.
#
# `clojure.main -m` rather than `java -jar`: `:gen-class` is on `vaelii.core`, so
# the jar's Main-Class is the API entry point and not this one.
#
# The first three flags are project.clj's top-level `:jvm-opts`, which an uberjar does
# not carry: without the two `--` ones JDK 25 warns when JNA loads a native solver and
# when nippy's LZ4 (aircompressor) calls `sun.misc.Unsafe`, and compact object headers
# hold about 8% less heap.  `-XX:AOTCache` reads the cache the training run above wrote.
ENTRYPOINT ["java", "--enable-native-access=ALL-UNNAMED", "--sun-misc-unsafe-memory-access=allow", \
            "-XX:+UseCompactObjectHeaders", "-XX:AOTCache=/app/vaelii.aot", \
            "-cp", "/app/vaelii.jar", "clojure.main", "-m", "vaelii.host.serve"]

# `[port [dir]] [--listen ADDR]`.  Binding an address inside the container is what
# lets a published port reach the daemon — and the daemon refuses that bind unless
# `VAELII_API_TOKEN` is set, exiting 2 before it opens the KB.  So an image run
# without a token does not serve unauthenticated; it does not start.
CMD ["4200", "/var/lib/vaelii", "--listen", "0.0.0.0"]

# `/health` is the one route that answers without the token — a daemon only its
# token-holder can probe is one no orchestrator can watch.  The start period is
# generous because a restart over a populated volume runs `recover`, one pass over
# every stored record, before Jetty accepts its first connection.
HEALTHCHECK --interval=30s --timeout=3s --start-period=120s --retries=3 \
  CMD curl -fsS http://127.0.0.1:4200/health || exit 1
