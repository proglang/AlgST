# For a smaller final image we do a multi-stage build.
FROM haskell:9.2.5-slim-buster AS builder

WORKDIR /opt/algst

# Copy only files necessary to derive dependencies.
COPY package.yaml stack.yaml stack.yaml.lock /opt/algst/

# We could request to build the dependecies required for the executable only
# but this would lead to a full rebuild should the user issue a `stack test`.
# Therefore we simply build *all* the dependencies beforehand.
RUN stack build --test --no-run-tests --dependencies-only

# Copy all the other files and build `algst`.
COPY . /opt/algst/
RUN stack build --test --copy-bins

# Haskell 9.0.2 uses debian:buster.
FROM debian:buster-slim

# Install some runtime dependencies.
RUN apt-get update && apt-get install -y --no-install-recommends \
  libnuma1 \
  libgmp10

# Copy the examples.
WORKDIR /opt/algst
COPY examples /opt/algst

# Copy the executable.
COPY --from=builder /root/.local/bin/algst /usr/local/bin

ENTRYPOINT ["algst"]
