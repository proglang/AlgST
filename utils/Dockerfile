# For a smaller final image we do a multi-stage build.
FROM haskell:9.0.2-slim AS builder

WORKDIR /opt/algst

# Copy only files necessary to derive dependencies.
COPY package.yaml stack.yaml stack.yaml.lock /opt/algst/

# We could request to build the dependecies required for the executable only
# but this would lead to a full rebuild should the user issue a `stack test`.
# Therefore we simply build *all* the dependencies beforehand.
RUN stack build --test --no-run-tests --dependencies-only

# Copy all the other files and build `algst`.
#
# Most of the time building only the executable will suffice. However,
# executing a `stack test` afterwards will rebuild the library. Therefore we
# just build everything. The increase in build time is small compared to
# building everything when running the tests.
COPY . /opt/algst/
RUN stack build --test --no-run-tests --copy-bins

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

# Default to running a shell.
CMD "bash"
