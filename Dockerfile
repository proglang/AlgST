###############################################################################
# AlgST executable                                                            #
###############################################################################

FROM haskell:9.2.7-slim-buster AS algst

WORKDIR /opt/build

# Copy only files necessary to derive dependencies.
COPY package.yaml stack.yaml stack.yaml.lock /opt/build/

# We could request to build the dependecies required for the executable only
# but this would lead to a full rebuild should the user issue a `stack test`.
# Therefore we simply build *all* the dependencies beforehand.
ARG BUILD_OPTS=
RUN stack build $BUILD_OPTS --test --no-run-tests --dependencies-only

# To ensure that we print any error messages from unit test (which are run in
# the next step) in a nice way.
ENV LANG=C.UTF-8

# Copy all the other files and build `algst`.
COPY src   /opt/build/src
COPY exe   /opt/build/exe
COPY tests /opt/build/tests
RUN stack build $BUILD_OPTS --test --copy-bins


###############################################################################
# FreeST benchmarker                                                          #
###############################################################################

FROM haskell:8.10.7-slim-buster AS freest

WORKDIR /opt/build

# Copy the files we need to build.
COPY benchmarks/cabal.project benchmarks/cabal.project.freeze /opt/build
COPY benchmarks/FreeST    /opt/build/FreeST
COPY benchmarks/overrides /opt/build/overrides

# Build and install the `freest-bench` executable.
ARG BUILD_OPTS=
RUN cabal update && cabal install $BUILD_OPTS freest-bench


###############################################################################
# Assembling the final image                                                  #
###############################################################################

FROM debian:buster-slim

# Install some runtime dependencies.
RUN apt-get update && apt-get install -y --no-install-recommends \
  libnuma1 \
  libgmp10

# Install some nice utilities.
RUN apt-get install -y --no-install-recommends \
  nano

# Copy the examples.
WORKDIR /opt/algst
COPY examples /opt/algst

# Copy the benchmark test-cases.
COPY benchmarks/test-cases /opt/algst/benchmarks/test-cases

# Copy the benchmarks runner. 
COPY benchmarks/run-benchmarks.sh /usr/local/bin

# Copy the executables.
COPY --from=algst  /root/.local/bin/algst        /usr/local/bin
COPY --from=freest /root/.cabal/bin/freest-bench /usr/local/bin

# Otherwise any of the quotations ‘like this’ in error messages and
# informational messages are replaced by ‘?’.
ENV LANG=C.UTF-8
