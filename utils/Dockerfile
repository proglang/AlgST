FROM haskell:9.0.2

WORKDIR /opt/algst

# Copy only files necessary to derive dependencies.
COPY package.yaml stack.yaml stack.yaml.lock /opt/algst/
RUN stack build AlgST:exe:algst --dependencies-only

# Copy all the other files and build `algst`.
COPY . /opt/algst/
RUN stack build AlgST:exe:algst --copy-bins

# Default to running a shell inside the example directory.
WORKDIR /opt/algst/examples
CMD "bash"
