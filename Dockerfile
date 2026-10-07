# ============================================================
# G2 Docker image
#
# Target architectures:
#   linux/arm64
#   linux/amd64
#
# Versions:
#   GHC   9.12.2
#   Cabal 3.14.1.0+
#   Z3    5.1.0
#   cvc5  1.3.4
# ============================================================

FROM debian:13

ARG TARGETARCH

ENV DEBIAN_FRONTEND=noninteractive

# ------------------------------------------------------------
# System dependencies
# ------------------------------------------------------------

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        wget \
        git \
        unzip \
        build-essential \
        cmake \
        pkg-config \
        python3 \
        libgmp-dev \
        libffi-dev \
        zlib1g-dev \
        libncurses-dev \
        && \
    rm -rf /var/lib/apt/lists/*

# ------------------------------------------------------------
# Install Cabal and GHC
# ------------------------------------------------------------

RUN curl --proto '=https' --tlsv1.2 -sSf \
    https://get-ghcup.haskell.org \
    | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
      BOOTSTRAP_HASKELL_GHC_VERSION=9.12.2 \
      BOOTSTRAP_HASKELL_CABAL_VERSION=3.14.2.0 \
      sh

ENV PATH="/root/.ghcup/bin:${PATH}"

RUN ghc --version && \
    cabal --version

# ------------------------------------------------------------
# Install Z3 5.1.0
# ------------------------------------------------------------

RUN if [ "${TARGETARCH}" = "arm64" ]; then \
        Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-arm64-glibc-2.38.zip"; \
        Z3_File="z3-5.1.0-arm64-glibc-2.38"; \
    elif [ "${TARGETARCH}" = "amd64" ]; then \
        Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-x64-glibc-2.39.zip"; \
        Z3_File="z3-5.1.0-x64-glibc-2.39"; \
    else \
        echo "Unsupported architecture: ${TARGETARCH}"; \
        exit 1; \
    fi && \
    curl -L -o z3.zip ${Z3_URL} \
    && unzip z3.zip \
    && mv ${Z3_File}/bin/z3 /usr/local/bin/z3 \
    && rm -rf z3.zip ${Z3_File}

RUN echo "Z3 version:" && \
    z3 --version

# ------------------------------------------------------------
# Install CVC5 1.3.4
# ------------------------------------------------------------
RUN if [ "${TARGETARCH}" = "arm64" ]; then \
        CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-arm64-static.zip"; \
        CVC5_File="cvc5-Linux-arm64-static"; \
    elif [ "${TARGETARCH}" = "amd64" ]; then \
        CVC5_URL="https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.4/cvc5-Linux-x86_64-static.zip"; \
        CVC5_File="cvc5-Linux-x86_64-static"; \
    else \
        echo "Unsupported architecture: ${TARGETARCH}"; \
        exit 1; \
    fi && \
    curl -L -o cvc5.zip ${CVC5_URL} \
    && unzip cvc5.zip \
    && mv ${CVC5_File}/bin/cvc5 /usr/local/bin/cvc5 \
    && rm -rf cvc5.zip ${CVC5_File}

RUN chmod +x /usr/local/bin/cvc5

RUN echo "cvc5 version:" && \
    cvc5 --version

# ------------------------------------------------------------
# Copy the COMPLETE G2 from local system to docker
# ------------------------------------------------------------

WORKDIR /g2

COPY . .

# ------------------------------------------------------------
# Build G2
# ------------------------------------------------------------

RUN cabal update

RUN cabal build --only-dependencies -j1

RUN ./base_setup.sh

RUN cabal build G2 -j1

WORKDIR /g2

# ENTRYPOINT ["g2"]