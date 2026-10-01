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

FROM haskell:9.12.2

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
        z3 \
        cvc5 \
        && \
    rm -rf /var/lib/apt/lists/*

# ------------------------------------------------------------
# Verify compiler/toolchain
# ------------------------------------------------------------

RUN echo "Target architecture: ${TARGETARCH}" && \
    ghc --version && \
    cabal --version


RUN echo "cvc5 version:" && cvc5 --version

# ------------------------------------------------------------
# G2
# ------------------------------------------------------------

WORKDIR /g2

# Copy Cabal files first so Docker can cache dependency
# resolution when G2 source files change.

RUN git clone https://github.com/BillHallahan/G2.git

RUN git clone https://github.com/BillHallahan/base-4.9.1.0.git ~/.g2/base-4.9.1.0/

RUN git clone https://github.com/BillHallahan/G2Stubs.git ~/.g2/G2Stubs/

COPY . .

RUN pwd

RUN cabal update

RUN cabal build --only-dependencies

# ------------------------------------------------------------
# Build G2
# ------------------------------------------------------------

RUN ./base_setup.sh

RUN cabal build

WORKDIR /g2

# ENTRYPOINT ["g2"]