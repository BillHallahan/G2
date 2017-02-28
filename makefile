FLAGS = -package ghc
CORE_SRC   = src/G2/Core
SMT_SRC    = src/G2/SMT
SAMPLE_SRC = src/G2/Sample
HSK_SRC    = src/G2/Haskell
HSK_TEST   = src/G2/Haskell/test

all:
	ghc ${FLAGS} \
  src/Main.hs ${CORE_SRC}/*.hs ${SMT_SRC}/*.hs ${SAMPLE_SRC}/*.hs ${HSK_SRC}/*.hs \
          ${HSK_TEST}/*.hs \
  -odir build/ -o G2 && \
  rm src/*.hi ${CORE_SRC}/*.hi ${SMT_SRC}/*.hi ${SAMPLE_SRC}/*.hi ${HSK_SRC}/*.hi \
          ${HSK_TEST}/*.hi

clean:
	rm -rf G2 build/*

