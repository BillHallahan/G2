FLAGS = -package ghc
CORE_SRC   = G2/Core
SMT_SRC    = G2/SMT
SAMPLE_SRC = G2/Sample
HSK_SRC    = G2/Haskell
HSK_TEST   = G2/Haskell/test

all:
	ghc ${FLAGS} \
  Main.hs ${CORE_SRC}/*.hs ${SMT_SRC}/*.hs ${SAMPLE_SRC}/*.hs ${HSK_SRC}/*.hs \
          ${HSK_TEST}/*.hs \
  -odir build/ -o G_2 && \
  rm *.hi ${CORE_SRC}/*.hi ${SMT_SRC}/*.hi ${SAMPLE_SRC}/*.hi ${HSK_SRC}/*.hi \
          ${HSK_TEST}/*.hi

clean:
	rm -rf G_2 build/*

