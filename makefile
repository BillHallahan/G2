FLAGS = -package ghc
CORE_SRC   = src/Core
SAMPLE_SRC = src/Sample

all:
	ghc ${FLAGS} Main.hs ${CORE_SRC}/*.hs ${SAMPLE_SRC}/*.hs \
  -odir build/ -o G2 && \
  rm *.hi ${CORE_SRC}/*.hi ${SAMPLE_SRC}/*.hi

clean:
	rm -rf G2 build/*

