#!/bin/sh
cabal run G2 $1 $2 -- --include nofib-symbolic/common --higher-order symbolic --hpc --hpc-print-times --print-num-nrpc \
                      --print-num-red-rules --solver-time --print-num-solver-calls --print-num-higher-states \
                      --no-step-limit --search subpath --subpath-len 2 --hpc-discard-strat --measure-coverage  --time 40 \
                      --print-encodeFloat \
                      --higher-nrpc \
                    # --log-pretty a_digits
                    #  --log-pretty a_exp --log-inline-nrpc --log-path "[1,1,1,1,2,2,1,2,1,1]" \
                    #   --states-at-time \
