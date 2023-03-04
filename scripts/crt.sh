#!/bin/bash


# Script folder
EXE_DIR=$(dirname $(readlink -f $0));

# Data / Logs folder
DATA_ROOT=$(dirname ${EXE_DIR});
DATA_DIR="${DATA_ROOT}/data"; 
LOGS_DIR="${DATA_ROOT}/logs";

# Just check that parent folders are indeed where they should be
[[ ! -d ${DATA_DIR} ]] && {
    echo -e "\x1b[31m[Err]\x1b[0m Data directory ${DATA_DIR} does not exist.";
    exit 1;
};

[[ ! -d ${LOGS_DIR} ]] && {
    echo -e "\x1b[31m[Err]\x1b[0m Logs directory ${LOGS_DIR} does not exist.";
    exit 1;
};


NUMBER_TESTS=10


# compute timings for double-crt method à la Thomé
for p in "$@"; do
    prime="$p"

    sage ${EXE_DIR}/crt.sage ${prime} ${NUMBER_TESTS}  1>${LOGS_DIR}/crt_${prime} 2>&1 &

    sage ${EXE_DIR}/crt_nfroots.sage ${prime} ${NUMBER_TESTS} 1>${LOGS_DIR}/crt_${prime}_nfroots 2>&1 &

done;

exit 0;
