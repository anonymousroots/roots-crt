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

for r in "$@"; do
    exp_range="$r"

    sage ${EXE_DIR}/cf_roots_twphs_saturation_good.sage "max" ${exp_range}  1>${LOGS_DIR}/twphs_sat_good_max_${exp_range} 2>&1 &

    sage ${EXE_DIR}/cf_roots_twphs_saturation_good_nfroots.sage "max" ${exp_range}  1>${LOGS_DIR}/twphs_sat_good_max_${exp_range}_nfroots 2>&1 &

done ;

exit 0;
