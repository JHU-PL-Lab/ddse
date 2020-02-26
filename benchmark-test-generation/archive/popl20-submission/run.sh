#!/usr/bin/env bash

set -o errexit
set -o pipefail
set -o nounset
set -o xtrace

echo "START"

TRIALS=3
TIMEOUT=10m

CASES=(
#  "input_facehugger_top"
#  "input_facehugger_bottom"
#  "input_ack_a"
#  "input_ack_b"
#  "input_tak"
#  "input_cptak"
#  "input_blur"
#  "fig4_1_1"
#  "fig4_1_2"
#  "fig4_2_1"
#  "fig4_2_2"
#  "fig4_3_1"
#  "fig4_3_2"
# the followings will timeout  
#  "fig4_1_3"
#  "fig4_3_3"
#  "fig4_4_1"
#  "fig6_1_1"
#  "fig6_2_1"
)

HERE="$(cd "$(dirname $0)" && pwd)"
CASES_PATH="${HERE}"
RESULTS_PATH="${HERE}/results"
DDSE="${HERE}/.."
DDSE_TOPLOOP="${DDSE}/test_generator"
STRATEGY="relstack-rep"

# date --iso-8601=seconds

mkdir -p $HERE/results

lscpu
cat /proc/cpuinfo
free -m
cat /proc/meminfo
uname -a
lsb_release -a

(cd "${DDSE}" && git rev-parse HEAD)
ocaml -version
opam --version

function result {
  RESULT=${RESULTS_PATH}/${CASE}-$(date -u +"%Y-%m-%dT%H:%M:%SZ").txt
  echo &> ${RESULT}
  uptime &> ${RESULT}
}

function ddse {
  result
  /usr/bin/time /usr/bin/timeout --foreground "${TIMEOUT}" "${DDSE_TOPLOOP}" -r 1 -e "${STRATEGY}" -t target "${SOURCE}" 1>>${RESULT} 2>&1 || true
}

# function ddse {
#   ANALYSIS=ddpa
#   result
#   cat "${SOURCE}" | racket "${SCHEME_TO_ODEFA}" | /usr/bin/time -v /usr/bin/timeout --foreground "${TIMEOUT}" "${DDPA_TOPLOOP}" --select-context-stack="${K}"ddpa --analyze-variables=all --report-sizes --report-source-statistics --disable-evaluation --disable-inconsistency-check &>> "${RESULT}" || true
# }

mkdir -p "${RESULTS_PATH}"
(cd "${DDSE}" && make)

for TRIAL in $(seq 1 "${TRIALS}");
do
  for CASE in "${CASES[@]}";
  do
    SOURCE="${CASES_PATH}/${CASE}.natodefa"
    ddse
  done
done

echo "END"
