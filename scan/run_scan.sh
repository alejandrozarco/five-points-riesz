#!/bin/bash
# How the data in this directory were produced (2026-10-03/04, macOS arm64, Clarabel 0.11.1; see ../README.md).
#
# sharpness_scan.jsonl: degree 10 (rows of the two rounds; failed solver runs are recorded as "error" rows):
#   POLYD=10 python3 sharpness_scan.py 0.5 1 1.5 2 2.5 3 4 5 6 7 8 9 10 11 12 13 14 15
#   POLYD=10 python3 sharpness_scan.py 1.45 2.55 4.05 5.05 8.05 9.05
# sharpness_scan_cap.jsonl: degree 10 with a five times larger cap:
#   CAPF=5 POLYD=10 OUT=sharpness_scan_cap.jsonl python3 sharpness_scan.py 10
#
# superseded_fixed_sos_degree.jsonl: runs at degrees 12 and 14 made before a fix in three_point_bound.py, which then
#   kept the SOS multiplier degrees at their degree-10 values (5, 4, 3) for every D, i.e. a restricted SDP (found by an
#   AI review). Not used in the README or the figure.
# rerun_fixed_sos_degree.jsonl: the same points rerun after the fix (degree 12; one point at degree 14): Clarabel
#   failed on all but one of them. Not used in the README or the figure.
cd "$(dirname "$0")"
POLYD=10 python3 sharpness_scan.py 0.5 1 1.5 2 2.5 3 4 5 6 7 8 9 10 11 12 13 14 15
