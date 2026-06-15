#!/usr/bin/env bash
set -e
if grep -rn 'sorry\|admit' Src/ 2>/dev/null | grep -v '^Binary'; then echo FAIL; exit 1; fi
echo PASS
