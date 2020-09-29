#!/bin/sh
# xtc.sh         Test XTC export
set -euf

ko() {
    printf '\033[31mKO\033[0m %s\n' "$1"
    exit 1
}

ok() {
    printf '\033[32mOK\033[0m %s\n' "$1"
    exit 0
}

LAMBDAPI="lambdapi check --termination 'cat > /dev/null; printf YES' \
--verbose 0"

if ${LAMBDAPI} tests/OK/nat.lp 2>/dev/null; then
    ko "XTC"
else
    ok "XTC"
fi
exit 0
