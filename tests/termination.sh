#!/bin/sh
# Test XTC export
set -euf

ko() {
    printf '\033[31mKO\033[0m %s\n' "$1"
    exit 1
}

ok() {
    printf '\033[32mOK\033[0m %s\n' "$1"
}

checker='cat > /dev/null; echo YES'
if lambdapi check -v 0 --termination "$checker" tests/OK/nat.lp 2> /dev/null
then
    ok "tests/OK/nat.lp"
else
    ko "tests/OK/nat.lp"
fi
exit 0