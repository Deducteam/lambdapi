#!/bin/sh
# Test Lambdapi decision-tree command

set -uf

ko() {
    printf '\033[31mKO\033[0m %s\n' "$1"
    exit 1
}

ok() {
    printf '\033[32mOK\033[0m %s\n' "$1"
}

LAMBDAPI="lambdapi decision-tree --verbose 0 \
--map-dir=tests:tests"

out="$(${LAMBDAPI} tests.OK.nat.+)"
if [ -z "$out" ]; then
    ko 'tests.OK.nat.+'
else
    ok 'tests.OK.nat.+'
fi

# Escaped characters (with no rule)
out="$(${LAMBDAPI} 'tests.OK.parsing.Escaped.{|KIND|}' 2>/dev/null)"
if [ "$?" = 1 ]; then
    ko 'tests.OK.parsing.Escaped.{|KIND|}'
fi
if [ -z "$out" ]; then
    ok 'tests.OK.parsing.Escaped.{|KIND|}'
fi

# Escaped with dots (no rule on symbol)
out="$(${LAMBDAPI} 'tests.OK.parsing.Escaped.{|KIND.OF.BLUE|}' 2>/dev/null)"
if [ "$?" = 1 ]; then
    ko 'tests.OK.parsing.Escaped.{|KIND.OF.BLUE|}'
fi
if [ -z "$out" ]; then
    ok 'tests.OK.parsing.Escaped.{|KIND.OF.BLUE|}'
fi

# Escaped with rules
out="$(${LAMBDAPI} 'tests.OK.parsing.Escaped.{|set|}' 2>/dev/null)"
if [ -z "$out" ]; then
    ko 'tests.OK.parsing.Escaped.{|set|}'
else
    ok 'tests.OK.parsing.Escaped.{|set|}'
fi

# Ghost symbols
# TODO put back tests.OK.unif_hint.#equiv when OK/unif_hint.lp is fixed
# out="$(${LAMBDAPI} 'tests.OK.unif_hint.#equiv' 2>/dev/null)"
# if [ "$?" = 1 ] || [ -z "$out" ]; then
#     ko 'tests.OK.unif_hint.#equiv'
# else
#     ok 'tests.OK.unif_hint.#equiv'
# fi
exit 0
