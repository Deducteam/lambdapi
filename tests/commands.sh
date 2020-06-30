#!/bin/sh
# commands.sh    Test Lambdapi commands

set -eu

ko() {
    printf '\033[31mKO\033[0m %s\n' "$1"
    exit 1
}

ok() {
    printf '\033[32mOK\033[0m %s\n' "$1"
}

LAMBDAPI="lambdapi decision-tree --verbose 0 \
    --lib-root=lib --map-dir=tests:tests"

printf '## decision-tree tests ##\n'

out="$(${LAMBDAPI} tests.OK.nat.add)"
if [ -z "$out" ]; then
    ko 'tests.OK.nat.add'
else
    ok 'tests.OK.nat.add'
fi

# Escaped characters (with no rule)
out="$(${LAMBDAPI} 'tests.OK.Escaped.{|KIND|}' 2>/dev/null)"
if [ "$?" = 1 ]; then
    ko 'tests.OK.Escaped.{|KIND|}'
fi
if [ -z "$out" ]; then
    ok 'tests.OK.Escaped.{|KIND|}'
fi

# Escaped with dots (no rule on symbol)
out="$(${LAMBDAPI} 'tests.OK.Escaped.{|KIND.OF.BLUE|}' 2>/dev/null)"
if [ "$?" = 1 ]; then
    ko 'tests.OK.Escaped.{|KIND.OF.BLUE|}'
fi
if [ -z "$out" ]; then
    ok 'tests.OK.Escaped.{|KIND.OF.BLUE|}'
fi

# Escaped with rules
out="$(${LAMBDAPI} 'tests.OK.Escaped.{|set|}' 2>/dev/null)"
if [ -z "$out" ]; then
    ko 'tests.OK.Escaped.{|set|}'
else
    ok 'tests.OK.Escaped.{|set|}'
fi

# Ghost symbols
out="$(${LAMBDAPI} 'tests.OK.unif_hint.#equiv' 2>/dev/null)"
if [ "$?" = 1 ] || [ -z "$out" ]; then
    ko 'tests.OK.unif_hint.#equiv'
else
    ok 'tests.OK.unif_hint.#equiv'
fi
