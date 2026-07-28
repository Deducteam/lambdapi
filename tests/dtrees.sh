#!/bin/sh

set -uf

dune build

echo '############ test decision-tree ############'

ko() {
    printf '\033[31mKO\033[0m %s\n' "$1"
    exit 1
}

ok() {
    printf '\033[32mOK\033[0m %s\n' "$1"
}

lambdapi='_build/install/default/bin/lambdapi'
cmd='decision-tree -v0 -w --map-dir=tests:tests'

out="$($lambdapi $cmd tests.OK.natural.+)"
if [ -z "$out" ]; then
    ko 'tests.OK.nat.+'
else
    ok 'tests.OK.nat.+'
fi

# Escaped identifier with no rule
out="$($lambdapi $cmd 'tests.OK.Escaped.{|KIND|}' 2>/dev/null)"
if [ "$?" = 1 ]; then
    ko 'tests.OK.Escaped.{|KIND|}'
fi
if [ -z "$out" ]; then
    ok 'tests.OK.Escaped.{|KIND|}'
fi

# Escaped identifier with dots and no rule
out="$($lambdapi $cmd 'tests.OK.Escaped.{|KIND.OF.BLUE|}' 2>/dev/null)"
if [ "$?" = 1 ]; then
    ko 'tests.OK.Escaped.{|KIND.OF.BLUE|}'
fi
if [ -z "$out" ]; then
    ok 'tests.OK.Escaped.{|KIND.OF.BLUE|}'
fi

# Escaped identifier with rules
out="$($lambdapi $cmd 'tests.OK.Escaped.{|_set|}' 2>/dev/null)"
if [ "$?" = 1 ] || [ -z "$out" ]; then
    ko 'tests.OK.Escaped.{|_set|}'
else
    ok 'tests.OK.Escaped.{|_set|}'
fi

# Ghost symbol
out="$($lambdapi $cmd --ghost 'tests.OK.unif_hint.≡' 2>/dev/null)"
if [ "$?" = 1 ] || [ -z "$out" ]; then
    ko 'tests.OK.unif_hint.≡'
else
    ok 'tests.OK.unif_hint.≡'
fi

exit 0
