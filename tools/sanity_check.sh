#!/bin/bash

awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' src/lambdapi.ml
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' src/lambdapi.ml
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' src/lambdapi.ml

awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' src/pure/*.ml src/pure/*.mli
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' src/pure/*.ml src/pure/*.mli
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' src/pure/*.ml src/pure/*.mli

awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' src/core/*.ml
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' src/core/*.ml
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' src/core/*.ml

#awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' lp-lsp/*.ml
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' src/lsp/*.ml src/lsp/*.mli
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' src/lsp/*.ml src/lsp/*.mli
