#!/bin/bash

awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' src/*.ml
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' src/*.ml
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' src/*.ml

awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' src/pure/*.ml src/pure/*.mli
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' src/pure/*.ml src/pure/*.mli
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' src/pure/*.ml src/pure/*.mli

#awk 'length>78 {print "In " FILENAME ", line " FNR " more than 78 characters..."}' lp-lsp/*.ml
awk '/.*\s$/   {print "In " FILENAME ", line " FNR " has trailing spaces..."}    ' lp-lsp/*.ml
awk '/.*\t.*/  {print "In " FILENAME ", line " FNR " contains tabulations..."}   ' lp-lsp/*.ml
