#!/bin/bash

dk dep $@ | cut -d ":" -f 2 | sed "s/ /\n/g" | grep ".dko$" | sed "s/\(.*\)\.dko$/require coq.\\1 as \\1;/g"
