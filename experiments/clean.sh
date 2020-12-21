#!/bin/bash

[ "$1" = "-f" ] && force=yes || force=no

pattern='.*\(boolector\|btormc\|cvc4\)-\(btor2\|functional\|relational\)\..*'

find $(dirname $0)/litmus -regex $pattern | sort
find $(dirname $0)/count -name buggy.* -o -name cas.* -type d | sort
