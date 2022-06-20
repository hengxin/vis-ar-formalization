#!/bin/bash

TESTSFILE=$1
ALLOYPATH=.

echo "# Tests file: $TESTSFILE"
echo "# bound: $2"

java $JAVAFLAGS -classpath $ALLOYPATH:$ALLOYPATH/alloy4.2.jar XmlGenerator -f $TESTSFILE -b ${@:2}