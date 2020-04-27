#!/bin/bash

if [ "$1" == "-h" ]; then
  echo "Usage: `basename $0` [scope] [name of the file with the spec]"
  exit 0
fi

if [ "$#" -ne 2 ]; then
    echo "Illegal number of parameters"
    exit 1
fi

export PhilStone='../'
if ! [ -x "$(command -v NuSMV)" ]; then
  echo 'Error: NuSMV is not installed.' >&2
  exit 1
fi

if [[ "$OSTYPE" == "darwin"* ]]; then
	export JAVA_LIBRARY_PATH="../lib/MacOs/"
elif [[ "$OSTYPE" == "linux"* ]]; then
	export LD_LIBRARY_PATH='../lib/AMD64/'
	export CLASSPATH='../jar/java-cup-11a.jar:../jar/*:$CLASSPATH:.'
fi

java PS/PhilStone -NuSMV -scope=$1 -pdf $2
