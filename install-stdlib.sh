#!/bin/bash

readonly AGDA_DIR=$HOME/.agda
readonly AGDA_VERSION=2.5.1.1

if [ -d $AGDA_DIR/lib/agda-stdlib-0.12 ]; then
    echo "ERROR: standard library already exists in $AGDA_DIR/lib/agda-stdlib-0.12" >&2
    exit 1
fi

mkdir -p $AGDA_DIR/lib
curl -L https://github.com/agda/agda-stdlib/archive/v0.12.tar.gz \
    | tar -xzC $AGDA_DIR/lib
echo 'standard-library' > $AGDA_DIR/defaults
echo '${AGDA_DIR}/lib/agda-stdlib-0.12/standard-library.agda-lib' \
    > $AGDA_DIR/libraries-$AGDA_VERSION
