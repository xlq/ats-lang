#!/bin/bash

if [ ${ATSHOME} != ${PWD} ] ; then
  echo "The value of ATSHOME is set to \"${ATSHOME}\", but it should be set to \"${PWD}\"!"; exit 1;
fi

### end of [ATSHOME_check.sh] ###
