#!/bin/bash

P="3 3 3"
V="3 3 3"
M="1 2 2"
R="3 3 3"
X="1 1 3"

for i in $(seq 1 3) ; do
	echo $i
	PP=$(echo $P | cut -d' ' -f $i)
	VV=$(echo $V | cut -d' ' -f $i)
	MM=$(echo $M | cut -d' ' -f $i)
	RR=$(echo $R | cut -d' ' -f $i)
	XX=$(echo $X | cut -d' ' -f $i)
    python sar_generator.py -p $PP -v $VV -m $MM -r $RR -x $XX> probs_generated/testProblem$(printf "_%01d-%01d-%01d" $PP $VV $RR).hddl
done
