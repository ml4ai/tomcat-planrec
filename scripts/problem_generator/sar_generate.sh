#!/bin/bash

P="1 2 3"
V="1 2 2"
S="1 2 3"
R="1 1 1"

for i in $(seq 1 3) ; do
	echo $i
	PP=$(echo $P | cut -d' ' -f $i)
	VV=$(echo $V | cut -d' ' -f $i)
	SS=$(echo $S | cut -d' ' -f $i)
	RR=$(echo $R | cut -d' ' -f $i)
	python sar_generator.py -p $PP -v $VV -s $SS -r $RR> problem$(printf "%02d" $i).hddl
done
