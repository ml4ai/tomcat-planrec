#!/bin/bash

P="1 2"
V="1 2"
S="1 2"
R="1 2"

for i in $(seq 1 3) ; do
	echo $i
	PP=$(echo $S | cut -d' ' -f $i)
	VV=$(echo $V | cut -d' ' -f $i)
	SS=$(echo $S | cut -d' ' -f $i)
	RR=$(echo $R | cut -d' ' -f $i)
	python sar_generator.py -p $P -v $V -s $SS -r $RR> problem$(printf "%02d" $i).hddl
done
