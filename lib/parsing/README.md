HDDL Parser
===========

This directory contains code to parse HDDL domains and problems.

Notes
-----

We deviate from the HDDL standard in a couple of ways.

- Parsing is case-sensitive. We'll probably fix this later, but for now keep
  this in mind when writing HDDL domain and problem definitions.
- For quantified FOL sentences (exists/forall), we deviate from the EBNF
  specification by requiring a single typed list of variables instead of zero
  or more after the quantifier.
