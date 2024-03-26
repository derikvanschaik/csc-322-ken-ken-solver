#!/usr/bin/env python3

import sys
import re


smt_output = "".join([line for line in sys.stdin])


if len(smt_output.split("\n")) == 0:
    print("unsatisfiable")

if smt_output.split("\n")[0] == "sat":
    pattern = re.compile(r"\(V\d+\s(\d+)\)")

    values = pattern.findall(smt_output)
    values = [value for value in values]

    print("".join(values))
else:
    print("unsatisfiable")
