#!/usr/bin/env python3

import sys
import re


smt_output = "".join([line for line in sys.stdin])
pattern = re.compile(r"\(V\d+\s(\d+)\)")

values = pattern.findall(smt_output)
values = [value for value in values]


print("".join(values))
