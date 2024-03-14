ex = """r1.16+,r2.3+,r2,r3.2-,r3,r4.4-,r4
r1,r1,r5.10+,r6.3+,r6,r7.7+,r7
r8.5+,r9.12+,r5,r10.13+,r11.6-,r12.4-,r12
r8,r9,r9,r10,r11,r13.9+,r13
r14.4+,r14,r15.11+,r15,r16.4,r17.13+,r18.3+
r19.11+,r20.6-,r21.12+,r22.5+,r22,r17,r18
r19,r20,r21,r21,r23.3-,r23,r24.6"""

import re

# from above we see that format can be
# r_<number>.<number><operator>
#  always   |  optional
# pattern = re.compile(r"(r\d+)(?:\.(\d+)([+\-*/]))?")
pattern = re.compile(r"(r\d+)(?:\.(\d+)([+\-*/])?)?")

# TODO: replce with n instead of hardcoded
variables = [f"V{num}" for num in range((7 * 7))]
rules = []
for line in ex.split("\n"):
    rs = line.split(",")
    for r in rs:
        rules.append(r)
# ex
# { r33 : { variables: [V0, V18, V19..], operator: -, value: 9 }}
rule_mapper = {}

for index, r in enumerate(rules):
    variable = variables[index]

    match = pattern.match(r)
    region, value, operation = None, None, None
    if match:
        region = match.group(1)
        if match.group(2):
            value = match.group(2)
        if match.group(3):
            operation = match.group(3)

        if region not in rule_mapper:
            rule_mapper[region] = {
                "variables": [variable],
                "operator": operation,
                "value": value,
            }
        else:
            rule_mapper[region]["variables"].append(variable)

print(rule_mapper)
