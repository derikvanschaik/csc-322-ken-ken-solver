import re
from itertools import permutations


# parses raw ken ken, returns dict of form
# { r33 : { variables: [V0, V18, V19..], operator: -, value: 9 }}
def parse_rules(unparsed, n=7):
    # from above we see that format can be
    # r_<number>.<number><operator>
    #  always   |  optional
    pattern = re.compile(r"(r\d+)(?:\.(\d+)([+\-*/])?)?")

    variables = [f"V{num}" for num in range((n * n))]
    rules = []
    for line in unparsed.split("\n"):
        rs = line.split(",")
        for r in rs:
            rules.append(r)

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

    return rule_mapper


"""

(assert (= 48 (* V51 V60))) ; Region gg
(assert (or (= 2 (- V34 V43))(= 2 (- V43 V34)))) ;
Region u
(assert (= 3 (+ V19 V20))) ; Region d
(assert (or (= 2 (- V39 V40))(= 2 (- V40 V39)))) ;
Region s
(assert (= 13 (+ V70 V79))) ; Region ab

"""


def region_constraints(parse_rules):
    constraints = []
    for region in parse_rules.keys():
        ## TODO: how would r.24.6 rule be created...?
        # maybe (assert (= 6 V24)) ? or (assert (= V24 6))
        # only thinking the second since prefix notation would write like that..
        variables = parse_rules[region]["variables"]
        operator = parse_rules[region]["operator"]
        value = parse_rules[region]["value"]

        const = ""
        variable_constraints = ""

        if operator in ("*", "+"):
            variable_constraints = f'({operator} {" ".join(variables)})'
            const = f"(= {value} {variable_constraints}))"

        elif operator in ("/", "-"):
            variable_perm = list(permutations(variables))
            for perm in variable_perm:
                variable_constraints += f'(= {value} ({operator} {" ".join(perm)}))'

            variable_constraints = f"(or {variable_constraints})"
            const = variable_constraints

        # single assignment -- don't really know yet what to do here
        else:
            pass

        constraint = f"(assert {const} ; Region {region}"
        constraints.append(constraint)

    return constraints


# build of form:
# (assert (and (> V0 0) (< V0 10)))
# (assert (and (> V1 0) (< V1 10)))
def range_constraints(variables):
    constraints = []
    # TODO: build
    return constraints


"""
from pdf: ...
Next the constraints for each number has to be unique on the row and unique in a column.
There are 18 of these lines

not sure if 18 is hardcoded or not, prolly not
"""


def build_unique_constraints(variables):
    constraints = []
    # TODO : build
    return constraints


def build_constraints(rules, n=7):
    variables = [f"V{num}" for num in range((n * n))]
    constraints = []
    constraints.extend(range_constraints(variables))
    constraints.extend(build_unique_constraints(variables))
    constraints.extend(region_constraints(rules))
    return constraints


if __name__ == "__main__":

    ex = """r1.16+,r2.3+,r2,r3.2-,r3,r4.4-,r4
    r1,r1,r5.10+,r6.3+,r6,r7.7+,r7
    r8.5+,r9.12+,r5,r10.13+,r11.6-,r12.4-,r12
    r8,r9,r9,r10,r11,r13.9+,r13
    r14.4+,r14,r15.11+,r15,r16.4,r17.13+,r18.3+
    r19.11+,r20.6-,r21.12+,r22.5+,r22,r17,r18
    r19,r20,r21,r21,r23.3-,r23,r24.6"""

    parsed = parse_rules(ex)
    constraints = build_constraints(parsed)
    for const in constraints:
        print(const)
