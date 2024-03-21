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

            # print(region, value, operation)

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
        ## TODO: some how verify that r24.6 would be of form
        # (assert (= 6 V24))
        variables = parse_rules[region]["variables"]
        operator = parse_rules[region]["operator"]
        value = parse_rules[region]["value"]

        const = ""
        variable_constraints = ""

        if operator in ("*", "+"):
            variable_constraints = f'({operator} {" ".join(variables)})'
            const = f"(= {value} {variable_constraints})"

        elif operator in ("/", "-"):
            variable_perm = list(permutations(variables))
            for perm in variable_perm:
                variable_constraints += f'(= {value} ({operator} {" ".join(perm)}))'

            variable_constraints = f"(or {variable_constraints})"
            const = variable_constraints

        # single assignment like r24.6
        else:
            const = f"(= {value} {variables[0]})"

        constraint = f"(assert {const}) ; Region {region}"
        constraints.append(constraint)

    return constraints


# build of form:
# (assert (and (> V0 0) (< V0 10)))
# (assert (and (> V1 0) (< V1 10)))
def range_constraints(variables):
    constraints = []
    for var in variables:
        const = f"(assert (and (> {var} 0) (< {var} 8)))"
        constraints.append(const)
    return constraints


"""
from pdf: ...
Next the constraints for each number has to be unique on the row and unique in a column.

"""


def build_unique_constraints(variables, n=7):
    # construct n by n matrix of variables
    matrix = []
    for _ in range(n):
        matrix.append([0 for _ in range(n)])

    for i, el in enumerate(variables):
        row = i // n
        col = i % n
        matrix[row][col] = el

    constraints = []
    for i in range(n):
        row = matrix[i]
        col = [row for row in zip(*matrix)][i]
        # TODO: is line part correct?
        row_const = f'(assert (distinct {" ".join(row)} )) ; line {i}1'
        col_const = f'(assert (distinct {" ".join(col)} )) ; line {i}{n}'

        constraints.append(row_const)
        constraints.append(col_const)

    return constraints


def declare_variables(n=7):
    variables = [f"V{num}" for num in range((n * n))]
    res = []
    for var in variables:
        res.append(f"(declare-const {var} Int)")
    return res


def build_constraints(rules, n=7):
    variables = [f"V{num}" for num in range((n * n))]
    constraints = []
    constraints.extend(range_constraints(variables))
    constraints.extend(build_unique_constraints(variables, n=n))
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

    ex2 = """r1.14+,r2.1,r3.13+,r3,r4.5+,r4,r5.6+
r1,r1,r6.4+,r7.11+,r8.9+,r9.7,r5
r10.6+,r10,r6,r7,r8,r11.3+,r12.12+
r13.9+,r13,r14.11+,r15.5+,r15,r11,r12
r16.10+,r17.13+,r14,r18.3+,r19.12+,r19,r19
r16,r17,r20.7+,r18,r21.9+,r21,r22.3
r23.3+,r23,r20,r24.10+,r24,r25.10+,r25"""

    ex3 = """r1.16+,r2.1-,r2,r3.5-,r3,r4.3/,r4,r5.13+,r5
r1,r6.4/,r6,r7.3-,r8.45*,r8,r9.22+,r9,r5
r1,r10.3+,r10,r7,r11.2-,r11,r9,r12.2-,r12
r13.3/,r14.1-,r15.8-,r16.120*,r16,r16,r17.20*,r18.2-,r19.2
r13,r14,r15,r20.2-,r20,r17,r17,r18,r21.17+
r22.9+,r23.63*,r24.1-,r25.5-,r24,r26.1-,r27.48*,r21,r21
r22,r23,r24,r28.5-,r28,r26,r27,r29.4/,r29
r30.3,r31.432*,r32.20+,r32,r33.18+,r34.3+,r34,r35.13+,r36.2-
r31,r31,r32,r32,r33,r33,r33,r34,r3"""

    ex4 = """r1.10+,r2.3+,r2,r3.8+,r3,r4.18+,r4
r1,r5.11+,r5,r6.3+,r6,r7.3,r4
r8.12+,r9.5+,r10.12+,r10,r11.4,r12.9+,r12
r8,r9,r10,r13.6+,r14.11+,r14,r15.6+
r16.10+,r16,r17.9+,r13,r18.3+,r18,r15
r19.7+,r19,r17,r20.13+,r20,r21.6+,r22.8+
r23.7+,r23,r24.5,r25.7+,r25,r21,r22"""

    n = 7
    parsed = parse_rules(ex4, n=n)
    # print(parsed)
    # print(parsed)
    declared = declare_variables(n=n)
    constraints = build_constraints(parsed, n=n)

    ## smt format
    smt_format = f"(set-logic UFNIA)\n(set-option :produce-models true)\n(set-option :produce-assignments true)\n"
    for d in declared:
        smt_format += d + "\n"
    for c in constraints:
        smt_format += c + "\n"

    smt_format += "(check-sat)\n"

    variables = [f"V{num}" for num in range((n * n))]

    smt_format += f"(get-value ({' '.join(variables)}))\n"
    smt_format += "(exit)\n"

    print(smt_format)
