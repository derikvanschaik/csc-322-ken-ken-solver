import json


def parse_kenken_data(json_data):
    # Extract the 'data' field from the JSON object
    data_str = json_data["data"]
    size = int(json_data["size"])

    # TODO: put into a function to clean up

    A = []
    for i in range(size):
        row = []
        for j in range(size):
            row.append(0)
        A.append(row)

    cur_data_str = data_str
    for i in range(0, size + 1):
        index = cur_data_str.find("\r\n")
        line = cur_data_str[0:index]
        if line != "A":
            # TODO: whitespace can be different from this format
            values = [val for val in line.split(" ") if val]
            for j, val in enumerate(values):
                A[i - 1][j] = val

        cur_data_str = cur_data_str[index + len("\r\n") :]

    T = []
    for i in range(size):
        row = []
        for j in range(size):
            row.append(0)
        T.append(row)

    for i in range(0, size + 1):
        index = cur_data_str.find("\r\n")
        line = cur_data_str[0:index]
        if line != "T":
            # TODO: whitespace can be different from this format
            values = [val for val in line.split(" ") if val]
            for j, val in enumerate(values):
                T[i - 1][j] = val

        cur_data_str = cur_data_str[index + len("\r\n") :]

    S = []
    for i in range(size):
        row = []
        for j in range(size):
            row.append(0)
        S.append(row)

    for i in range(0, size + 1):
        index = cur_data_str.find("\r\n")
        line = cur_data_str[0:index]
        if line != "S":
            # TODO: whitespace can be different from this format
            values = [val for val in line.split(" ") if val]
            for j, val in enumerate(values):
                S[i - 1][j] = val

        cur_data_str = cur_data_str[index + len("\r\n") :]

    V = []
    for i in range(size):
        row = []
        for j in range(size):
            row.append(0)
        V.append(row)

    for i in range(0, size + 1):
        index = cur_data_str.find("\r\n")
        line = cur_data_str[0:index]
        if line != "V":
            # TODO: whitespace can be different from this format
            values = [val for val in line.split(" ") if val]
            for j, val in enumerate(values):
                V[i - 1][j] = val

        cur_data_str = cur_data_str[index + len("\r\n") :]

    H = []
    for i in range(size):
        row = []
        for j in range(size):
            row.append(0)
        H.append(row)

    for i in range(0, size + 1):
        index = cur_data_str.find("\r\n")
        line = cur_data_str[0:index]
        if line != "H":
            # TODO: whitespace can be different from this format
            values = [val for val in line.split(" ") if val]
            for j, val in enumerate(values):
                H[i - 1][j] = val

        cur_data_str = cur_data_str[index + len("\r\n") :]

    return A, T, S, V, H


def generate_html(A, T, S, V, H):
    size = len(A)
    html_str = "<table>"
    for i in range(size):
        html_str += "<tr>"
        for j in range(size):
            # Determine borders
            border_classes = []

            # Add target and symbol if present
            content = f"{T[i][j]}{S[i][j]}" if S[i][j] != "0" else ""
            classes = " ".join(border_classes)
            html_str += f'<td class="{classes}">{content}</td>'
        html_str += "</tr>"
    html_str += "</table>"
    return html_str


# Open the file and load the JSON data
data = None

with open("./output.json", "r") as file:
    data = json.load(file)

if data is not None:
    size = int(data["size"])
    A, T, S, V, H = parse_kenken_data(data)

    # for i in range(size):
    #     for j in range(size):
    #         symbol = S[i][j]
    #         target = T[i][j]
    #         if symbol != "0" and target != "0":
    #             print(symbol + "" + target, end=" ")
    #         else:
    #             print(" " * 2, end=" ")
    #     print()
    for i in range(size):
        for j in range(size):
            symbol = S[i][j]
            target = T[i][j]
            if symbol != "0" and target != "0":
                # Assuming 'target' is an integer. Adjust formatting if it's not.
                cell_content = f"{symbol}{target}"  # Concatenating symbol and target
            else:
                cell_content = "__"

            # Right-align the content in a field of width 5. Adjust the width as needed.
            print(f"{cell_content:>5}", end=" ")
        print()

    # print("---------------------------")

    # for i in range(size):
    #     for j in range(size):
    #         print(S[i][j], end=" ")
    #     print()
