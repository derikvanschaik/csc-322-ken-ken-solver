import json
import sys


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
    html_start = """
<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Document</title>
  </head>
  <body>"""

    html_end = """
    <button id="show-solution">Show solution</button>
  </body>
  <style>
    button {
      font-size: 25px;
      padding: 15px;
    }
    table {
      border-collapse: collapse; /* Ensures that borders do not double up */
    }

    td {
      border: 1px solid grey; /* Small grey border around each cell */
      padding: 10px; /* Adjust padding as needed */
      text-align: center; /* Center content within the cell */
      position: relative;
      height: 60px;
      width: 44px;
      font-size: 19px;
    }
    .target {
      position: absolute;
      top: 0px;
      left: 0px;
      font-size: 24px;
    }

    .border-right {
      border-right: 3px solid black;
    }

    .border-bottom {
      border-bottom: 3px solid black;
    }
    .solution-hide {
      visibility: hidden;
    }
    .solution-show {
      visibility: visible;
    }
  </style>

  <script defer>
    document.addEventListener("DOMContentLoaded", (event) => {
      document.getElementById("show-solution").addEventListener("click", () => {
        document.querySelectorAll(".solution-hide").forEach((el) => {
          el.classList.remove("solution-hide");
          el.classList.add("solution-show");
        });
      });
    });
  </script>
</html>
"""
    html_str = "<table>"
    for i in range(size):
        html_str += "<tr>"
        for j in range(size):
            # Determine borders
            border_classes = []
            if V[i][j] == "1":
                border_classes.append("border-right")
            if H[j][i] == "1":
                border_classes.append("border-bottom")

            content = ""
            if S[i][j] != "0" and T[i][j] != "0":
                content = f"<span class='target'>{T[i][j]}{S[i][j]}</span><span class='solution-hide'>{A[i][j]}</span>"
            else:
                content = f"<span class='solution-hide'>{A[i][j]}</span>"

            classes = " ".join(border_classes)
            html_str += f'<td class="{classes}">{content}</td>'
        html_str += "</tr>"
    html_str += "</table>"
    return html_start + html_str + html_end


# def generate_terminal(A, T, S, V, H):
#     size = len(A)
#     for i in range(size):
#         for j in range(size):
#             print(A[i][j], end="|" if V[i][j] == "1" else " ")
#             # if V[i][j] == "1":
#             #     border_classes.append("border-right")
#         print()
#         for j in range(size):
#             if H[j][i] == "1":
#                 print("_", end="")
#             else:
#                 print(" ", end="")


#         print()


def generate_terminal_ascii(A, V, H):
    size = len(A)
    for i in range(size):
        # Draw the top border for the current row
        row_cells = []

        for j in range(size):
            cell = {}
            # cell['val']= f"{A[i][j]:^9}" # This formats the value to be centered within 5 spaces -- makes uniform across rows
            val = A[i][j]

            cell["right_border"] = V[i][j] == "1"
            cell["bottom_border"] = H[j][i] == "1"
            is_target_cell = S[i][j] != "0" and T[i][j] != "0"
            if is_target_cell:
                val = f"({S[i][j]}{T[i][j]})" + val

            row_cells.append(cell)
            vertical_bar = "|"
            cell["val"] = f"{val:^7}"

            print(cell["val"], end=vertical_bar if cell["right_border"] else " ")
        print()
        for cell in row_cells:
            char = " "
            if cell["bottom_border"]:
                char = "_"
                # plus one accounts for space or vertical bar added after cel val
            print(char * (len(cell["val"]) + 1), end="")
        print()


# Open the file and load the JSON data
data = None

filename = "./22171.json"

if len(sys.argv) > 1:
    filename = sys.argv[1]

with open(filename, "r") as file:
    data = json.load(file)

if data is not None:
    size = int(data["size"])
    A, T, S, V, H = parse_kenken_data(data)

    pretty_output = generate_html(A, T, S, V, H)

    file_path = "pretty_printer.html"

    with open(file_path, "w") as html_file:
        html_file.write(pretty_output)

    print(f"HTML file '{file_path}' has been created.")
    print(
        "Please open the html file in your browser for a very nice pretty printed puzzle "
    )
    print("here is a terminal equivalent:", end="\n\n")
    generate_terminal_ascii(A, V, H)
