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
      color: black;
    }

    .border-right {
      border-right: 3px solid black;
    }

    .border-bottom {
      border-bottom: 3px solid black;
    }
    td.solution-hide {
      color: white;
    }
    td.solution-show {
      color: black;
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
                content = f"{T[i][j]}{S[i][j]}"
            else:
                content = f"{A[i][j]}"
                border_classes.append("solution-hide")

            classes = " ".join(border_classes)
            html_str += f'<td class="{classes}">{content}</td>'
        html_str += "</tr>"
    html_str += "</table>"
    return html_start + html_str + html_end


# Open the file and load the JSON data
data = None

with open("./22171.json", "r") as file:
    data = json.load(file)

if data is not None:
    size = int(data["size"])
    A, T, S, V, H = parse_kenken_data(data)

    pretty_output = generate_html(A, T, S, V, H)

    # Specify the path to the HTML file you want to create
    file_path = "pretty_printer.html"

    # Open the file in write mode ('w') and write the HTML content to it
    with open(file_path, "w") as html_file:
        html_file.write(pretty_output)

    print(f"HTML file '{file_path}' has been created.")
