### Main task:

# How to run:
first type the command (replace input file with according text file path):
```
python3 kenken2smt.py < path-to-your-input-file.txt > result.smt
```
then run mathsat on the result.smt output:
```
mathsat < result.smt > result.txt
```
and finally run:
```
python3 smt2kenken.py < result.txt
```

### Extended Task:

We have provided an additional file `pretty.py` to perform this task. It expects a file path
to be passed to a json file that is the output of running the fetch.sh command that was provided to us
in the project description. I have not provided the fetch file, but an example json file has been included in this submission. To run, enter: `python3 pretty.py` which will generate an html file (as well as terminal output). 
Viewing this html file in the browser will display an html table similar to this:

![Alt text](./pretty_output.png "Try clicking show solution!")

NOTE: by default it will display the kenken puzzle for the `22171.json` file we provided. To make the pretty file read your own generated file, you can run `python3 pretty.py path_to_your_json_file_here.json`, for example running: `python3 pretty.py 22171.json` works as well. 