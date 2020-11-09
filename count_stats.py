#!/usr/bin/env python3
import sys
import re
import json
import subprocess
import shutil

if len(sys.argv) < 2:
    print("Usage: {} <files.c> ...".format(sys.argv[0]))
    exit(1)

FILES=sys.argv[1:]

for f in FILES:
    tmpname = f + ".statstmp"
    shutil.copyfile(f, tmpname)
    with open(f, "a") as fd:
        fd.write("//@rc::import enable_debug from refinedc.typing.automation\n")

    o = subprocess.check_output(["./build.sh", f], stderr=subprocess.STDOUT).split(b"\n")
    results = []
    total = { "evars": 0, "sideconds": 0, "unsolvedsideconds": 0, "extensible": 0 }
    current = None
    def finish():
        if current is None:
            return
        results.append(current)
    for line in o:
        if b"coqc " in line:
            finish()
            current = { "name" : line.decode("utf8"),
                        "evars": 0, "sideconds": 0, "unsolvedsideconds": 0, "extensible": 0 }
        if line == b"EVAR":
            current["evars"] += 1
            total["evars"] += 1
        if line == b"SIDECOND":
            current["sideconds"] += 1
            total["sideconds"] += 1
        if line == b"UNSOLVEDSIDECOND":
            current["unsolvedsideconds"] += 1
            total["unsolvedsideconds"] += 1
        if line == b"EXTENSIBLE":
            current["extensible"] += 1
            total["extensible"] += 1
    finish()
    print((json.dumps(results, indent=2)))
    print((json.dumps(total, indent=2)))
    shutil.move(tmpname, f)
