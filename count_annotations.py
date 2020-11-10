#!/usr/bin/env python3
import sys
import re
import json
import subprocess

## TODO: distinguish between specification annotations and proof
## annotations (by checking if there is whitespace at the beginning of
## the line?)
## TODO: also count Coq code

annotation_re = re.compile(r"( ?)\[\[rc::([A-Za-z_]+)\s*\((.*?)\)\s*\]\]", re.DOTALL)
annotation_block_re = re.compile(r"\[\[rc::([A-Za-z_]+)\s*\]\]")
inline_re = re.compile("rc_([A-Za-z_]*)")
comment_re = re.compile("//\s*@\s*rc::([A-Za-z_]*)")

ANNOT_TYPE = {
    "manual_proof": "annot",
    "context": "annot",
    "annot_args": "spec",
    "import": "annot",
    "require": "annot",
    "inlined": "annot",
    "tagged_union": "annot",
    "union_tag": "annot",
    "unfold_int": "annot",
    "refined_by": "annot",
    "ptr_type": "annot",
    "field": "annot",
    "size": "annot",
    "global": "annot",
    "constraints": "annot",
    "parameters": "spec",
    "args": "spec",
    "requires": "spec",
    "ensures": "spec",
    "exists": "spec",
    "returns": "spec",
    "loopexists": "annot",
    "inv_vars": "annot",
    "block": "annot",
    "tactics": "side",
    "lemmas": "side",
    "unfold": "rule",
    "unfold_once": "rule",
    "unlock": "rule",
    "share": "rule",
    "to_uninit": "rule",
    "uninit_strengthen_align": "rule",
}

def print_stats(annots, loc):
    # print(json.dumps(annots, indent=2))
    types = {}
    total = 0
    for k,v in annots.items():
        if k not in ANNOT_TYPE:
            print('unknown annotation: ' + k)
            exit(1)
        t = ANNOT_TYPE[k]
        types[t] = types.get(t, 0)
        types[t] += v
        if t != "import" and t != "inlined" and t != "require":
            total += v
    types["LoC"] = loc - total
    print(json.dumps(types, indent=2))

    # annots_sum_with_spec = 0
    # for k,v in annots.items():
    #     annots_sum_with_spec += v[0]
    # annots_sum_without_spec = 0
    # for k,v in annots.items():
    #     annots_sum_without_spec += v[1]
    # loc -= annots_sum_with_spec + annots_sum_without_spec
    # print("with spec: {}/{} = {:.2f}".format(annots_sum_with_spec, loc, annots_sum_with_spec / loc))
    # print("without spec: {}/{} = {:.2f}".format(annots_sum_without_spec, loc, annots_sum_without_spec / loc))

total = {}
def parse_file(f):
    per_file = {}
    for match in annotation_re.finditer(f):
        num_lines = len(match.group(3).strip().split('\n'))
        name = match.group(2)
        if name == "exists" and match.group(1) != "":
            name = "loopexists"

        # idx = 0 if match.group(1) == "" else 1
        # if "::" in name:
        # if match.group(1) == "parameters":
            # print(match.group(1), name)
        per_file[name] = per_file.get(name, 0)
        per_file[name] += num_lines

    for match in annotation_block_re.finditer(f):
        num_lines = 1
        # if "::" in match.group(2):
        # if match.group(1) == "parameters":
        # print(match.group(1))

        per_file[match.group(1)] = per_file.get(match.group(1), 0)
        per_file[match.group(1)] += num_lines

    for match in inline_re.finditer(f):
        num_lines = 1
        # if "::" in match.group(2):
        # if match.group(1) == "parameters":
        # print(match.group(1))

        per_file[match.group(1)] = per_file.get(match.group(1), 0)
        per_file[match.group(1)] += num_lines

    for match in comment_re.finditer(f):
        num_lines = 1
        # if "::" in match.group(2):
        # if match.group(1) == "parameters":
        # print(match.group(1))

        per_file[match.group(1)] = per_file.get(match.group(1), 0)
        per_file[match.group(1)] += num_lines

    return per_file


if len(sys.argv) < 2:
    print("Usage: {} <files.c> ...".format(sys.argv[0]))
    exit(1)

FILES=sys.argv[1:]

o = subprocess.check_output(["tokei", "--output=json", "--files"] + FILES)
inner = json.loads(o)["inner"]
if "CHeader" not in inner:
    inner["CHeader"] = { "code": 0, "stats": []}
lines_total = inner["C"]["code"] + inner["CHeader"]["code"]
lines_per_file = {}
for s in inner["C"]["stats"] + inner["CHeader"]["stats"]:
    lines_per_file[s["name"]] = s["code"]

for f in FILES:
    print(f)
    with open(f, 'r') as content_file:
        per_file = parse_file(content_file.read())

    print_stats(per_file, lines_per_file[f])

    for k,v in per_file.items():
        total[k] = total.get(k, 0)
        total[k] += v

print("total:")
print_stats(total, lines_total)
# print(json.dumps(total, indent=2))
