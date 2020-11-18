#!/usr/bin/env python3
import sys
import re
import json
import subprocess
import shutil
import os
import random

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
    "tactics": "pure",
    "lemmas": "pure",
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
        if k != "import" and k != "inlined" and k != "require":
            total += v
    types["LoC"] = loc - total
    types["annot"] = types.get("annot", 0) + types.get("rule", 0)
    types.pop('rule', None)
    print(json.dumps(types, indent=2))
    return types

def parse_file(f):
    per_file = {}
    for match in annotation_re.finditer(f):
        num_lines = len(match.group(3).strip().split('\n'))
        name = match.group(2)
        if name == "exists" and match.group(1) != "":
            name = "loopexists"

        per_file[name] = per_file.get(name, 0)
        per_file[name] += num_lines

    for match in annotation_block_re.finditer(f):
        num_lines = 1

        per_file[match.group(1)] = per_file.get(match.group(1), 0)
        per_file[match.group(1)] += num_lines

    for match in inline_re.finditer(f):
        num_lines = 1

        per_file[match.group(1)] = per_file.get(match.group(1), 0)
        per_file[match.group(1)] += num_lines

    for match in comment_re.finditer(f):
        num_lines = 1

        per_file[match.group(1)] = per_file.get(match.group(1), 0)
        per_file[match.group(1)] += num_lines

    return per_file

def compute_annots(FILES):
    total = {}
    o = subprocess.check_output(["tokei", "--output=json", "--files"] + FILES)
    print(o)
    inner = json.loads(o)
    if "CHeader" not in inner:
        inner["CHeader"] = { "code": 0, "reports": []}
    lines_total = inner["C"]["code"] + inner["CHeader"]["code"]
    lines_per_file = {}
    for s in inner["C"]["reports"] + inner["CHeader"]["reports"]:
        lines_per_file[s["name"]] = s["stats"]["code"]

    # count annotations
    for f in FILES:
        if f.endswith(".v"):
            continue
        print(f)
        with open(f, 'r') as content_file:
            per_file = parse_file(content_file.read())

        print_stats(per_file, lines_per_file[f])

        for k,v in per_file.items():
            total[k] = total.get(k, 0)
            total[k] += v


    total = print_stats(total, lines_total)
    if "Coq" in inner:
        total["pure"] = total.get("pure", 0) + inner["Coq"]["code"]
    # count lemmas and quantifier instantiations
    total["exists"] = 0
    total["sideconds"] = 0
    total["unsolvedsideconds"] = 0
    total["rules"] = 0
    results = []

    for f in FILES:
        if not f.endswith(".c"):
            continue
        proofsdir = os.path.join(os.path.dirname(f), "proofs", os.path.basename(f)[:-2])
        print(proofsdir)
        tmpname = f + ".statstmp"
        shutil.copyfile(f, tmpname)
        with open(f, "a") as fd:
            fd.write("//@rc::import enable_debug from refinedc.typing.automation\n")
            fd.write(f"//@rc::inlined Definition marker_{random.randint(0, 1000)} := tt.\n")

        subprocess.check_output(["dune", "exec", "--", "refinedc", "check", "--no-build", f])

        o = subprocess.check_output(["dune", "build", "--display", "short"],
                                    cwd=proofsdir, stderr=subprocess.STDOUT).split(b"\n")
        current = None

        for line in o:
            if b"coqc " in line:
                if current is not None:
                    results.append(current)
                    current = None

                name = line.decode("utf8")
                if proofsdir in name:
                    print(name)
                    current = { "name" : name,
                                "exists": 0, "sideconds": 0, "unsolvedsideconds": 0, "rules": 0 }
            if current is None:
                continue
            if line == b"EVAR":
                current["exists"] += 1
                total["exists"] += 1
            if line == b"SIDECOND":
                current["sideconds"] += 1
                total["sideconds"] += 1
            if line == b"UNSOLVEDSIDECOND":
                current["unsolvedsideconds"] += 1
                total["unsolvedsideconds"] += 1
            if line == b"EXTENSIBLE":
                current["rules"] += 1
                total["rules"] += 1
        if current is not None:
            results.append(current)
            current = None

        # print((json.dumps(results, indent=2)))
        # print((json.dumps(total, indent=2)))
        shutil.move(tmpname, f)

    print("total:")
    # print_stats(total, lines_total)
    print(json.dumps(total, indent=2))
    return total

stats = [ {
    "name": "#1",
    "progs": [ {
        "name": "Singly linked list",
        "abs": "wand, alloc",
        "stats": compute_annots(["tutorial/t03_list.c"])
    }, {
        "name": "Queue",
        "abs": "list segments, alloc",
        "stats": compute_annots(["examples/queue.c"])
    }, {
        "name": "Binary search",
        "abs": "arrays, func. ptr.",
        "stats": compute_annots(["examples/binary_search.c",
                                 "examples/proofs/binary_search/binary_search_extra.v"])
    } ]
}, {
    "name": "#2",
    "progs": [ {
        "name": "Thread-safe allocator",
        "abs": "wand, padded, spinlock",
        "stats": compute_annots(["tutorial/t04_alloc.c", "tutorial/alloc.h", "tutorial/alloc_internal.h"])
    }, {
        "name": "Page allocator",
        "abs": "padded",
        "stats": compute_annots(["examples/malloc1.c"])
    } ]
}, {
    "name": "#3",
    "progs": [ {
        "name": "Binary search tree (layered)",
        "abs": "wand, alloc",
        "stats": compute_annots(["tutorial/t08_tree.c", "tutorial/proofs/t08_tree/t08_tree_extra.v"])
    }, {
        "name": "Binary search tree (direct)",
        "abs": "wand, alloc",
        "stats": compute_annots(["tutorial/t11_tree_set.c"])
    } ]
}, {
    "name": "#4",
    "progs": [ {
        "name": "Linear probing hashmap",
        "abs": "unions, arrays, alloc",
        "stats": compute_annots(["examples/mutable_map.c", "examples/proofs/mutable_map/mutable_map_extra.v"])
    } ]
}, {
    "name": "#5",
    "progs": [ {
        "name": "Hafnium's mpool allocator",
        "abs": "wand, padded, spinlock",
        "stats": compute_annots(["examples/mpool.c"])
    } ]
}, {
    "name": "#6",
    "progs": [ {
        "name": "Spinlock",
        "abs": "atomic Boolean",
        "stats": compute_annots(["examples/spinlock.c", "examples/include/spinlock.h"])
    }, {
        "name": "One-time barrier",
        "abs": "atomic Boolean",
        "stats": compute_annots(["examples/latch.c", "examples/include/latch.h"])
    } ]
} ]

# Add 6 to spinlock for the 6 non-trivial lines in examples/proofs/spinlock/spinlock_proof.v
#   Typeclasses Transparent spinlock spinlocked_ex spinlock_token spinlocked_ex_token.
#   iApply fupd_typed_stmt.
#   iMod (own_alloc (● GSet ∅)) as (γ) "Hown"; [ by apply auth_auth_valid |].
#   iAssert (spinlock_token γ []) with "[Hown]" as "?"; [ by iExists _; iFrame |].
#   iModIntro.
#   liInst Hevar γ.
stats[5]["progs"][0]["stats"]["annot"] += 6

print(json.dumps(stats, indent=2))
with open('data.json', 'w') as f:
    json.dump(stats, f, indent=2)
