#!/usr/bin/env python3
"""List the local modules in the import closure of a Lean module, in dependency order.

usage: closure.py [ROOT_MODULE]      (default RHTripleIntegration.SimpleProportion)
Writes checks/clean-rebuild/order.json next to the repository root.
"""
import json, os, re, sys
from collections import Counter
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.join(REPO, 'lean')
IMP = re.compile(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)

def path(mod):
    p = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
    return p if os.path.exists(p) else None

order, seen, external = [], set(), set()
def visit(mod):
    if mod in seen:
        return
    p = path(mod)
    if p is None:
        external.add(mod); return
    seen.add(mod)
    deps = IMP.findall(open(p, encoding='utf-8').read())
    for d in deps:
        visit(d)
    order.append({'module': mod, 'file': os.path.relpath(p, REPO),
                  'local_imports': [d for d in deps if path(d)]})

visit(sys.argv[1] if len(sys.argv) > 1 else 'RHTripleIntegration.SimpleProportion')
out = os.path.join(REPO, 'checks', 'clean-rebuild')
os.makedirs(out, exist_ok=True)
json.dump({'modules': order, 'external': sorted(external)}, open(os.path.join(out, 'order.json'), 'w'), indent=1)
print(len(order), 'local modules', dict(Counter(m['module'].split('.')[0] for m in order)))
print('external:', dict(Counter(e.split('.')[0] for e in external)))
