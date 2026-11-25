#!/usr/bin/env python3
"""Compile Lean modules with the `lean` binary directly (no Lake), into an empty directory.

usage: build_direct.py --lean LEAN --root SRC_ROOT --out OUT --record RECORD.json
                       [--path DIR]... [--opt name=value]... [--entry Module]... [--workers N]

--lean    path of the `lean` binary of the pinned toolchain
--root    source root; module A.B is SRC_ROOT/A/B.lean
--out     output directory (must be empty or absent); receives obj/ and logs/
--path    directories put on LEAN_PATH before OUT/obj (dependency .olean trees), in order
--opt     passed as -Dname=value (the options of the project's lakefile)
--entry   modules whose import closure inside SRC_ROOT is compiled; default: every .lean file
"""
import argparse, hashlib, json, os, re, subprocess, sys, threading, time
ap = argparse.ArgumentParser()
ap.add_argument('--lean', required=True); ap.add_argument('--root', required=True)
ap.add_argument('--out', required=True); ap.add_argument('--record', required=True)
ap.add_argument('--path', action='append', default=[]); ap.add_argument('--opt', action='append', default=[])
ap.add_argument('--entry', action='append', default=[]); ap.add_argument('--workers', type=int, default=3)
a = ap.parse_args()
ROOT, OUT = os.path.abspath(a.root), os.path.abspath(a.out)
OBJ, LOG = os.path.join(OUT, 'obj'), os.path.join(OUT, 'logs')
if os.path.exists(OUT) and os.listdir(OUT):
    sys.exit('output directory is not empty')
os.makedirs(OBJ); os.makedirs(LOG)
IMP = re.compile(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
def path(mod):
    p = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
    return p if os.path.exists(p) else None
entries = a.entry
if not entries:
    for d, _, fs in os.walk(ROOT):
        for f in fs:
            if f.endswith('.lean'):
                entries.append(os.path.relpath(os.path.join(d, f), ROOT)[:-5].replace('/', '.'))
order, deps, seen = [], {}, set()
def visit(mod):
    if mod in seen or path(mod) is None:
        return
    seen.add(mod)
    ds = [d for d in IMP.findall(open(path(mod), encoding='utf-8').read()) if path(d)]
    for d in ds:
        visit(d)
    deps[mod] = set(ds); order.append(mod)
sys.setrecursionlimit(100000)
for e in sorted(entries):
    visit(e)
env = dict(os.environ); env['LEAN_PATH'] = ':'.join([os.path.abspath(p) for p in a.path] + [OBJ])
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
def run(mod):
    out = os.path.join(OBJ, mod.replace('.', '/') + '.olean')
    os.makedirs(os.path.dirname(out), exist_ok=True)
    cmd = [a.lean, '-j1'] + ['-D' + o for o in a.opt] + ['--root=' + ROOT, '-o', out, path(mod)]
    t = time.time(); p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    txt = p.stdout + p.stderr
    open(os.path.join(LOG, mod + '.log'), 'w').write(txt)
    return {'module': mod, 'rc': p.returncode, 'seconds': round(time.time() - t, 1),
            'errors': txt.count('error'), 'warnings': txt.count('warning'), 'sorryAx': txt.count('sorryAx'),
            'src_sha256': sha(path(mod)), 'olean_sha256': sha(out) if os.path.exists(out) else None}
t0 = time.time(); pending = list(order); running = set(); done = set(); res = {}; lock = threading.Lock()
def worker():
    while True:
        with lock:
            if not pending and not running:
                return
            pick = next((m for m in pending if deps[m] <= done), None)
            if pick is None and not running:
                return
            if pick is not None:
                pending.remove(pick); running.add(pick)
        if pick is None:
            time.sleep(0.5); continue
        r = run(pick)
        with lock:
            res[pick] = r; running.discard(pick)
            if r['rc'] == 0:
                done.add(pick)
ths = [threading.Thread(target=worker) for _ in range(a.workers)]
[t.start() for t in ths]; [t.join() for t in ths]
R = sorted(res.values(), key=lambda x: x['module'])
comb = lambda k: hashlib.sha256('\n'.join(f"{x['module']} {x[k]}" for x in R).encode()).hexdigest()
ver = subprocess.run([a.lean, '--version'], capture_output=True, text=True).stdout.strip()
rec = {'lean': ver, 'options': a.opt, 'lean_path': [os.path.basename(os.path.normpath(p)) for p in a.path],
       'workers': a.workers, 'wall_seconds': round(time.time() - t0, 1),
       'sum_module_seconds': round(sum(x['seconds'] for x in R), 1), 'modules': len(order),
       'succeeded': len(done), 'failed': [x['module'] for x in R if x['rc'] != 0], 'not_built': pending,
       'errors': sum(x['errors'] for x in R), 'sorryAx': sum(x['sorryAx'] for x in R),
       'warnings': sum(x['warnings'] for x in R), 'combined_source_sha256': comb('src_sha256'),
       'combined_olean_sha256': comb('olean_sha256'), 'results': R}
os.makedirs(os.path.dirname(os.path.abspath(a.record)), exist_ok=True)
json.dump(rec, open(a.record, 'w'), indent=1)
print({k: rec[k] for k in ('modules', 'succeeded', 'failed', 'errors', 'sorryAx', 'warnings', 'wall_seconds')})
sys.exit(0 if len(done) == len(order) else 1)
