#!/usr/bin/env python3
"""Compile the closure listed by closure.py into an empty directory, against a built AF checkout.

usage: build.py AF_CHECKOUT OUTPUT_DIR [WORKERS]
AF_CHECKOUT : unmodified checkout of the AF library at the pinned commit, already built
              (`lake build Zeta23`), so that `lake env lean` sees Zeta23 and Mathlib.
OUTPUT_DIR  : must not exist or must be empty; receives the .olean files and logs.
Writes checks/clean-rebuild/build.json.
"""
import hashlib, json, os, subprocess, sys, threading, time
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.join(REPO, 'lean')
AF, OUT = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
W = int(sys.argv[3]) if len(sys.argv) > 3 else 3
OBJ, LOG = os.path.join(OUT, 'obj'), os.path.join(OUT, 'logs')
if os.path.exists(OUT) and os.listdir(OUT):
    sys.exit('OUTPUT_DIR is not empty')
os.makedirs(OBJ); os.makedirs(LOG)
order = json.load(open(os.path.join(REPO, 'checks', 'clean-rebuild', 'order.json')))['modules']
deps = {m['module']: set(m['local_imports']) for m in order}
files = {m['module']: os.path.join(REPO, m['file']) for m in order}

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

def run(mod):
    out = os.path.join(OBJ, mod.replace('.', '/') + '.olean')
    os.makedirs(os.path.dirname(out), exist_ok=True)
    cmd = f'LEAN_PATH="{OBJ}:$LEAN_PATH" lean -j1 --root="{ROOT}" -o "{out}" "{files[mod]}"'
    t = time.time()
    p = subprocess.run(['lake', 'env', 'sh', '-c', cmd], cwd=AF, capture_output=True, text=True)
    txt = p.stdout + p.stderr
    open(os.path.join(LOG, mod + '.log'), 'w').write(txt)
    return {'module': mod, 'rc': p.returncode, 'seconds': round(time.time() - t, 1),
            'errors': txt.count('error'), 'warnings': txt.count('warning'),
            'sorryAx': txt.count('sorryAx'), 'src_sha256': sha(files[mod]),
            'olean_sha256': sha(out) if os.path.exists(out) else None}

t0 = time.time(); pending = [m['module'] for m in order]; running = set(); done = set(); res = {}
lock = threading.Lock()
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
ths = [threading.Thread(target=worker) for _ in range(W)]
[t.start() for t in ths]; [t.join() for t in ths]
R = sorted(res.values(), key=lambda x: x['module'])
comb = lambda k: hashlib.sha256('\n'.join(f"{x['module']} {x[k]}" for x in R).encode()).hexdigest()
def git(*a, cwd):
    return subprocess.run(['git', *a], cwd=cwd, capture_output=True, text=True).stdout.strip()
rec = {'af_commit': git('rev-parse', 'HEAD', cwd=AF), 'af_dirty_files': len(git('status', '--short', cwd=AF).splitlines()),
       'toolchain': open(os.path.join(AF, 'lean-toolchain')).read().strip(), 'workers': W,
       'wall_seconds': round(time.time() - t0, 1), 'sum_module_seconds': round(sum(x['seconds'] for x in R), 1),
       'modules': len(order), 'succeeded': len(done), 'not_built': pending,
       'errors': sum(x['errors'] for x in R), 'sorryAx': sum(x['sorryAx'] for x in R),
       'warnings': sum(x['warnings'] for x in R), 'combined_source_sha256': comb('src_sha256'),
       'combined_olean_sha256': comb('olean_sha256'), 'results': R}
json.dump(rec, open(os.path.join(REPO, 'checks', 'clean-rebuild', 'build.json'), 'w'), indent=1)
print({k: rec[k] for k in ('modules', 'succeeded', 'errors', 'sorryAx', 'warnings', 'wall_seconds')})
print('source', rec['combined_source_sha256']); print('olean ', rec['combined_olean_sha256'])
sys.exit(0 if len(done) == len(order) else 1)
