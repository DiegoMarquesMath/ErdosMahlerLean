"""Materialize pinned packages from local Git objects; do not alter the lockfile.

Copy pre-existing dependency build artifacts only after checking every tracked
source blob in the cache tree against the pinned Git tree. Project oleans are
never copied. This does not independently kernel-check dependency oleans.
"""
import hashlib
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPOS = pathlib.Path('/Users/diegomarques/Developer/DiophantineRigidity/.lake/packages')
CACHE = pathlib.Path('/private/tmp/em-deps')

def run(args):
    return subprocess.run(args, check=True, capture_output=True).stdout

records = []
for p in json.loads((ROOT / 'lake-manifest.json').read_text())['packages']:
    name, rev = p['name'], p['rev']
    repo, cached, dest = REPOS / name, CACHE / name, ROOT / '.lake/packages' / name
    tree = run(['git', '-C', str(repo), 'ls-tree', '-rz', rev]).split(b'\0')
    mismatches = []
    count = 0
    for entry in tree:
        if not entry:
            continue
        meta, path = entry.split(b'\t', 1)
        mode, kind, oid = meta.split()
        file = cached / path.decode()
        if kind != b'blob':
            mismatches.append([path.decode(), 'not a blob'])
            continue
        try:
            data = file.readlink().as_posix().encode() if mode == b'120000' else file.read_bytes()
        except OSError as e:
            mismatches.append([path.decode(), str(e)])
            continue
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual != oid.decode():
            mismatches.append([path.decode(), actual, oid.decode()])
        count += 1
    record = dict(name=name, revision=rev, tree=run(['git','-C',str(repo),'rev-parse',rev+'^{tree}']).decode().strip(), checked_blobs=count, mismatches=mismatches)
    records.append(record)
    print(json.dumps(record), flush=True)
    critical = [m for m in mismatches if m[0].endswith('.lean') or m[0] in ('lakefile.toml', 'lean-toolchain', 'lake-manifest.json')]
    if critical:
        raise SystemExit('Cache Lean/build source does not match pinned revision')
    if dest.exists() and run(['git','-C',str(dest),'rev-parse','HEAD']).decode().strip() == rev:
        continue
    if dest.exists():
        dest.rename(dest.with_name(name + '-initial-fetch'))
    run(['git', 'clone', '--shared', '--no-checkout', str(repo), str(dest)])
    run(['git', '-C', str(dest), 'checkout', '--detach', rev])
    run(['git', '-C', str(dest), 'remote', 'set-url', 'origin', p['url']])
    if (cached / '.lake/build').is_dir():
        (dest / '.lake').mkdir(exist_ok=True)
        run(['cp', '-cR', str(cached / '.lake/build'), str(dest / '.lake/build')])
(ROOT / 'audit-evidence/dependency-provenance.json').write_text(json.dumps(records, indent=2)+'\n')
