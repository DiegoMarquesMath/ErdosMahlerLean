"""Write or verify SHA-256 for the reports and every retained audit artifact.

The manifest excludes itself to avoid a self-reference. Invoke with --check
to verify both hashes and inventory. Git object IDs are checked at publication
separately; SHA-256 is the independent content fingerprint here.
"""
import argparse
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = root / 'audit-evidence/artifact-hashes.json'
reports = ['AUDIT_REPORT.md', 'EXTERNAL_THEOREM_RECONCILIATION.md', 'VERIFIED_STATEMENT.md']
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
files = [root / name for name in reports]
files += sorted(p for p in (root / 'audit-evidence').rglob('*')
                if p.is_file() and p != manifest and '__pycache__' not in p.parts)
actual = [{'path': str(p.relative_to(root)), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
          for p in files]
if args.check:
    assert json.loads(manifest.read_text()) == actual, 'Hash or inventory mismatch'
    print(f'PASS: {len(actual)} artifact SHA-256 hashes and complete inventory.')
else:
    manifest.write_text(json.dumps(actual, indent=2) + '\n')
    print(f'Wrote {len(actual)} artifact SHA-256 hashes; manifest excludes itself.')
for item in actual[:3]:
    print(item['sha256'], item['path'])
print(hashlib.sha256(manifest.read_bytes()).hexdigest(), str(manifest.relative_to(root)))
