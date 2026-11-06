"""Compare worktree bytes with the frozen Git tree; record SHA-256 independently."""
import hashlib
import json
import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parents[1]
tag = "prop21-conditional-2026-11-06"
def git(*args):
    return subprocess.check_output(["git", *args], cwd=root)

entries = []
for row in git("ls-tree", "-rz", tag).split(b"\0"):
    if not row:
        continue
    head, name = row.split(b"\t", 1)
    mode, kind, oid = head.decode().split()
    if kind != "blob":
        raise RuntimeError(f"Unexamined tree entry: {row!r}")
    path = root / name.decode()
    data = path.read_bytes()
    frozen = git("cat-file", "blob", oid)
    entries.append({"path": name.decode(), "git_blob": oid,
                    "sha256": hashlib.sha256(data).hexdigest(),
                    "matches_frozen": data == frozen})
report = {"commit": git("rev-parse", tag + "^{commit}").decode().strip(),
          "tree": git("rev-parse", tag + "^{tree}").decode().strip(),
          "files": entries}
(root / "audit-evidence/source-hashes.json").write_text(json.dumps(report, indent=2) + "\n")
assert all(e["matches_frozen"] for e in entries)
print(f"All {len(entries)} tracked files match the frozen tree byte for byte.")
for entry in entries:
    if entry["path"].startswith("paper/") or entry["path"] in {"lean-toolchain", "lake-manifest.json"}:
        print(entry["path"], entry["sha256"])

lock = json.loads((root / "lake-manifest.json").read_text())
for pkg in lock["packages"]:
    dest = root / ".lake/packages" / pkg["name"]
    rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=dest).decode().strip()
    subprocess.run(["git", "diff", "--exit-code", pkg["rev"], "--"], cwd=dest, check=True)
    assert rev == pkg["rev"]
    print(pkg["name"], rev, "clean pinned checkout")
