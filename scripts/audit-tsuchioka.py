"""Build Tsuchioka proof components and audit every public theorem's axioms."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MODULES = ROOT / "KanadeRussell" / "Tsuchioka"

def run(args):
    result = subprocess.run(args, cwd=ROOT, capture_output=True, encoding="utf-8")
    sys.stdout.buffer.write(result.stdout.encode("utf-8"))
    sys.stderr.buffer.write(result.stderr.encode("utf-8"))
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout

def main():
    names = []
    for path in sorted(MODULES.glob("*.lean")):
        source = path.read_text(encoding="utf-8-sig")
        # The namespace/declaration scan intentionally accepts only the simple
        # file structure used by these modules, rather than guessing scopes.
        code = re.sub(r"/-.*?-/", "", source, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
            raise SystemExit(f"Unapproved proof escape in {path}")
        if re.search(r"^import\s+(Comparator|KanadeRussell\.Pending)", code, re.M):
            raise SystemExit(f"Admitted/external input import in {path}")
        scopes = []
        for line in code.splitlines():
            match = re.match(r"\s*namespace\s+(\S+)", line)
            if match:
                scopes.append(match[1])
                continue
            if re.match(r"\s*end(?:\s|$)", line):
                if not scopes:
                    raise SystemExit(f"Unrecognized scope closure in {path}")
                scopes.pop()
                continue
            match = re.match(r"\s*(?:@\[[^]]*\]\s*)?(?:theorem|lemma)\s+(\S+)", line)
            if match:
                names.append(".".join(scopes + [match[1]]))
        if scopes:
            raise SystemExit(f"Unclosed namespace in {path}")
    if not names or len(set(names)) != len(names):
        raise SystemExit("Missing or duplicated public theorem declarations")
    run(["lake", "build", "KanadeRussell.Tsuchioka"])
    out = ROOT / "build" / "tsuchioka-audit"
    out.mkdir(parents=True, exist_ok=True)
    audit = out / "Axioms.lean"
    audit.write_text("import KanadeRussell.Tsuchioka\n" +
                     "\n".join("#print axioms " + name for name in names) + "\n",
                     encoding="utf-8")
    output = run(["lake", "env", "lean", str(audit)])
    (out / "axioms.log").write_text(output, encoding="utf-8")
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output):
        found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        found[name] = set()
    if set(found) != set(names):
        raise SystemExit("Incomplete axiom output")
    for name, axioms in found.items():
        if axioms - ALLOWED:
            raise SystemExit(f"Unapproved axioms in {name}: {sorted(axioms - ALLOWED)}")
    print(f"Tsuchioka component audit: {len(names)} public theorems; only standard axioms.")
    print("Scope: Tsuchioka components. For the final KR statements, run scripts/check-comparator.py.")

if __name__ == "__main__":
    main()
