#!/usr/bin/env python3
"""Check ordinary implementation exports against the standard Lean axiom boundary."""

from pathlib import Path
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def check():
    inventory = json.loads((ROOT / 'verification/modules.json').read_text())
    imports = []
    exports = []
    for entry in inventory['modules']:
        if entry['kind'] in {'ORDINARY_INFRASTRUCTURE', 'ORDINARY_LITERAL_INFRASTRUCTURE'}:
            imports.append('import ' + entry['path'][:-5].replace('/', '.'))
            exports.extend(entry['exports'])
    manifest_path = ROOT / 'verification/theorem-types.json'
    if manifest_path.exists():
        manifest = json.loads(manifest_path.read_text())
        for anchor in manifest['declarations']:
            imports.append('import ' + anchor['path'][:-5].replace('/', '.'))
            exports.append(anchor['export'])
    source = '\n'.join(['module', *imports, '',
                        *('#print axioms ' + name for name in exports), ''])
    result = subprocess.run(['lake', '--no-build', 'env', 'lean', '-DautoImplicit=false', '--stdin'],
                            cwd=ROOT, input=source, text=True, capture_output=True)
    if result.returncode:
        print(result.stdout + result.stderr, file=sys.stderr)
        return result.returncode
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout):
        found[name] = {axiom.strip() for axiom in axioms.split(',') if axiom.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        found[name] = set()
    if set(found) != set(exports):
        print('Missing or unexpected axiom output: ' +
              ', '.join(sorted(set(found).symmetric_difference(exports))), file=sys.stderr)
        print(result.stdout, file=sys.stderr)
        return 1
    failures = {name: sorted(axioms - ALLOWED) for name, axioms in found.items()
                if not axioms <= ALLOWED}
    if failures:
        print(json.dumps(failures, indent=2), file=sys.stderr)
        return 1
    print(f'AXIOM CLOSURE PASS: {len(exports)} ordinary and sealed exports; only standard Lean axioms')
    print('Registered provider results are covered transitively through their public interfaces.')
    return 0


if __name__ == '__main__':
    raise SystemExit(check())
