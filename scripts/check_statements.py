#!/usr/bin/env python3
"""Recompute exact approved declaration types with canonical Lean kernel expressions.

The encoding preserves universe parameters, binder names and visibility,
constants and all expression structure, excluding source-position metadata.
Definition bodies are separately bound by the frozen manifest's whole-file hash.
Frozen hashes remain exact. A provider may differ only in corresponding local
proof-helper names after their propositions and complete types pass kernel checks.
"""

from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import lean_source as lexer

ROOT = Path(__file__).resolve().parents[1]

ENCODER = r'''

meta import Lean
open Lean
private meta partial def encodeLevel : Level → Json
  | .zero => toJson ("zero" : String)
  | .succ l => Json.arr #[toJson ("succ" : String), encodeLevel l]
  | .max a b => Json.arr #[toJson ("max" : String), encodeLevel a, encodeLevel b]
  | .imax a b => Json.arr #[toJson ("imax" : String), encodeLevel a, encodeLevel b]
  | .param n => Json.arr #[toJson ("param" : String), toJson n.toString]
  | .mvar n => Json.arr #[toJson ("mvar" : String), toJson n.name.toString]
private meta partial def encodeExpr : Expr → Json
  | .bvar i => Json.arr #[toJson ("bvar" : String), toJson i]
  | .fvar i => Json.arr #[toJson ("fvar" : String), toJson i.name.toString]
  | .mvar i => Json.arr #[toJson ("mvar" : String), toJson i.name.toString]
  | .sort u => Json.arr #[toJson ("sort" : String), encodeLevel u]
  | .const n us => Json.arr #[toJson ("const" : String), toJson n.toString, Json.arr (us.toArray.map encodeLevel)]
  | .app f a => Json.arr #[toJson ("app" : String), encodeExpr f, encodeExpr a]
  | .lam n t b bi => Json.arr #[toJson ("lam" : String), toJson n.toString, toJson (reprStr bi), encodeExpr t, encodeExpr b]
  | .forallE n t b bi => Json.arr #[toJson ("forall" : String), toJson n.toString, toJson (reprStr bi), encodeExpr t, encodeExpr b]
  | .letE n t v b nondep => Json.arr #[toJson ("let" : String), toJson n.toString, encodeExpr t, encodeExpr v, encodeExpr b, toJson nondep]
  | .lit l => Json.arr #[toJson ("lit" : String), toJson (reprStr l)]
  | .mdata _ e => encodeExpr e
  | .proj n i e => Json.arr #[toJson ("proj" : String), toJson n.toString, toJson i, encodeExpr e]
'''


PROVIDER_PROOF_CHECKER = r'''

private meta def requireClosedABI (e : Expr) : Elab.Command.CommandElabM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "provider ABI expression is not closed"

private meta def requireKernelABIEquality (env : Environment) (a b : Expr) :
    Elab.Command.CommandElabM Unit := do
  requireClosedABI a
  requireClosedABI b
  unless Kernel.isDefEqGuarded env {} a b do
    throwError "provider ABI kernel definitional equality failed"

private meta def checkProviderProofABI (anchor provider : Name)
    (pairs : List (Name × Name)) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let some a := env.find? anchor | throwError "missing ABI anchor"
  let some p := env.find? provider | throwError "missing ABI provider"
  unless a.levelParams == p.levelParams do
    throwError "provider ABI universe parameters differ"
  for (left, right) in pairs do
    let some l := env.find? left | throwError "missing anchor proof helper"
    let some r := env.find? right | throwError "missing provider proof helper"
    unless l.levelParams == r.levelParams do
      throwError "provider ABI helper universe parameters differ"
    if l.isUnsafe || r.isUnsafe || l.isPartial || r.isPartial then
      throwError "provider ABI helper is unsafe or partial"
    for helper in [left, right] do
      for ax in (← collectAxioms helper) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "provider ABI helper has an unauthorized axiom: {ax}"
    requireClosedABI l.type
    requireClosedABI r.type
    let .ok ls := Kernel.check env {} l.type | throwError "invalid anchor helper type"
    let .ok rs := Kernel.check env {} r.type | throwError "invalid provider helper type"
    requireKernelABIEquality env ls (.sort .zero)
    requireKernelABIEquality env rs (.sort .zero)
    requireKernelABIEquality env l.type r.type
  requireKernelABIEquality env a.type p.type
  logInfo ("PROVIDER_PROOF_ABI_OK " ++ provider.toString)
'''


def provider_proof_pairs(anchor_type, provider_type, anchor_name, provider_name):
    """Allow only corresponding declaration-local generated proof constant names."""
    pattern = re.compile(re.escape(anchor_name) + r'\._proof_([0-9]+)\Z')
    pairs = set()

    def compare(left, right):
        if left == right:
            return
        if (isinstance(left, list) and isinstance(right, list) and
                len(left) == len(right) == 3 and left[0] == right[0] == 'const' and
                isinstance(left[1], str) and isinstance(right[1], str) and
                left[2] == right[2]):
            match = pattern.fullmatch(left[1])
            if match and right[1] == provider_name + '._proof_' + match.group(1):
                pairs.add((left[1], right[1]))
                return
        if isinstance(left, list) and isinstance(right, list) and len(left) == len(right):
            for lpart, rpart in zip(left, right):
                compare(lpart, rpart)
            return
        raise ValueError('Provider type differs outside corresponding proof constants: ' + provider_name)

    compare(anchor_type, provider_type)
    if not pairs:
        raise ValueError('Provider ABI mismatch has no corresponding proof constants: ' + provider_name)
    return sorted(pairs)


def check_provider_proof_pairs(modules, mismatches):
    """Kernel-check the exact helper propositions and complete declaration types."""
    code = 'module\n' + '\n'.join('public import ' + m for m in modules)
    code += '\nmeta import Lean\nopen Lean\n' + PROVIDER_PROOF_CHECKER
    for anchor, provider, pairs in mismatches:
        encoded_pairs = ', '.join('(``' + left + ', ``' + right + ')' for left, right in pairs)
        code += '\nrun_cmd checkProviderProofABI ``' + anchor + ' ``' + provider
        code += ' [' + encoded_pairs + ']\n'
    result = subprocess.run(['lake', '--no-build', 'env', 'lean', '-DautoImplicit=false', '--stdin'],
                            cwd=ROOT, input=code, text=True, capture_output=True)
    if result.returncode:
        raise ValueError('Provider proof-constant kernel check failed:\n' + result.stdout + result.stderr)
    found = [line.removeprefix('PROVIDER_PROOF_ABI_OK ') for line in result.stdout.splitlines()
             if line.startswith('PROVIDER_PROOF_ABI_OK ')]
    if sorted(found) != sorted(provider for _, provider, _ in mismatches):
        raise ValueError('Incomplete provider proof-constant kernel checks')



def check_public_api():
    """Require the exact public import closure and Main-only visibility."""
    inventory = json.loads((ROOT / 'verification/modules.json').read_text())['modules']
    entries = {item['path'][:-5].replace('/', '.'): item for item in inventory}
    public_import = re.compile(r'(?m)^\s*public\s+import\s+(?:all\s+)?(StratificationTheory(?:\.\S+)?)\s*$')
    visited = set()
    exports = set()

    def visit(module):
        if module in visited:
            return
        visited.add(module)
        item = entries[module]
        exports.update(item['exports'])
        source = lexer.code_mask((ROOT / item['path']).read_text())
        for child in public_import.findall(source):
            visit(child)

    visit('StratificationTheory')
    api = json.loads((ROOT / 'verification/public-api.json').read_text())
    expected = api['exports']
    if api['module'] != 'StratificationTheory' or len(expected) != len(set(expected)):
        raise ValueError('Malformed public API inventory')
    if exports != set(expected):
        raise ValueError('Public import/declaration closure changed')
    code = 'module\npublic import StratificationTheory\n' + ''.join('#check ' + name + '\n' for name in expected)
    result = subprocess.run(['lake', '--no-build', 'env', 'lean', '-DautoImplicit=false', '--stdin'],
                            cwd=ROOT, input=code, text=True, capture_output=True)
    if result.returncode:
        raise ValueError('Public Main-only visibility check failed:\n' + result.stdout + result.stderr)
    print(f'PUBLIC API MATCH: {len(expected)} declarations through {len(visited)} public project modules')


def check():
    check_public_api()
    manifest = json.loads((ROOT / 'verification/theorem-types.json').read_text())
    anchors = manifest['declarations']
    names = [a['export'] for a in anchors]
    modules = [a['path'][:-5].replace('/', '.') for a in anchors]
    sealed = [a for a in anchors if a['kind'] == 'theorem']
    names += [a['implementation']['export'] for a in sealed]
    modules += [a['implementation']['module'] for a in sealed]
    code = 'module\n' + '\n'.join('public import ' + m for m in modules) + '\n' + ENCODER
    code += '\nrun_cmd do\n  let env ← getEnv\n  for n in ['
    code += ', '.join('``' + n for n in names)
    code += '] do\n    let some ci := env.find? n | throwError "missing declaration: {n}"\n'
    code += '    logInfo ("TYPEJSON " ++ n.toString ++ " " ++ (Json.arr #[toJson (ci.levelParams.map Name.toString), encodeExpr ci.type]).compress)\n'
    result = subprocess.run(['lake','--no-build','env','lean','-DautoImplicit=false','--stdin'],cwd=ROOT,
                            input=code,text=True,capture_output=True)
    if result.returncode:
        print(result.stdout+result.stderr,file=sys.stderr)
        return result.returncode
    actual = {}
    payloads = {}
    for line in result.stdout.splitlines():
        if line.startswith('TYPEJSON '):
            _,name,payload = line.split(' ',2)
            if name not in names or name in actual:
                raise ValueError('Unexpected or duplicate type record: ' + name)
            json.loads(payload)
            actual[name] = hashlib.sha256(payload.encode()).hexdigest()
            payloads[name] = payload
    if set(actual) != set(names):
        raise ValueError('Incomplete declaration type records')
    for anchor in anchors:
        if actual[anchor['export']] != anchor['abi_sha256']:
            raise ValueError('Approved ABI changed: ' + anchor['export'])
    mismatches = []
    for anchor in sealed:
        if actual[anchor['implementation']['export']] != anchor['abi_sha256']:
            name, provider = anchor['export'], anchor['implementation']['export']
            pairs = provider_proof_pairs(json.loads(payloads[name]), json.loads(payloads[provider]),
                                         name, provider)
            mismatches.append((name, provider, pairs))
    if mismatches:
        check_provider_proof_pairs(modules, mismatches)
    print(f'APPROVED DECLARATION TYPE MATCH: {len(anchors)} exact exports')
    if mismatches:
        print(f'PROVIDER PROOF-CONSTANT MATCH: {len(mismatches)} providers; exact remaining structure and kernel equality')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(check())
    except (OSError, ValueError, KeyError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
