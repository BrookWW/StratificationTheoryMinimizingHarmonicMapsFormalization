#!/usr/bin/env python3
"""Validate the complete published Lean source set and pinned dependencies."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import lean_source as lexer

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check():
    manifest = json.loads((ROOT / 'verification/modules.json').read_text())
    entries = manifest['modules']
    paths = {entry['path'] for entry in entries}
    actual = {'StratificationTheory.lean'} | {
        p.relative_to(ROOT).as_posix() for p in (ROOT / 'StratificationTheory').rglob('*.lean')}
    if len(paths) != len(entries) or actual != paths:
        raise ValueError('Missing, duplicated or unregistered Lean source')
    forbidden = re.compile(r'\b(?:sorry|sorryAx|admit|axiom|opaque|unsafe|native_decide|'
        r'implemented_by|extern|ofReduceBool|ofReduceNat|trustCompiler|skipKernelTC)\b|'
        r'\bset_option\s+(?:maxHeartbeats|maxRecDepth)\b|#(?:check|print|eval|reduce|synth|guard)\b|'
        r'(?m:^\s*example\b)')
    private = re.compile(r'/Users/|/home/|/private/|/tmp/|\.agents/|\.codex/|'
        r'(?:blueprint|review|registry)/|OriginalProof/')
    for entry in entries:
        path = ROOT / entry['path']
        if path.is_symlink() or not path.is_file() or digest(path) != entry['sha256']:
            raise ValueError('Source fingerprint changed: ' + entry['path'])
        source = path.read_text()
        if not lexer.has_module_header(source) or len(source.splitlines()) > 1500:
            raise ValueError('Invalid Lean module layout: ' + entry['path'])
        if private.search(source) or forbidden.search(lexer.code_mask(source)):
            raise ValueError('Forbidden path, unfinished proof or trust bypass: ' + entry['path'])
        declarations = lexer.declarations(source)
        if [name for _, name, public in declarations if public] != entry['exports']:
            raise ValueError('Public declaration inventory changed: ' + entry['path'])
        for name in lexer.IMPORT.findall(lexer.code_mask(source)):
            if name.startswith('StratificationTheory.') and name.replace('.', '/') + '.lean' not in paths:
                raise ValueError('Unregistered project import: ' + name)
    interfaces = json.loads((ROOT / 'verification/theorem-types.json').read_text())['declarations']
    for item in interfaces:
        source = (ROOT / item['path']).read_text()
        actual_exports = [n for _, n, public in lexer.declarations(source) if public]
        if actual_exports != [item['export']]:
            raise ValueError('Source-facing declaration ownership changed: ' + item['path'])
        if item['kind'] == 'definition':
            if digest(ROOT / item['path']) != item['full_file_sha256']:
                raise ValueError('Literal/characterized definition changed: ' + item['path'])
        else:
            begin = source.index('\n', source.index('FROZEN_ANCHOR_PROOF_BEGIN')) + 1
            end = source.rfind('\n', 0, source.index('FROZEN_ANCHOR_PROOF_END')) + 1
            if (hashlib.sha256(source[:begin].encode()).hexdigest() != item['prefix_sha256'] or
                    hashlib.sha256(source[end:].encode()).hexdigest() != item['suffix_sha256']):
                raise ValueError('Complete theorem statement region changed: ' + item['path'])
        for definition in item['definition_closure']:
            if digest(ROOT / definition['path']) != definition['sha256']:
                raise ValueError('Meaning-carrying definition closure changed')
    pins = json.loads((ROOT / 'verification/sources.json').read_text())
    for item in pins['manuscripts'] + pins['build_configuration'] + pins['verification_tools']:
        path = ROOT / item['path']
        if path.is_symlink() or digest(path) != item['sha256']:
            raise ValueError('Published verification footprint changed: ' + item['path'])
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    package_names = set()
    for item in lock['packages']:
        if item['type'] != 'git' or not re.fullmatch(r'[0-9a-f]{40}', item['rev']):
            raise ValueError('Unpinned or local dependency: ' + item['name'])
        package_names.add(item['name'])
        package = ROOT / lock['packagesDir'] / item['name']
        if package.is_symlink():
            raise ValueError('Symlinked dependency: ' + item['name'])
        head = subprocess.check_output(['git', '-C', str(package), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(package), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
        if head != item['rev'] or dirty:
            raise ValueError('Dependency source drift: ' + item['name'])
    if package_names != {'mathlib','harmonicMaps','plausible','LeanSearchClient','importGraph',
                         'proofwidgets','aesop','Qq','batteries','Cli'}:
        raise ValueError('Dependency set changed')
    if (ROOT / '.lake/package-overrides.json').exists():
        raise ValueError('Undeclared dependency override')
    expected = {x['name']: x['rev'] for x in pins['direct_dependencies']}
    actual_pins = {x['name']: x['rev'] for x in lock['packages'] if not x['inherited']}
    if expected != actual_pins:
        raise ValueError('Direct dependency revisions changed')
    print(f'SOURCE FOOTPRINT PASS: {len(entries)} exact modules; {len(interfaces)} complete interfaces')
    print('DECLARATION INVENTORY, DEFINITION BODIES, MANUSCRIPT AND BUILD FINGERPRINTS PASS')
    print('PINNED GIT DEPENDENCIES AND MODULE HYGIENE PASS')


if __name__ == '__main__':
    try:
        check()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print('ERROR:', error, file=sys.stderr)
        raise SystemExit(1)
