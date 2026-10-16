"""Module-aware Lean source inspection helpers.

Adapted from Scott Armstrong's LeanAutoformalizationSkills,
lean-project-architecture/scripts/check_lean_modules.py, revision
05a07311f16bc581729e52f3e73647b95fa9bef1 (CC BY 4.0).
The public release retains the lexer and declaration helpers only.
See LICENSES/Armstrong-CC-BY-4.0.txt.
"""
from __future__ import annotations
import re

# `import`, `public import`, `meta import`, `public meta import`, each optionally `all`.
IMPORT = re.compile(r"(?m)^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(\S+)[ \t]*$")
MODULE_KEYWORD = re.compile(r"module(?![\w'.!?])")
CHAR_LITERAL = re.compile(r"'(?:\\.|[^\\'\n])'")
# Lines an import-only aggregator may contain besides imports.
SCAFFOLD_LINE = re.compile(
    r"[ \t]*(?:module|(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?\S+|"
    r"namespace[ \t]+\S+|end(?:[ \t]+\S+)?|"
    r"(?:@\[[^\]\n]*\][ \t]*)*(?:(?:public|private|noncomputable)[ \t]+)*section(?:[ \t]+\S+)?|"
    r"open[ \t].*|set_option[ \t].*)?[ \t]*")
IDENT = r"(?:[A-Za-z_][A-Za-z0-9_'!?]*|«[^»\n]+»)"
NAME = rf"{IDENT}(?:\.{IDENT})*"
NAMESPACE = re.compile(rf"^[ \t]*namespace[ \t]+({NAME})")
SECTION = re.compile(
    rf"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*((?:(?:public|private|noncomputable)[ \t]+)*)section(?:[ \t]+{NAME})?[ \t]*$")
END = re.compile(rf"^[ \t]*end(?:[ \t]+{NAME})?[ \t]*$")
DECL = re.compile(
    r"^[ \t]*(?:(?:open|set_option)\b[^\n]*?\bin[ \t]+)*(?:@\[[^\]\n]*\][ \t]*)*"
    r"((?:(?:private|protected|public|meta|noncomputable|unsafe|partial|nonrec|scoped|local)[ \t]+)*)"
    r"(theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|axiom)\b"
    rf"(?:[ \t]+({NAME}))?")


def header_token_offset(text: str) -> int:
    """Offset of the first token after ordinary comments and whitespace.

    `--` line comments and (nested) `/- -/` block comments are skipped. A doc
    comment `/-- -/` or module doc `/-! -/` is a command and ends the scan: it
    cannot precede `module`.
    """
    index, size = 0, len(text)
    while index < size:
        if text[index].isspace() or text[index] == "﻿":
            index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            index = size if newline < 0 else newline + 1
        elif text.startswith("/-", index) and not text.startswith(("/--", "/-!"), index):
            depth, index = 1, index + 2
            while index < size and depth:
                if text.startswith("/-", index):
                    depth, index = depth + 1, index + 2
                elif text.startswith("-/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
        else:
            return index
    return size


def has_module_header(text: str) -> bool:
    return MODULE_KEYWORD.match(text, header_token_offset(text)) is not None


def code_mask(text: str) -> str:
    """Blank comments (including doc comments) and string literals, keeping offsets and newlines."""
    out = list(text)
    index, size = 0, len(text)

    def blank(start: int, end: int) -> None:
        for position in range(start, end):
            if out[position] != "\n":
                out[position] = " "

    while index < size:
        if text.startswith("--", index):
            end = text.find("\n", index)
            end = size if end < 0 else end
            blank(index, end)
            index = end
        elif text.startswith("/-", index):
            start, depth, index = index, 1, index + 2
            while index < size and depth:
                if text.startswith("/-", index):
                    depth, index = depth + 1, index + 2
                elif text.startswith("-/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            blank(start, index)
        elif (text[index] == "'" and CHAR_LITERAL.match(text, index)
              and not (index and (text[index - 1].isalnum() or text[index - 1] in "_'!?"))):
            index = CHAR_LITERAL.match(text, index).end()
        elif text[index] == '"':
            start, index = index, index + 1
            while index < size and text[index] != '"':
                index += 2 if text[index] == "\\" else 1
            index = min(index + 1, size)
            blank(start, index)
        else:
            index += 1
    return "".join(out)


def is_import_only(text: str) -> bool:
    """True for an aggregator: code is only the module header, imports and scope scaffolding."""
    lines = [line for line in code_mask(text).splitlines() if line.strip()]
    return (bool(lines) and all(SCAFFOLD_LINE.fullmatch(line) for line in lines)
            and any(IMPORT.match(line) for line in lines))


def qualified_name(namespaces: list[str], name: str) -> str:
    """The full name of `name` declared under `namespaces`; `_root_.X` names X."""
    if name.startswith("_root_."):
        return name[len("_root_."):]
    return ".".join([*namespaces, name])


def declarations(text: str) -> list[tuple[str, str, bool]]:
    """(kind, full name, exported) for each named top-level declaration, lexically.

    In a module a declaration is exported when it is marked `public`, or lies in
    a `public section` and is not `private`. In a non-module file every
    non-`private` declaration is exported.
    """
    module = has_module_header(text)
    namespaces: list[str] = []
    scopes: list[tuple[int, str | None]] = []  # (namespace parts, section visibility)
    found: list[tuple[str, str, bool]] = []
    for line in code_mask(text).splitlines():
        if match := NAMESPACE.match(line):
            parts = match.group(1).split(".")
            namespaces.extend(parts)
            scopes.append((len(parts), None))
        elif match := SECTION.match(line):
            words = match.group(1).split()
            scopes.append((0, "public" if "public" in words else "private" if "private" in words else None))
        elif END.match(line):
            if scopes:
                count, _visibility = scopes.pop()
                if count:
                    del namespaces[-count:]
        elif match := DECL.match(line):
            modifiers, kind, name = match.group(1).split(), match.group(2), match.group(3)
            if name is None:
                continue
            default = next((v for _c, v in reversed(scopes) if v is not None),
                           "private" if module else "public")
            exported = "private" not in modifiers and ("public" in modifiers or default == "public")
            found.append((kind, qualified_name(namespaces, name), exported))
    return found


