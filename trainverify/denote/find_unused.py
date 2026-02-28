#!/usr/bin/env python3
"""Find unused lemmas and theorems in trainverify/denote/."""

import re
import os
import sys
from collections import defaultdict

DENOTE_DIR = os.path.dirname(os.path.abspath(__file__))

# Match declarations like:
#   private theorem foo ...
#   lemma bar ...
#   private noncomputable lemma baz ...
DECL_RE = re.compile(
    r'^(?P<prefix>(?:(?:private|protected|noncomputable)\s+)*)'
    r'(?P<kind>theorem|lemma)\s+'
    r'(?P<name>[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)',
    re.MULTILINE,
)

def collect_lean_files(root):
    """Recursively collect all .lean files."""
    files = []
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith('.lean'):
                files.append(os.path.join(dirpath, fn))
    return sorted(files)

def relpath(f):
    return os.path.relpath(f, DENOTE_DIR)

def main():
    lean_files = collect_lean_files(DENOTE_DIR)
    # Exclude self
    lean_files = [f for f in lean_files if not f.endswith('.py')]

    # Phase 1: collect all declarations
    # Each entry: (name, kind, is_private, file, line_no)
    declarations = []
    for fpath in lean_files:
        with open(fpath, 'r') as f:
            content = f.read()
        for m in DECL_RE.finditer(content):
            name = m.group('name')
            kind = m.group('kind')
            prefix = m.group('prefix').strip()
            is_private = 'private' in prefix
            line_no = content[:m.start()].count('\n') + 1
            declarations.append((name, kind, is_private, fpath, line_no))

    # Phase 2: for each declaration, check if it's referenced elsewhere
    # For private decls, only search within the same file
    # For public decls, search all files
    # A "reference" = the name appearing somewhere other than its own declaration line

    # Pre-load all file contents
    file_contents = {}
    for fpath in lean_files:
        with open(fpath, 'r') as f:
            lines = f.readlines()
        file_contents[fpath] = lines

    unused = []
    for name, kind, is_private, decl_file, decl_line in declarations:
        # Build a regex that matches the name as a whole word
        # (not part of a larger identifier)
        pat = re.compile(r'(?<![A-Za-z_\w\.])' + re.escape(name) + r'(?![A-Za-z_\w])')

        found = False
        search_files = [decl_file] if is_private else lean_files

        for fpath in search_files:
            lines = file_contents[fpath]
            for i, line in enumerate(lines):
                line_no_here = i + 1
                # Skip the declaration line itself
                if fpath == decl_file and line_no_here == decl_line:
                    continue
                # Skip comments
                stripped = line.lstrip()
                if stripped.startswith('--'):
                    continue
                if pat.search(line):
                    found = True
                    break
            if found:
                break

        if not found:
            unused.append((name, kind, is_private, decl_file, decl_line))

    # Report
    if not unused:
        print("All lemmas and theorems are referenced.")
        return

    print(f"Found {len(unused)} unused lemma(s)/theorem(s):\n")
    # Group by file
    by_file = defaultdict(list)
    for name, kind, is_private, fpath, line_no in unused:
        by_file[fpath].append((name, kind, is_private, line_no))

    for fpath in sorted(by_file.keys()):
        print(f"  {relpath(fpath)}:")
        for name, kind, is_private, line_no in sorted(by_file[fpath], key=lambda x: x[3]):
            priv = "private " if is_private else ""
            print(f"    L{line_no}: {priv}{kind} {name}")
        print()

if __name__ == '__main__':
    main()
