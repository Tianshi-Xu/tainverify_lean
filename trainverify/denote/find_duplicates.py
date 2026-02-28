#!/usr/bin/env python3
"""Find duplicate/similar lemmas and theorems across trainverify/denote/.

For each lemma/theorem name that appears in multiple files, extracts the
full statement (up to `:= by`) and compares them. Reports:
  - IDENTICAL: same statement, can be directly merged
  - SIMILAR: same name, different parameters (e.g. different shapes)
"""

import re
import os
from collections import defaultdict

DENOTE_DIR = os.path.dirname(os.path.abspath(__file__))

# Match theorem/lemma declarations
DECL_RE = re.compile(
    r'^(?P<prefix>(?:(?:private|protected|noncomputable)\s+)*)'
    r'(?P<kind>theorem|lemma)\s+'
    r'(?P<name>[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)',
    re.MULTILINE,
)

def collect_lean_files(root):
    files = []
    for dirpath, _, filenames in os.walk(root):
        for fn in sorted(filenames):
            if fn.endswith('.lean'):
                files.append(os.path.join(dirpath, fn))
    return sorted(files)

def relpath(f):
    return os.path.relpath(f, DENOTE_DIR)

def extract_statement(content, start):
    """Extract the statement from start position up to ':= by' or ':= {' or ':= ⟨'."""
    # Find the end of the statement: look for ':= by' or ':=' at the start of a line
    rest = content[start:]
    # Match ':= by' or just ':=' followed by something
    m = re.search(r':=\s*by\b|:=\s*\{|:=\s*⟨|:=\s*$', rest)
    if m:
        stmt = rest[:m.start()].strip()
    else:
        # Fallback: take first 500 chars
        stmt = rest[:500].strip()
    return stmt

def normalize_statement(stmt):
    """Normalize a statement for comparison: remove variable names, normalize whitespace."""
    # Remove the declaration prefix (private/theorem/lemma name)
    s = re.sub(r'^(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\s+\S+\s*', '', stmt)
    # Normalize whitespace
    s = re.sub(r'\s+', ' ', s).strip()
    return s

def extract_shape_signature(stmt):
    """Extract a 'shape signature' - the key numeric constants that define the shape."""
    # Find all shape-like patterns: [n, n, n, n]
    shapes = re.findall(r'\[[\d,\s]+\]', stmt)
    return tuple(shapes) if shapes else ()

def main():
    lean_files = collect_lean_files(DENOTE_DIR)
    lean_files = [f for f in lean_files if not f.endswith('.py')]

    # Phase 1: collect all declarations with their statements
    # {name: [(file, line, prefix, kind, statement, normalized)]}
    decl_map = defaultdict(list)

    for fpath in lean_files:
        with open(fpath, 'r') as f:
            content = f.read()
        for m in DECL_RE.finditer(content):
            name = m.group('name')
            kind = m.group('kind')
            prefix = m.group('prefix').strip()
            line_no = content[:m.start()].count('\n') + 1
            stmt = extract_statement(content, m.start())
            norm = normalize_statement(stmt)
            decl_map[name].append({
                'file': fpath,
                'line': line_no,
                'prefix': prefix,
                'kind': kind,
                'statement': stmt,
                'normalized': norm,
            })

    # Phase 2: find names with multiple declarations
    duplicates = {name: entries for name, entries in decl_map.items()
                  if len(entries) > 1}

    if not duplicates:
        print("No duplicate names found.")
        return

    # Phase 3: classify each group
    identical_groups = []
    similar_groups = []

    for name, entries in sorted(duplicates.items()):
        # Group entries by normalized statement
        by_norm = defaultdict(list)
        for e in entries:
            by_norm[e['normalized']].append(e)

        if len(by_norm) == 1:
            # All entries have identical statements
            identical_groups.append((name, entries))
        else:
            # Some entries differ
            similar_groups.append((name, entries, by_norm))

    # Report
    print(f"{'='*72}")
    print(f"IDENTICAL statements ({len(identical_groups)} groups) — can merge directly")
    print(f"{'='*72}\n")

    for name, entries in sorted(identical_groups, key=lambda x: -len(x[1])):
        files = [f"{relpath(e['file'])}:{e['line']}" for e in entries]
        print(f"  {name} ({len(entries)}x):")
        for f in files:
            print(f"    {f}")
        # Print the statement once (truncated)
        stmt_preview = entries[0]['normalized'][:120]
        print(f"    Statement: {stmt_preview}...")
        print()

    print(f"\n{'='*72}")
    print(f"SIMILAR names, DIFFERENT statements ({len(similar_groups)} groups)")
    print(f"{'='*72}\n")

    for name, entries, by_norm in sorted(similar_groups, key=lambda x: -len(x[1])):
        print(f"  {name} ({len(entries)} declarations, {len(by_norm)} variants):")
        for i, (norm, group) in enumerate(sorted(by_norm.items(),
                                                  key=lambda x: -len(x[1]))):
            files = [f"{relpath(e['file'])}:{e['line']}" for e in group]
            # Extract shapes for a quick summary
            shapes = extract_shape_signature(norm)
            shape_str = f" shapes={list(shapes)}" if shapes else ""
            print(f"    Variant {i+1} ({len(group)}x){shape_str}:")
            for f in files:
                print(f"      {f}")
        print()

    # Summary
    total_identical = sum(len(e) for _, e in identical_groups)
    total_similar = sum(len(e) for _, e, _ in similar_groups)
    mergeable_lines = sum(len(e) - 1 for _, e in identical_groups)
    print(f"{'='*72}")
    print(f"Summary:")
    print(f"  {total_identical} declarations in {len(identical_groups)} identical groups")
    print(f"  {total_similar} declarations in {len(similar_groups)} similar groups")
    print(f"  Up to {mergeable_lines} declarations could be eliminated by merging identical groups")
    print(f"{'='*72}")

if __name__ == '__main__':
    main()
