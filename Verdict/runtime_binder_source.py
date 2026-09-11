"""Lossless, finite-template binder sharing for generated theorem runs.

This is not a Lean parser. Only column-zero theorems with an exact supported
header, indented continuation lines, and their own adjacent ``#print axioms``
are eligible. Unknown syntax is left alone. Scopes never cross a declaration
or command boundary. The caller must kernel-check the unchanged full types;
this module neither publishes artifacts nor alters any source-size cap.
"""
import re

_MARKER = 'RBS_'
_FOUR = (' (s p t q : Store)\n'
         '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)')
_HEADERS = {
    _FOUR + '\n    (h : InitialParameterValues s p)': 's p t q hs hp h',
    _FOUR + '\n    (hvalues : InitialParameterValues s p)': 's p t q hs hp hvalues',
    _FOUR: 's p t q hs hp',
    ' (s t : Store) (h : smDenoteWithInputs s = some t)': 's t h',
    ' (s t : Store) (h : pmDenoteWithInputs s = some t)': 's t h',
    ' (smInit pmInit smFinal pmFinal : Store) (hs : smDenoteWithInputs smInit = some smFinal) (hp : pmDenoteWithInputs pmInit = some pmFinal)': 'smInit pmInit smFinal pmFinal hs hp',
    ' (init final : Store) (h : pmDenoteWithInputs init = some final)': 'init final h',
    ' (init final : Store) (h : smDenoteWithInputs init = some final)': 'init final h',
}
_NAME = r'[A-Za-z_][A-Za-z_0-9]*'
_PARAMETER_DEFINITION = (
    'def InitialParameterValues (initSM initPM : Store) : Prop :=\n'
    '  All (fun spec => spec.values initSM initPM) initialParameterSpecs\n')
_RECORD = re.compile(
    r'^theorem (?P<name>' + _NAME + r')(?P<rest>[^\n]*\n(?:[ \t]+[^\n]*\n)*)'
    r'#print axioms (?P=name)\n', re.M)
_SHADOW = re.compile(
    r'\b(?:def|abbrev|theorem|lemma|opaque|axiom|constant|instance|class|structure|inductive|namespace)'
    r'\s+(?:[\w\']+\.)*(?:Store|smDenoteWithInputs|pmDenoteWithInputs|InitialParameterValues|some)\b')


def _unsupported(text):
    # Allow the existing finite term-notation wrapper, not arbitrary strings.
    # Line comments outside records are boundaries; block comments/quotations
    # can hide apparent column-zero commands and therefore reject the input.
    if any(token in text for token in ('\r', '/-', '-/', '`', '«', '»')):
        return True
    # The generated relation's own exact definition is not a shadowing
    # extension. Exempt only this complete literal block, never its name alone.
    for line in text.replace(_PARAMETER_DEFINITION, '').splitlines():
        code = line.split('--', 1)[0]
        if '"' in code and not re.fullmatch(
                r'local notation "r[0-9]+" => [A-Za-z_][A-Za-z_0-9.]*', code):
            return True
        if re.search(r'\b(?:variable|variables|include|omit|syntax|macro|elab)\b', code):
            return True
        if _SHADOW.search(code):
            return True
    return False


def _records(text):
    for match in _RECORD.finditer(text):
        rest = match['rest']
        if '--' in rest or '@[' in rest:
            continue
        # Lean permits independent commands to be indented. They are not
        # theorem continuations and must never enter this theorem's include.
        if re.search(r'(?m)^[ \t]+(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*'
                r'(?:theorem|lemma|def|abbrev|opaque|axiom|constant|instance|class|structure|inductive|'
                r'namespace|section|end|open|attribute|set_option|variable|include|omit|export|syntax|macro|elab|example)\b'
                r'|^[ \t]+#', rest):
            continue
        for header in _HEADERS:
            if rest.startswith(header + ' :'):
                yield match, header
                break


def _safe_start(text, position):
    before = text[:position].rstrip('\n')
    if not before:
        return True
    line = before.rsplit('\n', 1)[-1]
    return bool(re.fullmatch(
        r'(?:#print axioms ' + _NAME + r'|namespace [A-Za-z_][A-Za-z_0-9.]*|'
        r'set_option maxHeartbeats 500000|set_option maxRecDepth 4096|'
        r'(?:noncomputable )?section(?: [A-Za-z_][A-Za-z_0-9.]*)?|'
        r'end(?: [A-Za-z_][A-Za-z_0-9.]*)?|open [A-Za-z_][A-Za-z_0-9. ]*)', line))


def compact(text):
    """Share only profitable contiguous exact headers; otherwise return input."""
    if _MARKER in text or _unsupported(text):
        return text
    records = list(_records(text))
    edits = []
    index = 0
    while index < len(records):
        first, header = records[index]
        end = index + 1
        while (end < len(records) and records[end][1] == header
               and records[end - 1][0].end() == records[end][0].start()):
            end += 1
        group = records[index:end]
        index = end
        if len(group) < 2 or not _safe_start(text, first.start()):
            continue
        marker = _MARKER + str(len(edits))
        body = ''.join(m[0][:m.start('rest') - m.start()]
                       + m['rest'][len(header):]
                       + f"#print axioms {m['name']}\n" for m, _ in group)
        replacement = (f'section {marker}\nvariable{header}\n'
                       f'include {_HEADERS[header]}\n' + body + f'end {marker}\n')
        stop = group[-1][0].end()
        if len(replacement.encode()) < len(text[first.start():stop].encode()):
            edits.append((first.start(), stop, replacement))
    for start, stop, replacement in reversed(edits):
        text = text[:start] + replacement + text[stop:]
    return text


def expand(text):
    """Invert this representation exactly, preserving all surrounding bytes."""
    start_re = re.compile(r'^section (' + _MARKER + r'[0-9]+)\n', re.M)
    edits = []
    for start in start_re.finditer(text):
        rest = text[start.end():]
        for header, names in _HEADERS.items():
            opening = f'variable{header}\ninclude {names}\n'
            if rest.startswith(opening):
                break
        else:
            raise ValueError('unsupported binder source header')
        body_start = start.end() + len(opening)
        closing = f'end {start[1]}\n'
        body_end = text.find(closing, body_start)
        if body_end < 0:
            raise ValueError('unterminated binder source scope')
        body = text[body_start:body_end]
        records = list(_RECORD.finditer(body))
        if (len(records) < 2 or ''.join(m[0] for m in records) != body
                or any(not m['rest'].startswith(' :') for m in records)):
            raise ValueError('invalid binder source body')
        restored = ''.join(m[0][:m.start('rest') - m.start()] + header
                           + m['rest'] + f"#print axioms {m['name']}\n" for m in records)
        edits.append((start.start(), body_end + len(closing), restored))
    for start, stop, restored in reversed(edits):
        text = text[:start] + restored + text[stop:]
    return text
