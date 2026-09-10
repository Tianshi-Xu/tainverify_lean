"""Lossless notation for fixed canonical source reads and entry terms.

Graph/scope/peer/request arguments are retained exactly. Unsupported syntax or
shadowing falls back to the original source; this is not a general Lean parser.
"""
import re
from Verdict.runtime_relation_source import _token

_START = 'section RuntimeReadSource\nopen TrainVerify.Denote TrainVerify.Denote.RuntimeWorld\n'
_END = 'end RuntimeReadSource\n'
_VERSION = '-- RuntimeReadSource v2\n'
_LEGACY_HELPERS = ('SourceInitialInputRead.input_value_of_split',
    'SourceEmbeddingRead.embedding_value_of_split', 'SourceAddRead.add_value_of_split',
    'SourcePrimitiveRead.chunk_value_of_split', 'SourcePrimitiveRead.allToAll_value_of_split',
    'SourceMultirefRead.multiref_value_of_split')
_HELPERS = _LEGACY_HELPERS + (
    'SourceAllGatherRead.allGather_value_of_split',
    'SourceLayernormRead.layernorm_value_of_split',
    'SourceLayoutRead.transposeAxes_value_of_split',
    'SourceLayoutRead.view_value_of_split',
    'SourceLinearRead.linear_value_of_split',
)
_ENTRY_TERMS = (
    'pmInputRequests.drop', 'pmInputRequests.take', 'pmInputRequests',
    'chunkPrimDimN', 'List.take_append_drop', 'AllToAllSourceFaithful.tensor',
    'List.mem_cons_self', 'pmDenoteWithInputs', 'allGatherPrimDimN',
    'smInputRequests', 'smInputRequests.drop', 'smDenoteWithInputs',
    'List.mem_cons_of_mem', 'congrArg₂', 'fw_embedding', 'List.Forall₂.cons',
    'SourceLayernormRead.layernorm_value_of_split', 'RelationCompiler.ReplicatedRel',
    'fw_layernorm', 'smInputRequests.take', 'List.not_mem_nil', 'List.cons',
    'chunkPrimDimN_shape',
)
_ENTRY_METHODS = {w + 'InputRequests.' + op for w in ('sm', 'pm') for op in ('take', 'drop')}
_IDENT = r"[\w.'!?]+"
_OLD = r'local notation "(r\d+)" => ([\w.]+)'


def _prefix(helper, world):
    return f'{helper} {world}Graph {world}Scope {world}Peers {world}Graph.nodes\n    {world}InputRequests'


def _entry_definition(alias, term):
    # Bare field notation eta-expands; default argument precedence eats `++`.
    if term in _ENTRY_METHODS:
        return f'local notation:max "{alias}" n:max => {term} n\n'
    return f'local notation "{alias}" => {term}\n'


def _code(text):
    """Offset-preserving mask: comments, imports and notation RHSs are not uses."""
    lines = []
    for line in text.splitlines(keepends=True):
        code = line.split('--', 1)[0].rstrip('\n')
        if code.lstrip().startswith(('import ', 'local notation')):
            code = ''
        lines.append(code + ''.join('\n' if c == '\n' else ' ' for c in line[len(code):]))
    return ''.join(lines)


def _replace(text, token, replacement):
    # Masking must not manufacture a match across an inline comment.
    matches = [m for m in token.finditer(_code(text)) if text[m.start():m.end()] == m[0]]
    for m in reversed(matches):
        text = text[:m.start()] + replacement + text[m.end():]
    return text


def _balanced(text):
    stack = []
    for line in _code(text).splitlines():
        m = re.fullmatch(r'\s*(?:noncomputable\s+)?(section|namespace|end)(?:\s+([\w.]+))?\s*', line)
        if not m:
            continue
        if m[1] != 'end':
            stack.append(m[2])
        elif not stack or (m[2] is not None and stack[-1] != m[2]):
            return False
        else:
            stack.pop()
    return not stack


def compact(text):
    return _compact(text, _HELPERS)


def _compact(text, helpers):
    if (any(x in text for x in ('RuntimeReadSource', '/-', '-/', '`', '«', '\r'))
            or re.search(r'\b(?:vP|c)\d+\b', text)
            or text.count('section RuntimeRelationSource\n') > 1):
        return text
    protected = {p for h in helpers + _ENTRY_TERMS
                 for p in (h, *h.split('.'))}
    protected.update(w+s for w in ('sm','pm') for s in ('Graph','Scope','Peers','InputRequests'))
    lines = [line.split('--', 1)[0] for line in text.splitlines()]
    for i, code in enumerate(lines):
        old_notation = re.fullmatch(_OLD, code)
        if '"' in code and not old_notation:
            return text
        stripped = code.strip()
        if stripped.startswith('namespace ') and stripped != 'namespace TrainVerify.Denote.RuntimeWorld':
            return text
        if stripped.startswith('open ') and any(name not in {
                'TrainVerify.Denote', 'TrainVerify.Denote.RuntimeWorld', 'SourceScopedEval',
                'SourceInitialParameterSpecs'} for name in stripped.split()[1:]):
            return text
        if re.search(r'\b(?:opaque|axiom|constant|class|structure|inductive|syntax|macro|elab|instance|export|generalize|set)\b', code):
            return text
        if not old_notation and re.search(r'\b(?:notation|infixl?|infixr|prefix|postfix)\b', code):
            return text
        if (re.search(r'\b(?:rcases|obtain|cases|induction|case|match)\b', code) or '|' in code) and not re.fullmatch(
                r'\s*rcases \w+ with rfl(?: \| rfl)*', code):
            return text
        tactic = re.search(r"(?<![\w.'])\b(?:intro|intros|rename_i)\b", code)
        if tactic:
            following = next((s for s in lines[i+1:] if s.strip()), '')
            leading = following[:len(following) - len(following.lstrip())]
            # Lean permits arguments on a line strictly beyond the tactic's
            # own column. A bullet's same-column proof is not an argument.
            if '\t' in code[:tactic.start()] or '\t' in leading or len(leading) > tactic.start():
                return text
        # These positions accept names, not terms. Include indented continuations
        # but not subsequent proof steps at the same indentation.
        command = re.search(r'\b(?:unfold|delta|attribute|include|omit|set_option|section|end)\b|#\w+', code)
        if command:
            names = code[command.end():]
            indent = len(code) - len(code.lstrip())
            for following in lines[i+1:]:
                if not following.strip():
                    continue
                if len(following) - len(following.lstrip()) <= indent:
                    break
                names += '\n' + following
            if any(n in protected or n.split('.')[-1] in protected
                   for n in re.findall(_IDENT, names)):
                return text
    code = _code(text)
    # Only complete, directly applied decimal-index methods are supported.
    # In particular `f requests.take 2` must not become `f (requests.take 2)`.
    for term in _ENTRY_METHODS:
        for use in _token(term).finditer(code):
            if (not re.search(r'(?:\(|:=|(?<![=<>!:+*/-])=|\+\+|∈)\s*$', code[:use.start()])
                    or not re.match(r" (?:0|[1-9][0-9]*)(?![\w.'!?])", code[use.end():])):
                return text
    declared = re.findall(r'\b(?:def|abbrev|theorem|lemma|have|let|namespace)\s+(' + _IDENT + ')', code)
    binders = re.findall(r'[({\[]\s*([^():{}\[\]]*):', code)
    binders += re.findall(r'\bfun\b([\s\S]*?)=>', code)
    binders += re.findall(r'\b(?:intro|intros|rename_i)\s+([^\n]+)', code)
    binders += re.findall(r'\bvariables?\s+(' + _IDENT + r'(?:[ \t]+' + _IDENT + r')*)', code)
    binders += re.findall(r'(?:∀|∃|\bforall\b|\bexists\b)\s+([^:=∈]*?)(?::|,|∈)', code)
    binders += re.findall(r'\b(?:let|have|def|abbrev)\s+(' + _IDENT + r'(?:\s+' + _IDENT + r')*)\s*(?::|:=)', code)
    if any(n in protected or n.split('.')[-1] in protected for n in declared):
        return text
    if any(any(n in protected or n.split('.')[-1] in protected
               for n in re.findall(_IDENT, b)) for b in binders):
        return text
    old = re.findall('^' + _OLD + '$', text, re.M)
    if len({a for a,_ in old}) != len(old) or not _balanced(text):
        return text
    imports = re.match(r'(?:import [^\n]+\n)*', text)[0]
    body, definitions = text[len(imports):], []
    extended = False
    for helper in helpers:
        for world in ('sm','pm'):
            for spelling in [helper]+[a for a,h in old if h==helper]:
                original = _prefix(spelling, world)
                token = _token(original)
                if spelling != helper:
                    start = body.find('section RuntimeRelationSource\n')
                    end = body.find('end RuntimeRelationSource\n', start)
                    if start<0 or end<0 or any(not start<=m.start()<end for m in token.finditer(_code(body))):
                        continue
                alias = f'vP{len(definitions)}'
                rhs = _prefix(helper,world).replace('\n    ',' ')
                suffix = '' if spelling==helper else f' -- {spelling}'
                definition = f'local notation "{alias}" => {rhs}{suffix}\n'
                replaced = _replace(body, token, alias)
                if len(body.encode()) - len(replaced.encode()) <= len(definition.encode()):
                    continue
                body = replaced
                definitions.append(definition)
                extended |= helper not in _LEGACY_HELPERS
    terms = []
    for original in _ENTRY_TERMS:
        alias = f'c{len(terms)}'
        definition = _entry_definition(alias, original)
        replaced = _replace(body, _token(original), alias)
        if len(body.encode()) - len(replaced.encode()) <= len(definition.encode()):
            continue
        body = replaced
        terms.append(definition)
    # Only profitable added prefixes opt into the extended canonical whitelist.
    version = _VERSION if extended else ''
    result = imports+_START+version+''.join(definitions+terms)+body+_END
    return result if len(result.encode())<len(text.encode()) else text


def expand(text):
    """Strict inverse metadata validation; this is not Lean elaboration evidence."""
    if 'RuntimeReadSource' not in text:
        return text
    if text.count(_START) != 1 or text.count(_END) != 1:
        raise ValueError('invalid source-read scope')
    before,_,rest = text.partition(_START)
    if not re.fullmatch(r'(?:import [^\n]+\n)*', before) or not rest.endswith(_END):
        raise ValueError('invalid source-read scope')
    extended = rest.startswith(_VERSION)
    helpers = _HELPERS if extended else _LEGACY_HELPERS
    if extended:
        rest = rest[len(_VERSION):]
    replacements = []
    seen = set()
    while rest.startswith('local notation "vP'):
        line,sep,rest = rest.partition('\n')
        match = re.fullmatch(r'local notation "(vP\d+)" => (.+?)(?: -- (r\d+))?',line)
        if not match or not sep or match[1] != f'vP{len(replacements)}':
            raise ValueError('invalid source-read notation')
        candidates = [(h,w) for h in helpers for w in ('sm','pm') if _prefix(h,w).replace('\n    ',' ')==match[2]]
        key = (match[2], match[3])
        if len(candidates)!=1 or key in seen:
            raise ValueError('unsupported source-read notation')
        seen.add(key)
        helper,world = candidates[0]
        replacements.append((match[1],_prefix(match[3] or helper,world)))
    terms = []
    last = -1
    while rest.startswith(('local notation "c', 'local notation:max "c')):
        line,sep,rest = rest.partition('\n')
        match = re.fullmatch(r'local notation(?::max)? "(c\d+)"(?: n:max)? => (\S+)(?: n)?', line)
        if (not match or not sep or match[1] != f'c{len(terms)}'
                or match[2] not in _ENTRY_TERMS or _ENTRY_TERMS.index(match[2]) <= last
                or line + '\n' != _entry_definition(match[1], match[2])):
            raise ValueError('invalid entry-term notation')
        last = _ENTRY_TERMS.index(match[2])
        terms.append((match[1], match[2]))
    body = rest[:-len(_END)]
    if not (replacements or terms) or not _balanced(body):
        raise ValueError('invalid source-read scope')
    for alias,original in terms + replacements:
        body = _replace(body, _token(alias), original)
    result = before+body
    if re.search(r'\b(?:vP|c)\d+\b', _code(result)) or 'RuntimeReadSource' in result:
        raise ValueError('invalid source-read alias use')
    # Validate each format against its own canonical helper whitelist.
    # Old vP-only entries predate the term whitelist and remain decodable.
    if (terms or extended) and _compact(result, helpers) != text:
        raise ValueError('noncanonical entry-term source')
    return result
