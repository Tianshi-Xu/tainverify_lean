"""Lossless term aliases for the generated initial/final relation suffix.

Only stable imported helper terms are eligible. Lean's scoped local notation
expands them normally; declarations, binders, schedules and proof bodies are
retained. The inverse is for inventories/audits, never a proof substitute.
"""
import re

_TERMS = (
    'pmInputRequests.drop', 'pmInputRequests.take',
    'smInputRequests.drop', 'smInputRequests.take',
    'SourceInitialInputEncoding.emitted_ordered_slice_eq_chunk',
    'SourceInitialInputRead.input_value_of_split',
    'RelationCompiler.RelationFact.chunked',
    'SourceEmbeddingRead.embedding_value_of_split',
    'List.take_append_drop', 'List.mem_cons_self', 'List.mem_cons_of_mem',
)
_START = 'section RuntimeRelationSource\nopen TrainVerify.Denote TrainVerify.Denote.RuntimeWorld\n'
_END = 'end RuntimeRelationSource\n'


def _token(term):
    return re.compile(r"(?<![\w.'!?])" + re.escape(term) + r"(?![\w.'!?])")


def compact(text):
    """Compact a generated suffix, returning unsupported/unprofitable text intact."""
    if (any(s in text for s in ('"', '«', '`', '/-', '--', 'RuntimeRelationSource'))
            or re.search(r"\br\d+\b", text)):
        return text
    # This pass supports only the generated declaration/unqualified-binder
    # subset. Other binding constructs are left to Lean without compaction.
    if '@[' in text or '|' in text or re.search(
            r'\b(?:opaque|axiom|constant|instance|class|structure|inductive|let|match|'
            r'rcases|obtain|cases|intro|intros|rename_i|variable|variables)\b', text):
        return text
    protected = {part for term in _TERMS for part in (term, term.split('.')[0], term.split('.')[-1])}
    declarations = re.findall(r'\b(?:def|abbrev|theorem|lemma|have)\s+([\w.\']+)', text)
    # Attribute/modifier prefixes do not hide the declaration keyword. Reject
    # relative declarations too: a nested namespace may shadow an imported term.
    if any(name in protected or name.split('.')[-1] in protected for name in declarations):
        return text
    heads = re.findall(r'[({\[]\s*([^():{}\[\]]*):', text)
    heads += re.findall(r'\bfun\b([\s\S]*?)=>', text)
    heads += re.findall(r'(?:∀|∃)\s+([^:=∈]*?)(?::|,|∈)', text)
    if any(set(re.findall(r"[\w.']+", head)) & protected for head in heads):
        return text
    body, declarations = text, []
    for term in _TERMS:
        token = _token(term)
        alias = f'r{len(declarations)}'
        declaration = f'local notation "{alias}" => {term}\n'
        count = len(token.findall(body))
        if count * (len(term.encode()) - len(alias)) <= len(declaration.encode()):
            continue
        body = token.sub(alias, body)
        declarations.append(declaration)
    candidate = _START + ''.join(declarations) + body + _END
    return candidate if len(candidate.encode()) < len(text.encode()) else text


def expand(text):
    """Recover the exact original text, also when prefixed by the old entry."""
    if _START not in text:
        return text
    prefix, _, rest = text.partition(_START)
    aliases = []
    while rest.startswith('local notation '):
        line, separator, rest = rest.partition('\n')
        match = re.fullmatch(r'local notation "(r\d+)" => (\S+)', line)
        if not separator or not match or match[2] not in _TERMS:
            raise ValueError('invalid relation source alias')
        aliases.append(match.groups())
    body, marker, suffix = rest.partition(_END)
    if not marker or not aliases:
        raise ValueError('invalid relation source scope')
    for alias, term in aliases:
        body = _token(alias).sub(term, body)
    return prefix + body + suffix
