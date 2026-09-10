"""Lossless notation for fixed canonical source-read partial applications.

Graph/scope/peer/request arguments are retained exactly. Unsupported syntax or
shadowing falls back to the original source; this is not a general Lean parser.
"""
import re
from Verdict.runtime_relation_source import _token

_START = 'section RuntimeReadSource\nopen TrainVerify.Denote TrainVerify.Denote.RuntimeWorld\n'
_END = 'end RuntimeReadSource\n'
_HELPERS = ('SourceInitialInputRead.input_value_of_split',
    'SourceEmbeddingRead.embedding_value_of_split', 'SourceAddRead.add_value_of_split',
    'SourcePrimitiveRead.chunk_value_of_split', 'SourcePrimitiveRead.allToAll_value_of_split',
    'SourceMultirefRead.multiref_value_of_split')


def _prefix(helper, world):
    return f'{helper} {world}Graph {world}Scope {world}Peers {world}Graph.nodes\n    {world}InputRequests'


def compact(text):
    if (any(x in text for x in ('RuntimeReadSource', '/-', '-/', '`', '«', '\r'))
            or re.search(r'\bvP\d+\b', text)
            or text.count('section RuntimeRelationSource\n') > 1):
        return text
    protected = {p for h in _HELPERS for p in (h, h.split('.')[0], h.split('.')[-1])}
    protected.update(w+s for w in ('sm','pm') for s in ('Graph','Scope','Peers','InputRequests'))
    for line in text.splitlines():
        code = line.split('--', 1)[0]
        if '"' in code and not re.fullmatch(r'local notation "r\d+" => [\w.]+', code):
            return text
        stripped = code.strip()
        if stripped.startswith('namespace ') and stripped != 'namespace TrainVerify.Denote.RuntimeWorld':
            return text
        if stripped.startswith('open ') and any(name not in {
                'TrainVerify.Denote', 'TrainVerify.Denote.RuntimeWorld', 'SourceScopedEval',
                'SourceInitialParameterSpecs'} for name in stripped.split()[1:]):
            return text
        if re.search(r'\b(?:opaque|axiom|constant|class|structure|inductive|syntax|macro|elab)\b', code):
            return text
        if (re.search(r'\b(?:rcases|obtain|cases|induction|case|match)\b', code) or '|' in code) and not re.fullmatch(
                r'\s*rcases \w+ with rfl(?: \| rfl)*', code):
            return text
    declared = re.findall(r'\b(?:def|abbrev|theorem|lemma|have|let|namespace)\s+([\w.]+)', text)
    binders = re.findall(r'[({\[]\s*([^():{}\[\]]*):', text)
    binders += re.findall(r'\bfun\b([\s\S]*?)=>', text)
    binders += re.findall(r'\b(?:intro|intros|rename_i)\s+([^\n]+)', text)
    if any(n in protected or n.split('.')[-1] in protected for n in declared):
        return text
    if any(set(re.findall(r'[\w.]+', b)) & protected for b in binders):
        return text
    old = re.findall(r'^local notation "(r\d+)" => ([\w.]+)$', text, re.M)
    if len({a for a,_ in old}) != len(old):
        return text
    imports = re.match(r'(?:import [^\n]+\n)*', text)[0]
    body, definitions = text[len(imports):], []
    for helper in _HELPERS:
        for world in ('sm','pm'):
            for spelling in [helper]+[a for a,h in old if h==helper]:
                original = _prefix(spelling, world)
                token = _token(original)
                if spelling != helper:
                    start = body.find('section RuntimeRelationSource\n')
                    end = body.find('end RuntimeRelationSource\n', start)
                    if start<0 or end<0 or any(not start<=m.start()<end for m in token.finditer(body)):
                        continue
                alias = f'vP{len(definitions)}'
                rhs = _prefix(helper,world).replace('\n    ',' ')
                suffix = '' if spelling==helper else f' -- {spelling}'
                definition = f'local notation "{alias}" => {rhs}{suffix}\n'
                count = len(token.findall(body))
                if count*(len(original.encode())-len(alias)) <= len(definition.encode()):
                    continue
                body = token.sub(alias,body)
                definitions.append(definition)
    result = imports+_START+''.join(definitions)+body+_END
    return result if len(result.encode())<len(text.encode()) else text


def expand(text):
    if _START not in text:
        return text
    before,_,rest = text.partition(_START)
    replacements = []
    while rest.startswith('local notation "vP'):
        line,sep,rest = rest.partition('\n')
        match = re.fullmatch(r'local notation "(vP\d+)" => (.+?)(?: -- (r\d+))?',line)
        if not match or not sep:
            raise ValueError('invalid source-read notation')
        candidates = [(h,w) for h in _HELPERS for w in ('sm','pm') if _prefix(h,w).replace('\n    ',' ')==match[2]]
        if len(candidates)!=1:
            raise ValueError('unsupported source-read notation')
        helper,world = candidates[0]
        replacements.append((match[1],_prefix(match[3] or helper,world)))
    body,marker,after = rest.rpartition(_END)
    if not marker or not replacements:
        raise ValueError('invalid source-read scope')
    for alias,original in replacements:
        body = _token(alias).sub(lambda _:original,body)
    return before+body+after
