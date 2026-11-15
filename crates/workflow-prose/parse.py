"""Parse each passage `check:prose` reads into sentences and tokens.

Reads a JSON array of passages on standard input and writes, for each, its
sentences as spaCy's `en_core_web_sm` parses them: every token's text, lemma,
coarse and fine tag, dependency, head as an index within its sentence, and
character offset within the passage. The Rust crate applies every rule; this
script only parses.
"""

import json
import sys

import spacy


def main() -> None:
    passages = json.load(sys.stdin)
    nlp = spacy.load("en_core_web_sm", disable=["ner"])
    parsed = [
        [
            [
                [t.text, t.lemma_, t.pos_, t.tag_, t.dep_, t.head.i - s.start, t.idx]
                for t in s
            ]
            for s in doc.sents
        ]
        for doc in nlp.pipe(passages, batch_size=64)
    ]
    json.dump(parsed, sys.stdout)


if __name__ == "__main__":
    main()
