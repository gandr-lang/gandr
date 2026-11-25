# shellcheck shell=bash
# The commits that a sign-off can name (#6853). `digests` prints each word of
# the text on stdin that holds 7 to 40 hexadecimal digits and nothing else,
# one for each line. A word is a run of letters, digits and `_`: the word
# that GNU's word boundary bounds. `tr` splits the text with POSIX classes
# alone, so each host reads the same words, and a digest inside a longer word
# is no match.
digests() {
  tr -cs '[:alnum:]_' '\n' | grep -xE '[0-9a-f]{7,40}' || :
}
