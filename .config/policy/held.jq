# The functions of one unit that `allocation_free_region` holds for a change
# (#7632), read from the unit's base record `$base` and from the record
# `$head` that the run writes. Each record is JSON lines; an item of kind
# `fn` or `assoc-fn` with a string body is a function. An empty base record
# is a unit new at the base, and the lint holds each function. A base whose
# bodies carry the head's hash scheme holds each function whose body differs
# from the base's, or that the base lacks. A base of another scheme holds
# nothing, as the lint reads it. The output is `{read, held}`: whether the
# lint reads the base, and the count of the functions it holds.
def functions($text):
  [$text | split("\n")[] | select(test("\\S")) | (try fromjson catch null)
    | select(type == "object" and .record == "item" and (.kind == "fn" or .kind == "assoc-fn") and (.body | type) == "string")];
functions($head) as $now
| ([$now[].body | split("-")[0]] | unique) as $schemes
| if ($base | test("\\S") | not) then {read: true, held: ($now | length)}
  else
    (functions($base) | map({key: .path, value: .body}) | from_entries) as $was
    | if [$was[] | . as $body | $schemes | any(. as $scheme | $body | startswith($scheme + "-"))] | any
      then {read: true, held: ([$now[] | select($was[.path] != .body)] | length)}
      else {read: false, held: 0}
      end
  end
