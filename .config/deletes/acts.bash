#!/usr/bin/env bash
# Prints the act of each item and test that leaves its place and whose body
# stands at an item that the head adds (#7058), as a JSON object
# `{<id>: {act, at}}`. `act` is `moved` when the last segment of the two
# paths is the same, and `renamed` when it differs. `at` is the id at the
# head. An item that the object does not hold stands nowhere in the head, and
# the check reads it as deleted.
#
# Two bodies are the same when their tokens are the same. The comparison
# sets aside comments, whitespace, the visibility (`pub`, `pub(…)`), `use`
# declarations, the module path before each name (`a::b::C` reads as `C`),
# the name of the item itself, and the attributes that change no behaviour:
# `inline`, `must_use`, `doc` and the lint levels. A move across crates adds
# `#[inline]` to a small function. A false match needs an item of the head
# with the same tokens, so the text stands in the head.
#
# A body of a test at the base matches a head item of either flag (#7103):
# the library unit holds an item of a fixture module only when the run turns
# on the feature, so a helper that moves from a test module into a fixture
# module can read as a test at the base and as an item at the head. A body
# of an item at the base matches only an item at the head, so an item that
# goes from the library into test code still reads as deleted.
#
# `<items-base>` and `<items-head>` are the inventories of `check.bash`:
# `{id, kind, file, start, end, test}`, each file at its path in the tree. The
# text before comes from `<base>` in one `git cat-file --batch`, and the text
# after from the work tree. An item whose file is null, or whose text the
# check cannot read, matches nothing, so it reads as deleted.
#
# Usage: acts.bash <base> <items-base> <items-head>
set -euo pipefail
base=${1:?acts.bash takes the base}
items_base=${2:?acts.bash takes the base inventory}
items_head=${3:?acts.bash takes the head inventory}
root=$(git rev-parse --show-toplevel)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-acts.XXXXXX")
trap 'rm -rf "$work"' EXIT
# Each item that leaves, and each item that the head adds: side, kind, test,
# id, file, start and end, one a line.
jq -r -n --slurpfile b "$items_base" --slurpfile h "$items_head" '
  def ids($items): $items | map({key: .id, value: true}) | from_entries;
  ids($b[0]) as $bi | ids($h[0]) as $hi
  | ($b[0][] | select(.file != null and ($hi[.id] | not)) | ["base"] + [.kind, (.test // false), .id, .file, .start, .end]),
    ($h[0][] | select(.file != null and ($bi[.id] | not)) | ["head"] + [.kind, (.test // false), .id, .file, .start, .end])
  | map(tostring) | join("\t")' > "$work/items"
awk -F '\t' -v base="$base" '$1 == "base" && !seen[$5]++ { print base ":" $5, $5 }' "$work/items" \
  | git cat-file --batch='%(objectname) %(objecttype) %(objectsize) %(rest)' > "$work/blobs"
perl -e '
  use strict;
  use warnings;
  my ($root, $blobs, $items) = @ARGV;
  # The text of each file of the base, by its path.
  my %before;
  open my $in, "<:raw", $blobs or die "acts.bash: $blobs: $!\n";
  while (my $header = <$in>) {
    chomp $header;
    my ($object, $type, $size, $path) = split / /, $header, 4;
    next unless defined $path and $type eq "blob";
    read($in, my $text, $size) == $size or die "acts.bash: a short read of $path\n";
    $before{$path} = $text;
    <$in>;
  }
  close $in;
  my %after;
  sub text_of {
    my ($side, $file) = @_;
    return $before{$file} if $side eq "base";
    unless (exists $after{$file}) {
      $after{$file} = undef;
      if (open my $f, "<:raw", "$root/$file") { local $/; $after{$file} = <$f>; close $f; }
    }
    return $after{$file};
  }
  # The tokens of a text: words, numbers, literals and single marks.
  sub tokens {
    my ($text) = @_;
    my @tokens;
    while ($text =~ m{\G(?:\s+|//[^\n]*|/\*.*?\*/|(r(\#*)".*?"\2)|(b?"(?:\\.|[^"\\])*")|(b?\x27(?:\\.|[^\x27\\])\x27)|([A-Za-z_][A-Za-z0-9_]*|[0-9][A-Za-z0-9_.]*)|(\S))}gcs) {
      my $token = $1 // $3 // $4 // $5 // $6;
      push @tokens, $token if defined $token;
    }
    return @tokens;
  }
  # The attributes that change no behaviour: a hint, a lint level or a doc,
  # and a `cfg_attr` that gives such attributes alone.
  my %quiet = map { $_ => 1 } qw(inline must_use doc allow expect warn deny forbid);
  # Whether the attribute that opens at `#` index `$i` of `@$t` is quiet, and
  # the index of its closing `]`.
  sub attribute {
    my ($t, $i) = @_;
    my ($depth, $end) = (0, $i + 1);
    for (; $end < @$t; $end++) {
      $depth++ if $t->[$end] eq "[";
      $depth-- if $t->[$end] eq "]";
      last if $depth == 0;
    }
    my $path = $t->[$i + 2] // "";
    return ($quiet{$path} ? 1 : 0, $end) unless $path eq "cfg_attr" and ($t->[$i + 3] // "") eq "(";
    # The attributes that the `cfg_attr` gives: each part past the first
    # comma at its own depth.
    my (@given, $part) = ();
    $depth = 0;
    for my $k ($i + 4 .. $end - 2) {
      my $token = $t->[$k];
      $depth++ if $token =~ /^[(\[{]$/;
      $depth-- if $token =~ /^[)\]}]$/;
      if ($depth == 0 and $token eq ",") { $part++; next; }
      push @given, $token if $part and $depth == 0 and $token =~ /^[A-Za-z_]/ and $t->[$k - 1] eq ",";
    }
    return ((@given and !grep { !$quiet{$_} } @given) ? 1 : 0, $end);
  }
  # The body of an item: its tokens with the visibility, the `use`
  # declarations, the quiet attributes, the module path before each name and
  # its own name `$name` set aside.
  sub body {
    my ($text, $name) = @_;
    my @t = tokens($text);
    my @out;
    for (my $i = 0; $i < @t; $i++) {
      my $token = $t[$i];
      if ($token eq "#" and ($t[$i + 1] // "") eq "[") {
        my ($quiet, $end) = attribute(\@t, $i);
        if ($quiet) { $i = $end; next; }
      }
      if ($token eq "pub") {
        if (($t[$i + 1] // "") eq "(") {
          my $depth = 0;
          for ($i++; $i < @t; $i++) {
            $depth++ if $t[$i] eq "(";
            $depth-- if $t[$i] eq ")";
            last if $depth == 0;
          }
        }
        next;
      }
      if ($token eq "use" and (!@out or $out[-1] =~ /^[;{}\]]$/)) {
        $i++ while $i < @t and $t[$i] ne ";";
        next;
      }
      if ($token =~ /^[A-Za-z_]/ and ($t[$i + 1] // "") eq ":" and ($t[$i + 2] // "") eq ":" and ($t[$i + 3] // "") =~ /^[A-Za-z_]/) {
        $i += 2;
        next;
      }
      push @out, $token eq $name ? "\x01" : $token;
    }
    return join " ", @out;
  }
  sub name_of {
    my ($id) = @_;
    $id =~ s/.*:://;
    $id =~ s/<.*//;
    return $id;
  }
  # How many trailing segments two paths share: of several items with one
  # body, the one whose path ends as the path of the item ends is its place.
  sub shared {
    my @a = split /::/, $_[0];
    my @b = split /::/, $_[1];
    my $n = 0;
    $n++ while $n < @a and $n < @b and $a[-1 - $n] eq $b[-1 - $n];
    return $n;
  }
  my (%added, @left);
  open my $list, "<", $items or die "acts.bash: $items: $!\n";
  while (my $line = <$list>) {
    chomp $line;
    my ($side, $kind, $test, $id, $file, $start, $end) = split /\t/, $line;
    my $text = text_of($side, $file);
    next unless defined $text;
    my @lines = split /\n/, $text, -1;
    next if $start < 1 or $end > @lines or $start > $end;
    my $name = name_of($id);
    my $key = join "\0", $kind, body(join("\n", @lines[$start - 1 .. $end - 1]), $name);
    if ($side eq "head") {
      push @{$added{"$test\0$key"}}, $id;
    } else {
      push @left, [$id, $name, $test, $key];
    }
  }
  close $list;
  for my $item (@left) {
    my ($id, $name, $test, $key) = @$item;
    my $candidates = $added{"$test\0$key"} // ($test eq "true" ? $added{"false\0$key"} : undef) or next;
    my ($at) = sort { shared($id, $b) <=> shared($id, $a) or $a cmp $b } @$candidates;
    print join("\t", $id, name_of($at) eq $name ? "moved" : "renamed", $at), "\n";
  }
' "$root" "$work/blobs" "$work/items" \
  | jq -R -s -c 'split("\n") | map(select(. != "") | split("\t") | {(.[0]): {act: .[1], at: .[2]}}) | add // {}'
