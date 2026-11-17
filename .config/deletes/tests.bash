#!/usr/bin/env bash
# Prints each test of both sides whose lines differ, as a JSON array of
# `{id, name}`. `<items-base>` and `<items-head>` are the inventories of
# `check.bash`: `{id, kind, file, start, end, test}`, each file at its path
# in the tree (`paths.jq`). The text before is read from `<base>`, and the
# text after from the work tree. A file that the base does not hold stops the
# run with exit 2, since an empty text would read as a change (#6844). A test
# whose file is null comes from a source that a build script writes: git
# holds no text of it, so it is not compared.
#
# The pass starts a fixed count of processes, whatever the count of pairs
# (#7045): one `jq` gives each pair as one line, one `git cat-file --batch`
# reads each file of the base once, and one `perl` reads each file of the
# head once and compares each pair.
#
# Usage: tests.bash <base> <items-base> <items-head>
set -euo pipefail
base=${1:?tests.bash takes the base}
items_base=${2:?tests.bash takes the base inventory}
items_head=${3:?tests.bash takes the head inventory}
root=$(git rev-parse --show-toplevel)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-tests.XXXXXX")
trap 'rm -rf "$work"' EXIT
# Each test of both sides: the file, the start and the end at the base, the
# same three at the head, and the id, one a line.
jq -r -n --slurpfile b "$items_base" --slurpfile h "$items_head" '
  ($h[0] | map(select(.test)) | map({key: .id, value: .}) | from_entries) as $head
  | $b[0][] | select(.test) | . as $before | $head[.id] as $after
  | select($after != null and $before.file != null and $after.file != null)
  | [$before.file, $before.start, $before.end, $after.file, $after.start, $after.end, .id]
  | map(tostring) | join("\t")' > "$work/pairs"
awk -F '\t' -v base="$base" '!seen[$1]++ { print base ":" $1, $1 }' "$work/pairs" \
  | git cat-file --batch='%(objectname) %(objecttype) %(objectsize) %(rest)' > "$work/blobs"
perl -e '
  use strict;
  use warnings;
  my ($root, $base, $blobs, $pairs) = @ARGV;
  # The text of each file of the base, by its path.
  my %before;
  open my $in, "<:raw", $blobs or die "tests.bash: $blobs: $!\n";
  while (my $header = <$in>) {
    chomp $header;
    my ($object, $type, $size, $path) = split / /, $header, 4;
    next unless defined $path and $type eq "blob";
    read($in, my $text, $size) == $size or die "tests.bash: a short read of $path\n";
    $before{$path} = $text;
    <$in>;
  }
  close $in;
  # The text of each file of the head, read once. A file that the work tree
  # lacks reads as empty, so each of its tests reads as changed.
  my %after;
  sub after {
    my ($file) = @_;
    unless (exists $after{$file}) {
      $after{$file} = "";
      if (open my $f, "<:raw", "$root/$file") { local $/; $after{$file} = <$f> // ""; close $f; }
    }
    return $after{$file};
  }
  # The lines `$start` to `$end` of a text, as `sed -n` prints them, with
  # the trailing newlines cut, as a command substitution cuts them.
  my %lines;
  sub span {
    my ($key, $text, $start, $end) = @_;
    my $all = $lines{$key} //= [split /\n/, $text, -1];
    my $last = $end < @$all ? $end : scalar @$all;
    my $span = $start <= $last ? join("\n", @$all[$start - 1 .. $last - 1]) : "";
    $span =~ s/\n+\z//;
    return $span;
  }
  open my $list, "<", $pairs or die "tests.bash: $pairs: $!\n";
  while (my $line = <$list>) {
    chomp $line;
    my ($ofile, $ostart, $oend, $nfile, $nstart, $nend, $id) = split /\t/, $line, 7;
    unless (exists $before{$ofile}) {
      print STDERR "check:deletes: the base $base holds no $ofile, the file of a test\n";
      exit 2;
    }
    if (span("b:$ofile", $before{$ofile}, $ostart, $oend) ne span("h:$nfile", after($nfile), $nstart, $nend)) {
      (my $name = $id) =~ s/^.*:://;
      print "$id\t$name\n";
    }
  }
' "$root" "$base" "$work/blobs" "$work/pairs" \
  | jq -R -s -c 'split("\n") | map(select(. != "") | split("\t") | {id: .[0], name: .[1]})'
