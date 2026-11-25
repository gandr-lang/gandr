// A return with no value from a function whose result is a word.
llvm.func tailcc @narrow() -> i8 {
  gandr.return
}
