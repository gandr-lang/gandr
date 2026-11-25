// A wrong text: the function returns i64, and its body returns an i32. The
// verifier refuses it before the shim translates anything.
llvm.func @wrong(%a: i32) -> i64 {
  llvm.return %a : i32
}
