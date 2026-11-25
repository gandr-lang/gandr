// One function in the `llvm` dialect: the shim gives an object.
llvm.func @add(%a: i32, %b: i32) -> i32 {
  %sum = llvm.add %a, %b : i32
  llvm.return %sum : i32
}
