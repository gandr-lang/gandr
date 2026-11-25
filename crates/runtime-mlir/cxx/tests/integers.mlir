// The integer operations of the words of 8, 16, 32 and 64 bits: arithmetic,
// bits, shifts, comparison, selection, and the casts between widths.
llvm.func @words(%a8: i8, %b8: i8, %a16: i16, %b16: i16,
                 %a32: i32, %b32: i32, %a64: i64, %b64: i64) -> i64 {
  %add8 = llvm.add %a8, %b8 : i8
  %sub16 = llvm.sub %a16, %b16 : i16
  %mul32 = llvm.mul %a32, %b32 : i32
  %udiv64 = llvm.udiv %a64, %b64 : i64
  %sdiv64 = llvm.sdiv %a64, %b64 : i64
  %urem32 = llvm.urem %a32, %b32 : i32
  %srem32 = llvm.srem %a32, %b32 : i32
  %and = llvm.and %udiv64, %sdiv64 : i64
  %or = llvm.or %and, %a64 : i64
  %xor = llvm.xor %or, %b64 : i64
  %shl = llvm.shl %xor, %a64 : i64
  %lshr = llvm.lshr %shl, %b64 : i64
  %ashr = llvm.ashr %lshr, %a64 : i64
  %lt = llvm.icmp "ult" %a32, %b32 : i32
  %pick = llvm.select %lt, %urem32, %srem32 : i1, i32
  %wide8 = llvm.zext %add8 : i8 to i64
  %wide16 = llvm.sext %sub16 : i16 to i64
  %wide32 = llvm.zext %mul32 : i32 to i64
  %wide = llvm.zext %pick : i32 to i64
  %narrow = llvm.trunc %ashr : i64 to i32
  %back = llvm.sext %narrow : i32 to i64
  %s1 = llvm.add %wide8, %wide16 : i64
  %s2 = llvm.add %s1, %wide32 : i64
  %s3 = llvm.add %s2, %wide : i64
  %s4 = llvm.add %s3, %back : i64
  llvm.return %s4 : i64
}
