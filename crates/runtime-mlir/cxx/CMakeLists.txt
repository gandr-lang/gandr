cmake_minimum_required(VERSION 3.31)

# The shim of gandr over MLIR: one shared library with the C interface of
# `include/gandr_mlir_shim.h`. The build script of the crate builds it under
# the feature `full`, with the toolchain of the pin that
# `GANDR_MLIR_TOOLCHAIN` names. Without the feature nothing builds it.
#
# The archives of the toolchain hold ThinLTO bitcode, so the link of the
# library runs LTO through mold and the LTO plugin of the environment. The
# library then holds native code only.

project(gandr-mlir-shim LANGUAGES CXX)

set(CMAKE_LINKER_TYPE MOLD)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(MLIR REQUIRED CONFIG NO_DEFAULT_PATH PATHS "${MLIR_DIR}")
if(NOT LLVM_PACKAGE_VERSION VERSION_EQUAL "${GANDR_MLIR_VERSION}")
  message(FATAL_ERROR
    "gandr-mlir-shim: the pin is LLVM ${GANDR_MLIR_VERSION}, the toolchain is ${LLVM_PACKAGE_VERSION}")
endif()

llvm_map_components_to_libnames(llvm_target_libs
  AllTargetsAsmParsers AllTargetsCodeGens AllTargetsDescs AllTargetsInfos)

# The `gandr` dialect: `src/gandr.td` gives the operations, and `mlir-tblgen`
# of the pin writes their C++ into the build directory.
list(APPEND CMAKE_MODULE_PATH "${MLIR_CMAKE_DIR}" "${LLVM_CMAKE_DIR}")
include(TableGen)
include(AddLLVM)
include(AddMLIR)
include_directories(${LLVM_INCLUDE_DIRS} ${MLIR_INCLUDE_DIRS})
set(LLVM_TARGET_DEFINITIONS src/gandr.td)
mlir_tablegen(GandrOps.h.inc -gen-op-decls)
mlir_tablegen(GandrOps.cpp.inc -gen-op-defs)
mlir_tablegen(GandrDialect.h.inc -gen-dialect-decls -dialect=gandr)
mlir_tablegen(GandrDialect.cpp.inc -gen-dialect-defs -dialect=gandr)
add_public_tablegen_target(GandrIncGen)

add_library(gandr_mlir_shim SHARED src/shim.cpp src/dialect.cpp src/read.cpp)
add_dependencies(gandr_mlir_shim GandrIncGen)
target_include_directories(gandr_mlir_shim PUBLIC
  "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
  "$<INSTALL_INTERFACE:include>")
target_include_directories(gandr_mlir_shim PRIVATE
  "${CMAKE_CURRENT_SOURCE_DIR}/src" "${CMAKE_CURRENT_BINARY_DIR}")
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(gandr_mlir_shim PRIVATE -fno-rtti)
endif()
target_link_options(gandr_mlir_shim PRIVATE
  -flto=thin
  "-Wl,--version-script=${CMAKE_CURRENT_SOURCE_DIR}/exports.map"
  -Wl,--no-undefined)
set_target_properties(gandr_mlir_shim PROPERTIES
  LINK_DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/exports.map")
# The imported targets carry their own include directories, by the patch
# `01-export-install-include-directories` of the recipe.
target_link_libraries(gandr_mlir_shim PRIVATE
  MLIRBuiltinToLLVMIRTranslation
  MLIRLLVMDialect
  MLIRLLVMToLLVMIRTranslation
  MLIRParser
  MLIRTargetLLVMIRExport
  MLIRTransformUtils
  ${llvm_target_libs})

install(TARGETS gandr_mlir_shim LIBRARY DESTINATION lib)
install(FILES include/gandr_mlir_shim.h DESTINATION include)

# The tests call the library through its C interface.
enable_testing()
add_executable(shim_test tests/shim_test.cpp)
target_link_libraries(shim_test PRIVATE gandr_mlir_shim)

function(shim_test name file triple)
  add_test(NAME ${name}
    COMMAND shim_test "${CMAKE_CURRENT_SOURCE_DIR}/tests/${file}" "${triple}" ${ARGN})
endfunction()

set(x86_64 x86_64-unknown-linux-gnu)
# A function in the `llvm` dialect gives an object, for each backend of the pin.
shim_test(object-x86_64 add.mlir ${x86_64} object)
shim_test(object-aarch64 add.mlir aarch64-unknown-linux-gnu object)
shim_test(object-riscv64 add.mlir riscv64-unknown-linux-gnu object)
# A wrong text gives the error of the verifier.
shim_test(verifier-refuses wrong-return.mlir ${x86_64} invalid-text
  "'llvm.return' op mismatching result types")
shim_test(unknown-target add.mlir nonsense-unknown-none unknown-target)
# One test for each operation that the end of the minimal core needs.
shim_test(operation-integers integers.mlir ${x86_64} object)
shim_test(operation-load-store memory.mlir ${x86_64} object)
shim_test(operation-atomic atomic.mlir ${x86_64} object)
shim_test(operation-inline-asm inline-asm.mlir ${x86_64} object)
# The conventions of a transition.
shim_test(convention-tailcc-x86_64 tail-call.mlir ${x86_64} object)
# The RISC-V backend of the pin has no `tailcc`: the code generator gives a
# fatal error. The shim turns it into the status of a compile error, and the
# process continues.
shim_test(convention-tailcc-riscv64-refused tail-call.mlir riscv64-unknown-linux-gnu
  compile-error "Unsupported calling convention")
shim_test(convention-preserve-none preserve-none.mlir ${x86_64} invalid-text
  "preserve_nonecc")
# The `gandr` dialect: the verifier accepts each transition of the slice, and
# the lowering leaves no `gandr` operation, so the translation gives an object.
shim_test(dialect-transitions transitions.mlir ${x86_64} object)
shim_test(dialect-return-wrong-type return-wrong-type.mlir ${x86_64} invalid-text
  "'gandr.return' op returns 'i16' from a function of 'i8'")
shim_test(dialect-return-no-value return-no-value.mlir ${x86_64} invalid-text
  "'gandr.return' op returns '!llvm.void' from a function of 'i8'")
shim_test(dialect-call-wrong-operand call-wrong-operand.mlir ${x86_64} invalid-text
  "'gandr.call' op gives operand 0 of type 'i16' to @inc, which takes 'i8'")
shim_test(dialect-jump-wrong-result jump-wrong-result.mlir ${x86_64} invalid-text
  "'gandr.jump' op jumps to @wide of 'i16' from a function of 'i8'")

# The read entry: a body and the type of each hole go in, the facts of each
# operation come out. Each test compares the facts with a file.
add_executable(read_test tests/read_test.cpp)
target_link_libraries(read_test PRIVATE gandr_mlir_shim)

function(read_test name body expect)
  add_test(NAME ${name}
    COMMAND read_test "${CMAKE_CURRENT_SOURCE_DIR}/tests/read/${body}" ${expect} ${ARGN})
endfunction()

set(read "${CMAKE_CURRENT_SOURCE_DIR}/tests/read")
read_test(read-load load.body "${read}/load.facts" address=i64)
read_test(read-store store.body "${read}/store.facts" address=i64 word=i64)
read_test(read-atomic-load atomic-load.body "${read}/atomic-load.facts" address=i64)
read_test(read-inline-asm inline-asm.body "${read}/inline-asm.facts" number=i64 a=i64)
# The verifier refuses an atomic load with no alignment, at line 2, column 9
# of the body.
read_test(read-verifier-refuses atomic-no-alignment.body invalid-text
  "2:9: error: 'llvm.load' op expected alignment for atomic access"
  address=i64)
