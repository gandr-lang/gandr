// The test runner of the shim. It calls the one entry through the exported C
// interface, as the Rust side does.
//
//   shim_test <file.mlir> <triple> object
//   shim_test <file.mlir> <triple> invalid-text <text of the diagnostic>
//   shim_test <file.mlir> <triple> unknown-target
//   shim_test <file.mlir> <triple> compile-error <text of the error>
//
// `object` asks for an ELF object. The other forms ask for the status, and
// for a diagnostic that holds the given text.

#include "gandr_mlir_shim.h"

#include <cstdio>
#include <cstring>
#include <fstream>
#include <iterator>
#include <string>

namespace {

const char *statusName(gandr_mlir_status status) {
  switch (status) {
  case GANDR_MLIR_OK:
    return "object";
  case GANDR_MLIR_INVALID_TEXT:
    return "invalid-text";
  case GANDR_MLIR_UNKNOWN_TARGET:
    return "unknown-target";
  case GANDR_MLIR_COMPILE_ERROR:
    return "compile-error";
  }
  return "unknown status";
}

} // namespace

int main(int argc, char **argv) {
  if (argc < 4) {
    std::fprintf(stderr, "usage: shim_test <file.mlir> <triple> <expect> [text]\n");
    return 2;
  }
  std::ifstream file(argv[1], std::ios::binary);
  if (!file) {
    std::fprintf(stderr, "shim_test: cannot read %s\n", argv[1]);
    return 2;
  }
  std::string text((std::istreambuf_iterator<char>(file)),
                   std::istreambuf_iterator<char>());
  std::string triple = argv[2];
  std::string expect = argv[3];

  gandr_mlir_output output = gandr_mlir_compile(
      text.data(), text.size(), triple.data(), triple.size());
  std::string bytes(reinterpret_cast<const char *>(output.bytes), output.len);
  gandr_mlir_status status = output.status;
  gandr_mlir_output_free(&output);

  if (expect != statusName(status)) {
    std::fprintf(stderr, "shim_test: expected %s, got %s:\n%s\n",
                 expect.c_str(), statusName(status),
                 status == GANDR_MLIR_OK ? "(object)" : bytes.c_str());
    return 1;
  }
  if (status == GANDR_MLIR_OK) {
    if (bytes.size() < 4 || std::memcmp(bytes.data(), "\x7f"
                                                      "ELF",
                                        4) != 0) {
      std::fprintf(stderr, "shim_test: the object is not ELF\n");
      return 1;
    }
    std::printf("shim_test: %s: object of %zu bytes\n", argv[1], bytes.size());
    return 0;
  }
  if (argc > 4 && bytes.find(argv[4]) == std::string::npos) {
    std::fprintf(stderr, "shim_test: the diagnostic has no \"%s\":\n%s\n",
                 argv[4], bytes.c_str());
    return 1;
  }
  std::printf("shim_test: %s: %s:\n%s\n", argv[1], expect.c_str(),
              bytes.c_str());
  return 0;
}
