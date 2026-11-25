// The test runner of the read entry. It calls `gandr_mlir_read` through the
// exported C interface, as the Rust side does.
//
//   read_test <file.body> <file.facts> [name=type]...
//   read_test <file.body> invalid-text <text of the diagnostic> [name=type]...
//
// The first form asks for the facts, and compares them with the file byte for
// byte. The second form asks for the refusal, and for a diagnostic that holds
// the given text. Each `name=type` is one hole, in order.

#include "gandr_mlir_shim.h"

#include <cstdio>
#include <fstream>
#include <iterator>
#include <string>
#include <vector>

namespace {

bool readFile(const char *path, std::string &text) {
  std::ifstream file(path, std::ios::binary);
  if (!file)
    return false;
  text.assign(std::istreambuf_iterator<char>(file),
              std::istreambuf_iterator<char>());
  return true;
}

} // namespace

int main(int argc, char **argv) {
  if (argc < 3) {
    std::fprintf(stderr, "usage: read_test <file.body> <file.facts | "
                         "invalid-text text> [name=type]...\n");
    return 2;
  }
  std::string body;
  if (!readFile(argv[1], body)) {
    std::fprintf(stderr, "read_test: cannot read %s\n", argv[1]);
    return 2;
  }
  std::string expect = argv[2];
  bool refusal = expect == "invalid-text";
  int firstHole = refusal ? 4 : 3;
  if (refusal && argc < 4) {
    std::fprintf(stderr, "read_test: invalid-text needs a text\n");
    return 2;
  }

  // The names and the types stay alive in `specs` for the call.
  std::vector<std::string> specs(argv + firstHole, argv + argc);
  std::vector<gandr_mlir_hole> holes;
  for (const std::string &spec : specs) {
    size_t equals = spec.find('=');
    if (equals == std::string::npos) {
      std::fprintf(stderr, "read_test: a hole is name=type, not %s\n",
                   spec.c_str());
      return 2;
    }
    holes.push_back({spec.data(), equals, spec.data() + equals + 1,
                     spec.size() - equals - 1});
  }

  gandr_mlir_output output =
      gandr_mlir_read(body.data(), body.size(), holes.data(), holes.size());
  std::string bytes(reinterpret_cast<const char *>(output.bytes), output.len);
  gandr_mlir_status status = output.status;
  gandr_mlir_output_free(&output);

  if (refusal) {
    if (status != GANDR_MLIR_INVALID_TEXT) {
      std::fprintf(stderr, "read_test: expected invalid-text, got status %d:\n%s\n",
                   static_cast<int>(status), bytes.c_str());
      return 1;
    }
    if (bytes.find(argv[3]) == std::string::npos) {
      std::fprintf(stderr, "read_test: the diagnostics have no \"%s\":\n%s\n",
                   argv[3], bytes.c_str());
      return 1;
    }
    std::printf("read_test: %s: invalid-text:\n%s", argv[1], bytes.c_str());
    return 0;
  }
  if (status != GANDR_MLIR_OK) {
    std::fprintf(stderr, "read_test: expected the facts, got status %d:\n%s\n",
                 static_cast<int>(status), bytes.c_str());
    return 1;
  }
  std::string facts;
  if (!readFile(expect.c_str(), facts)) {
    std::fprintf(stderr, "read_test: cannot read %s\n", expect.c_str());
    return 2;
  }
  if (bytes != facts) {
    std::fprintf(stderr, "read_test: the facts differ. Expected:\n%sGot:\n%s",
                 facts.c_str(), bytes.c_str());
    return 1;
  }
  std::printf("read_test: %s: facts:\n%s", argv[1], bytes.c_str());
  return 0;
}
