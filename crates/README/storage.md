# The `storage` crates

The member rows of the `storage` category of [`crates/README.md`](../README.md#members): one row for each directory, the directory and what it is.

```text
# Rows sort lexicographically by directory; the dependency order is § Layering.
crates/
├── storage-artifact/              kernel artifacts on the record plane and canonical BLAKE3 certificate-step identities
├── storage-chunker/               content-defined chunk boundaries and their committed parameters
├── storage-records/               the authenticated ordered-record plane
├── storage-schema/                the record plane as C-sets with checked equations
├── storage-store/                 one store over both planes and named roots
└── storage-values/                the content-addressed value plane: typed chunk DAG and content pointers
```
