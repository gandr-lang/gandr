# Whether a bounded run met a bound (#3855). `timeout` exits 124 at the
# wall-clock limit. The kernel kills a process at a scope's memory bound,
# which exits 137. Under `ulimit -v` an allocation fails instead, and the
# caller reads that off the run's errors as `out_of_memory`. A run past a
# bound is recorded `past bound` and never retried larger. `row.jq` reads
# Catt's runs and `stress.jq` gandr's.
#
# Input: {status: number, out_of_memory: boolean}.
def past_bound: .status == 124 or .status == 137 or .out_of_memory;
