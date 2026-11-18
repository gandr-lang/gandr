#!/usr/bin/env bash
# Writes the compiler wrapper of one job and prints its path. `setup-rust`
# runs it, and `check:kache-wrapper` runs it for two jobs at one time.
#
# The wrapper gives kache its configuration and the token, and nothing else
# in the job sees them. Where the job has no kache, as in an image built
# before the pin, the wrapper runs the compiler itself.
#
# Each job has a runtime directory of its own. A root container job keeps its
# socket, locks and state inside the CI image. Other jobs keep them under
# `RUNNER_TEMP`. Two runners of one account resolve one default runtime
# directory. Without a directory for each job, they share one daemon, and the
# job that ends first stops it under the other job's compiles.
#
# The cache directory stays shared by the jobs of a host.
# - see: #7828
#
# A trusted run publishes: a merge group, or a push, a schedule or a dispatch
# on `main`, `landing` or `integration`. Under GitHub Actions, kache publishes
# only from a push to a protected branch, and our pushes compile almost
# nothing. So in a trusted run the wrapper gives kache alone
# `GITHUB_ACTIONS=false`. A pull request's run reads the cache and publishes
# nothing.
#
# The wrapper is a bash script. dash, the `sh` of the CI image, drops each
# variable whose name is no shell name, such as `CARGO_BIN_EXE_host-tools`.
# A test that reads such a variable then fails to compile.
#
#   RUNNER_TEMP=<dir> KACHE_TRUSTED=<true|false> KACHE_USER=<login> \
#     KACHE_TOKEN=<token> kache-wrapper.bash
set -euo pipefail
state=${RUNNER_TEMP:?}
if [[ $(id -u) == 0 ]]; then
  state=/opt/ci/kache/${GITHUB_RUN_ID:?}/${GITHUB_JOB:?}
  install -d -m 700 -o ci -g ci "$state"
fi
config=$state/kache.toml
token=$state/kache-token
wrapper=$state/kache-wrapper
runtime=$state/kache-runtime
printf '[cache]\ncache_executables = true\nruntime_dir = "%s"\n\n[cache.remote]\ntype = "oci"\nrepository = "ghcr.io/gandr-lang/gandr-kache"\nprefix = "gandr"\n' "$runtime" > "$config"
(umask 077 && printf '%s' "${KACHE_TOKEN:?}" > "$token")
trusted=
if [[ ${KACHE_TRUSTED:-} == true ]]; then trusted='export GITHUB_ACTIONS=false'; fi
cat > "$wrapper" << EOF
#!/usr/bin/env bash
command -v kache > /dev/null 2>&1 || exec "\$@"
export KACHE_CONFIG='$config' KACHE_OCI_USERNAME='${KACHE_USER:?}'
KACHE_OCI_PASSWORD=\$(cat '$token'); export KACHE_OCI_PASSWORD
$trusted
if [[ \$(id -u) == 0 ]]; then
  exec runuser --user ci --preserve-environment -- env HOME=/opt/ci XDG_CACHE_HOME=/opt/ci/.cache KACHE_CACHE_DIR='$state/cache' kache "\$@"
fi
exec kache "\$@"
EOF
chmod +x "$wrapper"
if [[ $(id -u) == 0 ]]; then chown ci:ci "$config" "$token" "$wrapper"; fi
printf '%s\n' "$wrapper"
