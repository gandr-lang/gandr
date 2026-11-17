// Stop kache's daemon at the end of the job. The daemon sends its queued
// uploads to the remote before it exits, and the command waits up to 35 s.
// The job's own wrapper is the command, so the daemon gets the setting that
// the job built with.
//
// This step runs outside `mise run`, so mise's tools are not on its PATH.
// `mise which` finds the kache that the job's tasks ran, and installs
// nothing. The step first writes kache's summary to the log: the hit rate,
// the time saved and the state of the remote.
// - see: #7789
const { existsSync } = require("node:fs");
const { delimiter, dirname } = require("node:path");
const { spawnSync } = require("node:child_process");

const wrapper = `${process.env.RUNNER_TEMP}/kache-wrapper`;
const which = spawnSync("mise", ["which", "kache"], { encoding: "utf8" });
const kache = which.status === 0 ? which.stdout.trim() : "";
if (!existsSync(wrapper) || kache === "") {
  console.log("kache drain: this job has no kache");
} else {
  const env = { ...process.env, PATH: `${dirname(kache)}${delimiter}${process.env.PATH}` };
  for (const args of [["stats", "--since", "6h"], ["daemon", "stop"]]) {
    const run = spawnSync(wrapper, args, { stdio: "inherit", env });
    if (run.error) {
      console.log(`kache drain: kache ${args.join(" ")}: ${run.error.message}`);
    }
  }
}
