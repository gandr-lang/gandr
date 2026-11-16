// Stop kache's daemon at the end of the job. The daemon sends its queued
// uploads to the remote before it exits, and the command waits up to 35 s.
// The job's own wrapper is the command, so the daemon gets the setting that
// the job built with.
const { existsSync } = require("node:fs");
const { spawnSync } = require("node:child_process");

const wrapper = `${process.env.RUNNER_TEMP}/kache-wrapper`;
if (existsSync(wrapper)) {
  const stop = spawnSync(wrapper, ["daemon", "stop"], { stdio: "inherit" });
  if (stop.error) {
    console.log(`kache drain: ${stop.error.message}`);
  }
}
