# The service that keeps a `mise` task running on a host (#4167): a
# `systemd --user` unit on Linux, a `launchd` agent on macOS. Either runs
# `mise run <task>` from the checkout that installed it, under the installing
# shell's `PATH` and the variables `service.bash` carries with it, and starts
# it again 20 seconds after any exit, so a task killed by hand or by a
# relaunch runs again within a minute. `service.bash` writes it under the XDG
# configuration directory or `~/Library/LaunchAgents/`, never the tree.
#
# Input: `{os, dir, mise, path, environment, name, task, description}`:
# `linux` or `macos`, the checkout, the `mise` executable, the `PATH` the
# service runs under, the other variables it runs under by name (git's
# configuration, #4866), the service's name (`gandr-<name>` or
# `gandr.<name>`), the task it runs and the unit's description.
# Output: the unit's or the agent's text.

. as $in
| def xml: gsub("&"; "&amp;") | gsub("<"; "&lt;") | gsub(">"; "&gt;");
  ([["PATH", $in.path]] + [($in.environment // {}) | to_entries[] | [.key, .value]]) as $variables
  | if $in.os == "linux" then
    [ "[Unit]",
      "Description=\($in.description)",
      "",
      "[Service]",
      "WorkingDirectory=\($in.dir)"
    ]
    + [$variables[] | "Environment=\(.[0])=\(.[1])"]
    + [ "ExecStart=\($in.mise) run \($in.task)",
      "Restart=always",
      "RestartSec=20",
      "",
      "[Install]",
      "WantedBy=default.target"
    ] | join("\n")
  elif $in.os == "macos" then
    [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>",
      "<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">",
      "<plist version=\"1.0\">",
      "<dict>",
      "  <key>Label</key><string>gandr.\($in.name | xml)</string>",
      "  <key>WorkingDirectory</key><string>\($in.dir | xml)</string>",
      "  <key>EnvironmentVariables</key><dict>\([$variables[] | "<key>\(.[0] | xml)</key><string>\(.[1] | xml)</string>"] | join(""))</dict>",
      "  <key>ProgramArguments</key><array><string>\($in.mise | xml)</string><string>run</string><string>\($in.task | xml)</string></array>",
      "  <key>KeepAlive</key><true/>",
      "  <key>ThrottleInterval</key><integer>20</integer>",
      "</dict>",
      "</plist>"
    ] | join("\n")
  else
    error("\($in.task) --install knows Linux and macOS, not \($in.os)")
  end
