# The service that keeps `stall:watch` running (#4167): a `systemd --user`
# unit on Linux, a `launchd` agent on macOS. Either runs `mise run
# stall:watch` from the checkout that installed it, under the installing
# shell's `PATH`, and starts it again 20 seconds after any exit, so a
# detector killed by hand or by a relaunch reads again within a minute.
# `stall:watch --install` writes it under the XDG configuration directory or
# `~/Library/LaunchAgents/`, never the tree.
#
# Input: `{os, dir, mise, path}`: `linux` or `macos`, the checkout, the
# `mise` executable and the `PATH` the service runs under.
# Output: the unit's or the agent's text.

. as $in
| def xml: gsub("&"; "&amp;") | gsub("<"; "&lt;") | gsub(">"; "&gt;");
  if $in.os == "linux" then
    [ "[Unit]",
      "Description=gandr stall detector (stall:watch)",
      "",
      "[Service]",
      "WorkingDirectory=\($in.dir)",
      "Environment=PATH=\($in.path)",
      "ExecStart=\($in.mise) run stall:watch",
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
      "  <key>Label</key><string>gandr.stall-watch</string>",
      "  <key>WorkingDirectory</key><string>\($in.dir | xml)</string>",
      "  <key>EnvironmentVariables</key><dict><key>PATH</key><string>\($in.path | xml)</string></dict>",
      "  <key>ProgramArguments</key><array><string>\($in.mise | xml)</string><string>run</string><string>stall:watch</string></array>",
      "  <key>KeepAlive</key><true/>",
      "  <key>ThrottleInterval</key><integer>20</integer>",
      "</dict>",
      "</plist>"
    ] | join("\n")
  else
    error("stall:watch --install knows Linux and macOS, not \($in.os)")
  end
