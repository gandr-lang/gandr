#!/usr/bin/env bash
# The scope script of the cases of `gate verdict read`. It names the base
# that it reads, so a key against one base is no key against another.
printf -- '--workspace --exclude base-%s\n' "${GATE_BASE:0:7}"
