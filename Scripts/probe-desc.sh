#!/usr/bin/env bash
set -euo pipefail
lake build GARCD
lake env lean Research/DESC_Open_Probe.lean
