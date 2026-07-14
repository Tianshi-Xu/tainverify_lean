#!/usr/bin/env python3
"""Bridge emitter target config.

Reads target directory + generated-data file names from env vars, with the
legacy gpt_ly4_regen defaults preserved for backward compatibility.

Env vars:
  BRIDGE_DENOTE_DIR : denote subdirectory, relative to trainverify/
                      Default: "denote/gpt_ly4_regen"
  BRIDGE_GEN_FILE   : generated-data lean file name (basename)
                      Default: "GeneratedData.lean"
  BRIDGE_MOD_PREFIX : Lean module prefix for imports
                      Default: computed from BRIDGE_DENOTE_DIR
                      e.g. "denote/gpt_ly4_regen" -> "denote.gpt_ly4_regen"

Usage in downstream modules:
    from target_config import DENOTE_DIR, GEN_FILE, MOD_PREFIX
"""
import os

DENOTE_DIR = os.environ.get("BRIDGE_DENOTE_DIR", "denote/gpt_ly4_regen")
GEN_FILE = os.environ.get("BRIDGE_GEN_FILE", "GeneratedData.lean")
MOD_PREFIX = os.environ.get(
    "BRIDGE_MOD_PREFIX",
    DENOTE_DIR.replace("/", ".").rstrip("."),
)
