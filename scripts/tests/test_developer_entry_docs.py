"""Keep the developer entry navigable and its advertised CLI surface real."""

from dataclasses import dataclass
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tomllib
from urllib.parse import unquote, urlsplit

import pytest


ROOT = Path(__file__).resolve().parents[2]
DOCS = ("README.md", "AGENTS.md", "DEVELOPMENT.md", "docs/ARCHITECTURE.md")
LINK = re.compile(r"!?\[[^\]\n]*\]\(([^)\s]+)\)")


def local_links(path: Path) -> list[Path]:
    links = []
    for target in LINK.findall(path.read_text(encoding="utf-8")):
        url = urlsplit(target)
        if url.scheme or url.netloc:
            continue
        resolved = (path.parent / unquote(url.path)).resolve()
        assert resolved.is_relative_to(ROOT), f"{path.name}: nonportable link {target}"
        assert resolved.exists(), f"{path.name}: broken relative link {target}"
        if url.fragment:
            headings = re.findall(
                r"^#{1,6}\s+(.+?)\s*#*$", resolved.read_text(encoding="utf-8"), re.M
            )
            anchors = {
                re.sub(r"[^\w\- ]", "", heading.lower()).replace(" ", "-")
                for heading in headings
            }
            assert unquote(url.fragment) in anchors, f"{path.name}: missing anchor {target}"
        links.append(resolved)
    return links


@pytest.mark.parametrize("document", DOCS)
def test_relative_links_and_portable_paths(document):
    path = ROOT / document
    assert path.is_file(), f"missing developer entry: {document}"
    assert local_links(path), f"{document} must link to its context"
    assert not re.search(r"/(?:home|Users)/|[A-Z]:\\", path.read_text(encoding="utf-8"))


def test_landing_navigation():
    links = local_links(ROOT / "README.md")
    for target in (
        "DEVELOPMENT.md",
        "docs/ARCHITECTURE.md",
        "AGENTS.md",
        "docs/HANDOFF_2026-09-14.md",
        "docs/BRANCH_CONSOLIDATION_2026-09-14.md",
    ):
        assert ROOT / target in links, f"README needs a link to {target}"


def test_default_build_is_not_advertised_as_the_library():
    config = tomllib.loads((ROOT / "trainverify/lakefile.toml").read_text())
    assert config["defaultTargets"] == ["Trainverify"]
    assert "import Trainverify.Basic" in (ROOT / "trainverify/Trainverify.lean").read_text()
    assert 'def hello := "world"' in (ROOT / "trainverify/Trainverify/Basic.lean").read_text()
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    assert "`Trainverify`" in readme and "stub" in readme.lower()
    guide = (ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")
    for term in ("Basic", "hello", "lake build denote", "smoke", "release"):
        assert term in guide, f"development guide must distinguish {term}"
    workflow = (ROOT / ".github/workflows/lean_action_ci.yml").read_text()
    for target in (
        "denote.GraphGears",
        "denote.MultirefCertificate",
        "denote.yoco_goals.MultirefCertificateRegression",
    ):
        assert target in workflow and target in guide


def test_contribution_rules_do_not_restore_retired_shortcuts():
    rules = (ROOT / "AGENTS.md").read_text(encoding="utf-8")
    for obsolete in (
        "5-axiom baseline",
        "Lean.trustCompiler",
        "def op (data _cu ...) : Tensor := data",
        "git checkout HEAD --",
        "goal_N_stmt_with_labels",
    ):
        assert obsolete not in rules, f"retired contribution advice: {obsolete}"
    for term in ("authority", "dX", "dW", "rank", "shape", "native_decide"):
        assert term.casefold() in rules.casefold()


def test_historical_coverage_has_diagnostic_guidance():
    guide = (ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")
    section = re.search(
        r"^## Historical coverage diagnostic\n(.*?)(?=^## |\Z)",
        guide, re.M | re.S,
    )
    assert section, "separate historical coverage from clean-checkout verification"
    diagnostic = section.group(1)
    assert "count_yoco_faithful_coverage.py" in diagnostic
    for term in (
        "historical-only", "--historical --repo", "--inventory", "1154/1156",
        "ad821ce18494d30b5517a36260faa817fb45cda1", "HISTORICAL SOURCE-NAME CHECK",
        "source-only", "not proof coverage", "not kernel verification",
        "suppressed", "emitter discoveries", "not verified counterexamples",
    ):
        assert term in diagnostic
    assert "unexpected corpus size: 1096" not in diagnostic
    assert re.search(r"\b(?:fails?|rejects?)\b", diagnostic, re.I)
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    for term in ("historical-only", "--historical --repo", "--inventory", "source-only"):
        assert term in readme


@dataclass(frozen=True)
class HelpCase:
    module: str
    subcommand: str = ""
    flags: tuple[str, ...] = ()

    @property
    def arguments(self) -> tuple[str, ...]:
        return ("-m", self.module, *self.subcommand.split(), "--help")


HELP_CASES = (
    HelpCase("Verdict.main", flags=("--sm", "--pm", "--cache_dir", "--log_dir")),
    HelpCase("Verdict.graph_to_lean", flags=("--sm-pkl", "--pm-pkl", "--out", "--module",
                                          "--runtime-world-definitions-out")),
    HelpCase("trainverify.bridge_emitter.emit2", flags=("--whole-model", "--parallel-config",
                                                       "--targets", "--model-id", "--out")),
    HelpCase("trainverify.artifact_tools", flags=("verify-kernel", "check-lean", "render-joint")),
    HelpCase("trainverify.frontier_replay", flags=("--recipe", "--expected-commit", "--out")),
    HelpCase("trainverify.canonical_run", "run", ("--source-manifest", "--stages", "--out")),
    HelpCase("trainverify.canonical_run", "recheck", ("--command-sha256", "--observation-sha256")),
    HelpCase("trainverify.canonical_contract_prepare", flags=("--config", "--recipe-sha256", "--out")),
    HelpCase("trainverify.artifact_contracts", "render", ("--manifest", "--source-output")),
    HelpCase("trainverify.artifact_contracts", "check", ("--source", "--sha256", "--out-dir")),
    HelpCase("trainverify.artifact_contracts", "compare", ("--reference-stdout", "--candidate-stdout")),
    HelpCase("trainverify.scripts.count_yoco_faithful_coverage", flags=("--historical", "--inventory", "--repo")),
)


@pytest.mark.parametrize(
    "case", HELP_CASES, ids=lambda case: ".".join(filter(None, (case.module, case.subcommand)))
)
def test_real_cli_help(case, tmp_path):
    env = {
        **os.environ,
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONPATH": os.pathsep.join((str(ROOT), str(ROOT / "Verdict"))),
    }
    command = (sys.executable, *case.arguments)
    # Keep the complete subprocess evidence even when an assertion fails.
    with (tmp_path / "stdout.txt").open("wb") as stdout, (tmp_path / "stderr.txt").open("wb") as stderr:
        result = subprocess.run(
            command, cwd=ROOT, env=env, stdout=stdout, stderr=stderr,
            timeout=60, check=False,
        )
    (tmp_path / "exit.txt").write_text(f"{result.returncode}\n", encoding="ascii")
    output = (tmp_path / "stdout.txt").read_text(encoding="utf-8")
    errors = (tmp_path / "stderr.txt").read_text(encoding="utf-8")
    assert result.returncode == 0, f"{shlex.join(command)}\n{output}\n{errors}"
    assert "usage:" in output.lower()
    for flag in case.flags:
        assert flag in output, f"{case.module}: missing documented option {flag}"


def test_graph_inspection_role_and_private_commands():
    guide = (ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")
    architecture = (ROOT / "docs/ARCHITECTURE.md").read_text(encoding="utf-8")
    for term in ("Graph inspection", "--sm", "--pm", "--cache_dir", "--log_dir",
                 "fresh or empty", "pickle", "arbitrary code", "inspection.log",
                 "--max_ser_proc", "--no_cache_nodes", "exit 2", "exit 1"):
        assert term in guide
    assert '"$TV_PY" "$TV_ROOT/Verdict/main.py" --help' in guide
    assert "legacy default capture paths" not in architecture
    assert "graph inspection" in architecture
    assert "does not call" in architecture and "launch()" in architecture
    assert "RuntimeLineageBlocked" in architecture


def test_documented_help_commands_match_exercised_surface():
    guide = (ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")
    commands = [
        tuple(shlex.split(line)[1:])
        for line in guide.splitlines()
        if line.startswith('"$TV_PY" -m ') and line.endswith(" --help")
    ]
    assert commands == [case.arguments for case in HELP_CASES]
