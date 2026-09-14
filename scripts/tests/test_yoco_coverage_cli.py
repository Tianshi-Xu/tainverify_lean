"""Source accounting only: these checks never run Lean or model capture."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "trainverify/scripts/count_yoco_faithful_coverage.py"
PIN = "ad821ce18494d30b5517a36260faa817fb45cda1"


def cli(*args, cwd=ROOT):
    return subprocess.run(
        [sys.executable, str(SCRIPT), *map(str, args)], cwd=cwd,
        capture_output=True, text=True, timeout=120, check=False,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )


def load_cli():
    spec = importlib.util.spec_from_file_location("yoco_coverage", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_default_rejects_without_current_ratio(tmp_path):
    result = cli(cwd=tmp_path)
    assert result.returncode != 0
    assert not result.stdout
    assert "historical-only" in result.stderr
    assert "--historical --repo" in result.stderr
    assert "--inventory" in result.stderr
    assert "%" not in result.stderr and "1096" not in result.stderr


def test_help_is_safe_without_sources(tmp_path):
    result = cli("--help", cwd=tmp_path)
    assert result.returncode == 0, result.stderr
    assert "usage:" in result.stdout
    for flag in ("--historical", "--repo", "--inventory"):
        assert flag in result.stdout


def test_import_has_no_source_reads(monkeypatch, capsys):
    def forbidden(*args, **kwargs):
        pytest.fail("import must not read sources or call Git")
    monkeypatch.setattr(Path, "read_text", forbidden)
    monkeypatch.setattr(subprocess, "run", forbidden)
    assert callable(load_cli().main)
    assert capsys.readouterr() == ("", "")


def test_current_inventory_exact_sets(tmp_path):
    source = ROOT / "trainverify/denote/GeneratedYOCOMoE.lean"
    # Independent literal-line accounting, not the production regex scanner.
    ordinary, zigzag, top, nonordinary, top_nonordinary = (set() for _ in range(5))
    for line in source.read_text().splitlines():
        if line.startswith("def "):
            words = line.split()
            name = words[1]
            if words[3] == "LineageGoal" and name.startswith(("intermediateGoal_", "goal_")):
                (ordinary if name.startswith("intermediateGoal_") else top).add(name)
            elif name.startswith("intermediateGoal_") and name.endswith("_zigzag"):
                zigzag.add(name.removesuffix("_zigzag"))
        elif line.startswith("-- NOT an ordinary gather: "):
            name = line.split()[5]
            (nonordinary if name.startswith("intermediateGoal_") else top_nonordinary).add(name)
    expected = {
        "ordinary_intermediate": ordinary,
        "emitted_zigzag": zigzag,
        "ordinary_top": top,
        "nonordinary_top_discoveries": top_nonordinary,
        "suppressed_nonordinary_intermediate_discoveries": nonordinary - zigzag,
    }
    result = cli("--inventory", ROOT / "trainverify", cwd=tmp_path)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report["scope"] == "source-only; not proof coverage; not kernel verification"
    assert report["source"] == str(source)
    assert "emitter discoveries, not verified counterexamples" in report["limitations"]
    assert set(report["categories"]) == set(expected)
    for category, ids in expected.items():
        assert report["categories"][category] == {"count": len(ids), "ids": sorted(ids)}
    assert [len(ids) for ids in expected.values()] == [646, 445, 5, 0, 60]
    assert report["total_discoveries"] == sum(map(len, expected.values())) == 1156
    assert not any(word in result.stdout.lower() for word in ('%', '"accepted"', '"proved"', 'retired'))
    assert cli("--inventory", ROOT / "trainverify").stdout == result.stdout
    assert cli("--inventory", cwd=tmp_path).stdout == result.stdout


ORDINARY = "def intermediateGoal_1 : LineageGoal :=\n  {}\n"
DISCOVERY = "-- NOT an ordinary gather: intermediateGoal_2 (ts = 2).\n"
ZIGZAG = "def intermediateGoal_2_zigzag : TrainVerify.Denote.GeneratedPatterns.ZigzagLineageGoal :=\n  {}\n"
TOP = "def goal_1 : LineageGoal :=\n  {}\n"
TOP_DISCOVERY = "-- NOT an ordinary gather: goal_2 (ts = 42).\n"


def fixture_root(tmp_path, text):
    source = tmp_path / "denote/GeneratedYOCOMoE.lean"
    source.parent.mkdir()
    source.write_text(text)
    return tmp_path


def test_inventory_classifies_small_emitter_fixture(tmp_path):
    result = cli("--inventory", fixture_root(tmp_path, ORDINARY + DISCOVERY + ZIGZAG + TOP + TOP_DISCOVERY
                 + "-- NOT an ordinary gather: intermediateGoal_3 (ts = 3).\n"))
    assert result.returncode == 0, result.stderr
    categories = json.loads(result.stdout)["categories"]
    assert {key: value["ids"] for key, value in categories.items()} == {
        "ordinary_intermediate": ["intermediateGoal_1"],
        "emitted_zigzag": ["intermediateGoal_2"],
        "ordinary_top": ["goal_1"],
        "nonordinary_top_discoveries": ["goal_2"],
        "suppressed_nonordinary_intermediate_discoveries": ["intermediateGoal_3"],
    }


@pytest.mark.parametrize("text", [
    ORDINARY * 2,
    DISCOVERY * 2,
    DISCOVERY + ZIGZAG * 2,
    ORDINARY + DISCOVERY.replace("_2", "_1").replace("= 2", "= 1"),
    ORDINARY + DISCOVERY + ZIGZAG + ORDINARY.replace("_1", "_2"),
    TOP + TOP_DISCOVERY.replace("goal_2", "goal_1"),
    ORDINARY + ZIGZAG,
    ORDINARY + DISCOVERY.replace("= 2", "= 99"),
    ORDINARY + "def intermediateGoal_3 : UnknownGoal := {}\n",
    ORDINARY + "-- NOT an ordinary gather: intermediateGoal_bad (ts = 3).\n",
    "this is not generated source\n",
], ids=["duplicate-ordinary", "duplicate-discovery", "duplicate-zigzag", "ordinary-discovery-overlap",
        "ordinary-zigzag-overlap", "top-overlap", "zigzag-without-discovery", "tid-mismatch",
        "unknown-target-type", "malformed-discovery", "no-targets"])
def test_inventory_rejects_lossy_classifications(tmp_path, text):
    result = cli("--inventory", fixture_root(tmp_path, text))
    assert result.returncode != 0
    assert not result.stdout
    assert "invalid generated source" in result.stderr
    assert "Traceback" not in result.stderr


def test_inventory_missing_source(tmp_path):
    result = cli("--inventory", tmp_path)
    assert result.returncode != 0 and not result.stdout
    assert str(tmp_path / "denote/GeneratedYOCOMoE.lean") in result.stderr
    assert "cannot read inventory source" in result.stderr


def historical_repo():
    # An archive-only runner must explicitly supply the real local object store.
    # Missing prerequisites FAIL, never skip or substitute a synthetic checkpoint.
    return Path(os.environ.get("YOCO_HISTORICAL_REPO", str(ROOT)))


def test_authentic_pinned_historical_cli(tmp_path):
    result = cli("--historical", "--repo", historical_repo(), cwd=tmp_path)
    assert result.returncode == 0, result.stderr
    assert not result.stderr
    for text in ("HISTORICAL SOURCE-NAME CHECK", PIN, "ordinary: 649/649", "zigzag: 505/505",
                 "source-name matches: 1154/1156", "not fresh Lean acceptance", "goal_3", "goal_4"):
        assert text in result.stdout
    assert "proof coverage" not in result.stdout or "not proof coverage" in result.stdout


def test_historical_never_reads_worktree(monkeypatch, capsys, tmp_path):
    module = load_cli()
    real_run = subprocess.run
    calls = []

    def guarded_run(command, **kwargs):
        assert isinstance(command, list) and command[0] == "git"
        assert not kwargs.get("shell") and 0 < kwargs["timeout"] <= 30
        assert kwargs["env"]["GIT_NO_REPLACE_OBJECTS"] == "1"
        assert kwargs["env"]["GIT_NO_LAZY_FETCH"] == "1"
        assert kwargs["env"]["GIT_TERMINAL_PROMPT"] == "0"
        assert kwargs["env"]["GIT_ALLOW_PROTOCOL"] == ""
        assert "GIT_DIR" not in kwargs["env"]
        assert PIN in " ".join(command)
        assert "ls-tree" in command or "show" in command
        calls.append(command)
        return real_run(command, **kwargs)

    def forbidden(*args, **kwargs):
        pytest.fail("historical mode attempted a worktree read")

    repo = historical_repo()
    monkeypatch.setenv("GIT_DIR", str(tmp_path / "wrong-git-dir"))
    monkeypatch.setattr(subprocess, "run", guarded_run)
    monkeypatch.setattr(Path, "read_text", forbidden)
    monkeypatch.setattr(Path, "read_bytes", forbidden)
    monkeypatch.setattr(Path, "glob", forbidden)
    assert module.main(["--historical", "--repo", str(repo)]) == 0
    assert "source-name matches: 1154/1156" in capsys.readouterr().out
    assert calls and "ls-tree" in calls[0]
    shows = [command[-1].split(":", 1)[1] for command in calls if "show" in command]
    assert "trainverify/denote/GeneratedYOCOMoE.lean" in shows
    assert all(p == "trainverify/denote/GeneratedYOCOMoE.lean" or
               (Path(p).parent.as_posix() == "trainverify/denote/yoco_goals" and p.endswith(".lean"))
               for p in shows)


@pytest.mark.parametrize("kind", ["missing-directory", "not-git", "missing-commit"])
def test_historical_unavailable_rejects(tmp_path, kind):
    repo = tmp_path / "repo"
    if kind != "missing-directory":
        repo.mkdir()
        if kind == "missing-commit":
            subprocess.run(["git", "init", "--quiet", str(repo)], check=True, timeout=10)
        fixture_root(repo, ORDINARY)
    result = cli("--historical", "--repo", repo)
    assert result.returncode != 0 and not result.stdout
    assert PIN in result.stderr and "--repo" in result.stderr
    assert "historical blobs unavailable" in result.stderr
    assert "Traceback" not in result.stderr


@pytest.mark.parametrize("args", [
    ["--historical"], ["--historical", "--repo", ".", "live-root"],
    ["--historical", "--repo", ".", "--commit", "HEAD"],
    ["--inventory", "--repo", "."], ["--historical", "--inventory"],
], ids=["repo-required", "no-live-root", "no-commit-override", "no-inventory-repo", "exclusive-modes"])
def test_mode_argument_errors(args):
    result = cli(*args)
    assert result.returncode == 2 and not result.stdout
    assert "error:" in result.stderr and "Traceback" not in result.stderr


def test_historical_original_exact_names_and_failures():
    module = load_cli()
    assert module.HISTORICAL_COMMIT == PIN
    assert (module.HISTORICAL_TOTAL, module.HISTORICAL_NAMES) == (1156, 1154)
    # Isolated scanner negative controls, NOT a substitute historical acceptance run.
    with pytest.raises(ValueError, match="unexpected corpus size: 1"):
        module.historical_name_report(ORDINARY, "theorem recon_intermediateGoal_1_faithful : True := by trivial")
    generated = "".join(f"def intermediateGoal_{n} : LineageGoal :=\n" for n in range(1154))
    generated += "-- NOT an ordinary gather: goal_3 (ts = 42).\n-- NOT an ordinary gather: goal_4 (ts = 43).\n"
    # Helpers, restatements, ringAttn and cut suffixes must not inflate the numerator.
    proofs = "\n".join(f"theorem recon_intermediateGoal_{n}_faithful_extra : True := by trivial" for n in range(1154))
    with pytest.raises(ValueError, match="coverage changed: 0"):
        module.historical_name_report(generated, proofs)


def test_historical_scan_failure_keeps_nonzero_exit(monkeypatch, capsys):
    module = load_cli()
    # Only the failure path is isolated. Authentic success is tested above.
    monkeypatch.setattr(module, "historical_sources", lambda repo: (ORDINARY, ""))
    assert module.main(["--historical", "--repo", "unused-negative-control"]) == 1
    output = capsys.readouterr()
    assert not output.out and "unexpected corpus size: 1" in output.err


@pytest.mark.parametrize("failure", [FileNotFoundError("git unavailable"), subprocess.TimeoutExpired("git", 30)],
                         ids=["git-unavailable", "git-timeout"])
def test_historical_git_failures_are_actionable(monkeypatch, capsys, failure):
    module = load_cli()
    def fail(*args, **kwargs):
        raise failure
    monkeypatch.setattr(subprocess, "run", fail)
    assert module.main(["--historical", "--repo", "unused-negative-control"]) == 1
    output = capsys.readouterr()
    assert not output.out
    assert "historical blobs unavailable" in output.err and PIN in output.err
    assert "--repo" in output.err and "Traceback" not in output.err
