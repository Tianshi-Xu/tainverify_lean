"""Worker #11 regen runner: drive OUR Verdict graph_to_lean.py (with the
params-aware FW_reshape fix) over the yoco_moe_a04b pkls.

Uses conda 'verdict' env python (has nnscaler, triton, dill, torch installed).
Points nnscaler_backend / verdict / graph_to_lean at /tmp/tv-intermediates/Verdict.
"""
import sys, os

OUR_VERDICT = "/tmp/tv-intermediates/Verdict"
WS = "/home/argustest/.openclaw/workspace"
IROHA = WS + "/iroha-tasks/trainverify-llm-train"

# stubs first (triton_shim + flash_attn shim), then our Verdict, then llm-train ops.
sys.path.insert(0, IROHA + "/stubs")
sys.path.insert(0, IROHA + "/nnscaler")  # nnscaler clone matching the pkl (has emit_self_getattr)
sys.path.insert(0, WS + "/llm-train")
sys.path.insert(0, WS + "/llm-train/llm")
sys.path.insert(0, OUR_VERDICT)

# --- triton stub driver (avoid GPU/benchmark) ---
import triton
from triton.runtime.driver import driver as drv_cfg


class _StubDriver:
    def get_benchmarker(self):
        return lambda *a, **kw: 0.0

    def get_current_target(self):
        class _T:
            backend = "cpu"
        return _T()

    def __getattr__(self, name):
        return lambda *a, **kw: None


try:
    drv_cfg.set_active(_StubDriver())
except Exception:
    try:
        type(drv_cfg).active = property(lambda self: _StubDriver())
    except Exception:
        pass


def _noop_autotune(*a, **kw):
    def d(fn):
        return fn
    return d


triton.autotune = _noop_autotune

sys.setrecursionlimit(200000)


# --- sequential Pool so build_graph takes the in-memory path ---
class _FakePool:
    def __init__(self, processes=None, initializer=None, initargs=()):
        if initializer is not None:
            initializer(*initargs)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False

    def map(self, fn, iterable):
        return [fn(x) for x in iterable]

    def close(self):
        pass

    def join(self):
        pass


import nnscaler_backend.build_graph as _bg
_bg.Pool = _FakePool

# --- torch version-skew shim: llm-train sets torch._dynamo.config attrs
# (e.g. recompile_limit) that don't exist on the installed torch 2.4/2.6.
# Auto-allow unknown config keys instead of raising AttributeError. ---
try:
    from torch.utils import _config_module as _cm

    _orig_setattr = _cm.ConfigModule.__setattr__

    def _lenient_setattr(self, name, value):
        try:
            _orig_setattr(self, name, value)
        except AttributeError:
            try:
                self._allowed_keys.add(name)
                self._config[name] = value
            except Exception:
                object.__setattr__(self, name, value)

    _cm.ConfigModule.__setattr__ = _lenient_setattr
except Exception as e:
    print("torch config shim skipped:", e)

# dill instead of pickle for load
try:
    import dill as _dill
    import nnscaler_backend.load_graph as _lg
    _lg.pickle = _dill
except Exception as e:
    print("dill patch skipped:", e)

import runpy

sys.argv = ["graph_to_lean.py"] + sys.argv[1:]
runpy.run_path(OUR_VERDICT + "/graph_to_lean.py", run_name="__main__")
