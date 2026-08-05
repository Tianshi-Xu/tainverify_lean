"""No-op Triton driver/autotune shim for CPU graph tracing only."""
import triton
from triton.runtime.driver import driver as _driver
class _StubDriver:
    def get_benchmarker(self): return lambda *a, **kw: 0.0
    def get_current_target(self):
        class _T: backend='cpu'
        return _T()
    def __getattr__(self,_name): return lambda *a, **kw: None
_driver._obj=_StubDriver()
triton.autotune=lambda *_a,**_kw:(lambda fn:fn)
