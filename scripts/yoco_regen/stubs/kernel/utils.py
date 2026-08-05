"""Load llm-train kernel.utils while forcing a CPU target."""
import importlib.util, os
from pathlib import Path
path=Path(os.environ['YOCO_LLM_TRAIN_REPO'])/'llm'/'kernel'/'utils.py'
spec=importlib.util.spec_from_file_location('_real_kernel_utils',path)
real=importlib.util.module_from_spec(spec); real.is_hip=lambda:False; spec.loader.exec_module(real)
for name in dir(real):
    if not name.startswith('_'): globals()[name]=getattr(real,name)
def is_hip(): return False
