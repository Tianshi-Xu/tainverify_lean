"""CPU tracing shims with fallback to the selected llm-train kernel package."""
import os
from pathlib import Path
__path__=[str(Path(__file__).parent),str(Path(os.environ['YOCO_LLM_TRAIN_REPO'])/'llm'/'kernel')]
