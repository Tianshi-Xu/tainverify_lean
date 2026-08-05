"""CPU tracing stubs for unused quantized paths."""


def _unused(*_args, **_kwargs):
    raise RuntimeError("quantized path invoked during bfloat16 CPU smoke")


get_cached_weight_quant = _unused
per_block_cast_to_fp8 = _unused
per_token_cast_to_fp8 = _unused


def clear_weight_quant_cache():
    return None


def set_weight_quant_cache_enabled(_enabled):
    return None
