#!/usr/bin/env bash
# Production YOCO-MoE A0.4B authority generation. Requires a 2-GPU node.
set -euo pipefail
umask 077
if [[ "${TRAINVERIFY_CLEAN_ENV:-}" != 1 ]]; then
  echo 'FATAL: TRAINVERIFY_CLEAN_ENV must equal 1 (use documented env -i launch)' >&2
  exit 2
fi
while IFS= read -r _tv_env_name; do
  case "$_tv_env_name" in
    HOME|PWD|SHLVL|TRAINVERIFY_CLEAN_ENV|TRAINVERIFY_PRIVATE_MATERIALIZATION|YOCO_PYTHON|YOCO_LLM_TRAIN_REPO|YOCO_NNSCALER_REPO|YOCO_AUTHORITY_OUT|YOCO_COMP_PROFILE_ARTIFACT|_) ;;
    *) echo "FATAL: unexpected inherited environment: $_tv_env_name" >&2; exit 2 ;;
  esac
done < <(compgen -e)
: "${YOCO_PYTHON:?set absolute trusted venv python}"
[[ "$YOCO_PYTHON" = /* && -x "$YOCO_PYTHON" ]] || {
  echo 'FATAL: YOCO_PYTHON must be an absolute executable path' >&2; exit 2;
}
unset PYTHONPATH PYTHONHOME PYTHONSTARTUP PYTHONINSPECT PYTHONOPTIMIZE
unset LD_AUDIT LD_PRELOAD LD_LIBRARY_PATH CC CXX CFLAGS CXXFLAGS CPPFLAGS LDFLAGS
unset CPATH LIBRARY_PATH COMPILER_PATH GCC_EXEC_PREFIX
export PATH=/usr/local/cuda/bin:/usr/local/bin:/usr/bin:/bin
export PYTHONSAFEPATH=1 PYTHONNOUSERSITE=1 PYTHONDONTWRITEBYTECODE=1
PYTHON="$YOCO_PYTHON"
PYVER="$("$PYTHON" -S -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
VENV_SITE="$(dirname "$(dirname "$PYTHON")")/lib/python$PYVER/site-packages"
[[ -d "$VENV_SITE" ]] || { echo "FATAL: venv site-packages missing: $VENV_SITE" >&2; exit 2; }
export PYTHONPATH="$VENV_SITE"
: "${YOCO_LLM_TRAIN_REPO:?set absolute llm-train checkout}"
: "${YOCO_NNSCALER_REPO:?set absolute pinned nnScaler checkout}"
: "${YOCO_AUTHORITY_OUT:?set absolute output directory}"
LLM="$(realpath "$YOCO_LLM_TRAIN_REPO")"
NNS_SOURCE="$(realpath "$YOCO_NNSCALER_REPO")"
OUT="$(realpath -m "$YOCO_AUTHORITY_OUT")"
EXTERNAL_COMP_PROFILE="${YOCO_COMP_PROFILE_ARTIFACT:-}"
if [[ -n "$EXTERNAL_COMP_PROFILE" && "$EXTERNAL_COMP_PROFILE" != /* ]]; then
  echo 'FATAL: YOCO_COMP_PROFILE_ARTIFACT must be absolute' >&2
  exit 2
fi
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
: "${TRAINVERIFY_PRIVATE_MATERIALIZATION:?set absolute private TrainVerify materialization}"
[[ "$(realpath "$TRAINVERIFY_PRIVATE_MATERIALIZATION")" == "$ROOT" ]] || {
  echo 'FATAL: script is not running from the declared private TrainVerify materialization' >&2
  exit 2
}
ROOT_MODE="$(stat -c %a "$ROOT")"
[[ "$(stat -c %u "$ROOT")" == "$(id -u)" ]] && (( (8#$ROOT_MODE & 8#077) == 0 )) || {
  echo 'FATAL: TrainVerify materialization must be current-user-owned and owner-private' >&2
  exit 2
}
TRAINVERIFY_REV="$(git -C "$ROOT" rev-parse HEAD)"
[[ "$TRAINVERIFY_REV" =~ ^[0-9a-f]{40}$ ]] || { echo 'FATAL: invalid TrainVerify revision' >&2; exit 2; }
[[ "$(git -C "$ROOT" status --porcelain --untracked-files=all)" == "" ]] || {
  echo 'FATAL: private TrainVerify materialization is dirty' >&2; exit 2;
}
export PYTHONPATH="$ROOT:$VENV_SITE"
EXPECTED_LLM=9a1be1d5fd1c063d80be82797692cdc7d23cfbef
EXPECTED_NNS=d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf
[[ "$(git -C "$LLM" status --porcelain --untracked-files=all)" == "" ]] || {
  echo 'FATAL: llm-train dirty' >&2; exit 2;
}
[[ "$(git -C "$NNS_SOURCE" status --porcelain --untracked-files=all)" == "" ]] || {
  echo 'FATAL: nnScaler source dirty' >&2; exit 2;
}
LLM_REV="$(git -C "$LLM" rev-parse HEAD)"
NNS_REV="$(git -C "$NNS_SOURCE" rev-parse HEAD)"
[[ "$LLM_REV" == "$EXPECTED_LLM" ]] || { echo "FATAL llm revision $LLM_REV" >&2; exit 2; }
[[ "$NNS_REV" == "$EXPECTED_NNS" ]] || { echo "FATAL nnScaler revision $NNS_REV" >&2; exit 2; }
[[ ! -e "$OUT" ]] || { echo "FATAL: output already exists: $OUT" >&2; exit 2; }
mkdir -p "$(dirname "$OUT")"
IFS=$'\t' read -r STAGE STAGE_MARKER STAGE_DEV STAGE_INO < <(
  "$PYTHON" -S "$ROOT/scripts/yoco_regen/safe_cleanup.py" create \
    "$(dirname "$OUT")" ".$(basename "$OUT").partial."
)
cleanup() {
  "$PYTHON" -S "$ROOT/scripts/yoco_regen/safe_cleanup.py" cleanup \
    "$STAGE" "$STAGE_MARKER" "$STAGE_DEV" "$STAGE_INO" || true
}
trap cleanup EXIT
IFS=$'\t' read -r PROFILE_HOME PROFILE_MARKER PROFILE_DEV PROFILE_INO < <(
  "$PYTHON" -S "$ROOT/scripts/yoco_regen/safe_cleanup.py" create \
    "$STAGE" ".profile-home."
)
LLM_WORK="$STAGE/.llm-train-source"
NNS_WORK="$STAGE/.nnscaler-source"
export TRAINVERIFY_LLM_SOURCE_ROOT="$LLM_WORK/llm"
git clone --quiet --no-hardlinks "$LLM" "$LLM_WORK"
git clone --quiet --no-hardlinks "$NNS_SOURCE" "$NNS_WORK"
git -C "$LLM_WORK" checkout --quiet "$EXPECTED_LLM"
git -C "$NNS_WORK" checkout --quiet "$EXPECTED_NNS"
"$PYTHON" -S "$ROOT/scripts/yoco_regen/patch_mgener_dump.py" "$NNS_WORK/nnscaler/parallel.py"
"$PYTHON" -S "$ROOT/scripts/yoco_regen/patch_llm_cc12_gemm.py" "$LLM_WORK/llm/kernel/gemm.py"
DP_SOLVER_BUILD_OUTPUT="$STAGE/.dp-solver-build-output"
IFS=$'\t' read -r DP_SOLVER_BUILD_ARTIFACT TRAINVERIFY_DP_SOLVER_SHA256 < <(
  "$PYTHON" -S "$ROOT/scripts/yoco_regen/build_dp_solver.py" build \
    "$NNS_WORK" "$EXPECTED_NNS" "$DP_SOLVER_BUILD_OUTPUT"
)
DP_SOLVER_EXTENSION="$NNS_WORK/nnscaler/autodist/$(basename "$DP_SOLVER_BUILD_ARTIFACT")"
ln "$DP_SOLVER_BUILD_ARTIFACT" "$DP_SOLVER_EXTENSION"
ln "$DP_SOLVER_BUILD_ARTIFACT" "$STAGE/nnscaler_dp_solver.so"
export TRAINVERIFY_DP_SOLVER_SHA256
read -r TRAINVERIFY_PATCHED_LLM_GEMM_SHA256 _ < <(
  sha256sum "$LLM_WORK/llm/kernel/gemm.py"
)
export TRAINVERIFY_PATCHED_LLM_GEMM_SHA256
COMM_PROFILE_SOURCE="$(
  PYTHONPATH="$NNS_WORK:$VENV_SITE" "$PYTHON" -S -c \
    'from nnscaler.autodist.util import get_default_profile_path; print(get_default_profile_path() / "comm" / "intra_2.json")'
)"
PROFILE_ARCH="$(
  PYTHONPATH="$NNS_WORK:$VENV_SITE" "$PYTHON" -S -c \
    'from nnscaler.autodist.util import get_node_arch; print(get_node_arch())'
)"
PRIVATE_COMM_DIR="$PROFILE_HOME/.cache/nnscaler/autodist/1.0/$PROFILE_ARCH/comm"
mkdir -p "$PRIVATE_COMM_DIR"
TRAINVERIFY_COMM_PROFILE_SHA256="$(
  "$PYTHON" -S "$ROOT/scripts/yoco_regen/comm_profile.py" \
    "$COMM_PROFILE_SOURCE" "$PRIVATE_COMM_DIR/intra_2.json"
)"
ln "$PRIVATE_COMM_DIR/intra_2.json" "$STAGE/comm_profile_intra_2.json"
export TRAINVERIFY_COMM_PROFILE_SHA256
DP_SOLVER_SITE_GUARD="$STAGE/.dp-solver-site-guard"
mkdir -m 0700 "$DP_SOLVER_SITE_GUARD"
cp "$ROOT/scripts/yoco_regen/dp_solver_sitecustomize.py" \
  "$DP_SOLVER_SITE_GUARD/sitecustomize.py"
chmod 0444 "$DP_SOLVER_SITE_GUARD/sitecustomize.py"
export PYTHONPATH="$ROOT:$VENV_SITE"
export TRAINVERIFY_EXPECTED_POLICY='main.<locals>.autodist_wrapper'
cd "$LLM_WORK/llm"
COMMON=(
  --model YOCO-MoE-A0.4B --data long-256k-251219 --num_workers 0
  --hyperparams warmup_constant --batch_size 1 --update_freq 1
  --max_seq_len 4096 --name trainverify_yoco_a04b_9a1be1d
  --gpu_mem_constraint 200 --disable_shared_param_constraint --precision fp32
  --xentropy_recompute --recompute_modules Block --run_mode compile
  --partition_constraints_path ./pcs/all2all_moe.yaml
)
run_compile() {
  local kind="$1" plan="$2" port="$3" profile_mode="$4"
  local dump="$STAGE/${kind}_mgener.pkl" gen="$STAGE/.nnscaler_${kind}"
  local profile_args=()
  if [[ "$profile_mode" == live ]]; then
    profile_args=(--allow-live-comp-profile)
  elif [[ "$profile_mode" == frozen ]]; then
    profile_args=(
      --comp-profile "$STAGE/comp_profile.json"
      --comp-profile-sha256 "$TRAINVERIFY_COMP_PROFILE_SHA256"
    )
  else
    echo "FATAL: invalid computation profile mode: $profile_mode" >&2
    exit 2
  fi
  HOME="$PROFILE_HOME" MGENER_DUMP_PATH="$dump" \
  "$PYTHON" -S "$ROOT/scripts/yoco_regen/sealed_extension_exec.py" \
    "${profile_args[@]}" run \
    "$DP_SOLVER_EXTENSION" "$TRAINVERIFY_DP_SOLVER_SHA256" "$NNS_WORK" \
    "$DP_SOLVER_SITE_GUARD/sitecustomize.py" "$LLM_WORK/llm" \
    -- torchrun \
    --nproc_per_node="$plan" --nnodes=1 --node_rank=0 \
    --master_addr=127.0.0.1 --master_port="$port" \
    nnscaler_train.py "${COMMON[@]}" \
    --plan_ngpus "$plan" --runtime_ngpus "$plan" --zero_group_size "$plan" \
    --gen_savedir "$gen"
  [[ -s "$dump" ]] || { echo "FATAL missing $dump" >&2; exit 3; }
  [[ -s "$dump.receipt.json" ]] || { echo "FATAL missing $dump.receipt.json" >&2; exit 3; }
}
if [[ -n "$EXTERNAL_COMP_PROFILE" ]]; then
  TRAINVERIFY_COMP_PROFILE_SHA256="$(
    "$PYTHON" -S -m scripts.yoco_regen.comp_profile copy \
      "$EXTERNAL_COMP_PROFILE" "$STAGE/comp_profile.json"
  )"
else
  TRAINVERIFY_COMP_PROFILE_SHA256="$(printf '0%.0s' {1..64})"
  export TRAINVERIFY_COMP_PROFILE_SHA256
  run_compile .warmup_sm 1 29581 live
  run_compile .warmup_pm 2 29582 live
  COMP_PROFILE_DIR="$PROFILE_HOME/.cache/nnscaler/autodist/1.0/$PROFILE_ARCH/comp"
  "$PYTHON" -S -m scripts.yoco_regen.comp_profile create \
    "$COMP_PROFILE_DIR" "$STAGE/comp_profile.json"
  read -r TRAINVERIFY_COMP_PROFILE_SHA256 _ < <(sha256sum "$STAGE/comp_profile.json")
  rm -rf "$COMP_PROFILE_DIR" \
    "$STAGE/.warmup_sm_mgener.pkl" "$STAGE/.warmup_sm_mgener.pkl.receipt.json" \
    "$STAGE/.warmup_pm_mgener.pkl" "$STAGE/.warmup_pm_mgener.pkl.receipt.json" \
    "$STAGE/.nnscaler_.warmup_sm" "$STAGE/.nnscaler_.warmup_pm"
  [[ ! -e "$COMP_PROFILE_DIR" ]] || {
    echo 'FATAL: live computation profile directory survived freezing' >&2; exit 3;
  }
fi
export TRAINVERIFY_COMP_PROFILE_SHA256
run_compile sm 1 29583 frozen
run_compile pm 2 29584 frozen
"$PYTHON" -S -m scripts.yoco_regen.write_authority_metadata \
  --llm-train "$LLM_WORK" --nnscaler "$NNS_WORK" --authority-dir "$STAGE" \
  --comm-profile "$STAGE/comm_profile_intra_2.json" \
  --comp-profile "$STAGE/comp_profile.json" \
  --dp-solver-extension "$DP_SOLVER_EXTENSION" \
  --trainverify-revision "$TRAINVERIFY_REV" \
  --trust-local-pickle
rm -rf "$STAGE/.nnscaler_sm" "$STAGE/.nnscaler_pm" \
  "$DP_SOLVER_BUILD_OUTPUT" "$DP_SOLVER_SITE_GUARD" "$LLM_WORK" "$NNS_WORK"
"$PYTHON" -S "$ROOT/scripts/yoco_regen/safe_cleanup.py" cleanup \
  "$PROFILE_HOME" "$PROFILE_MARKER" "$PROFILE_DEV" "$PROFILE_INO"
[[ ! -e "$PROFILE_HOME" ]] || { echo 'FATAL: private profile HOME survived cleanup' >&2; exit 4; }
[[ "$(git -C "$ROOT" rev-parse HEAD)" == "$TRAINVERIFY_REV" ]] || {
  echo 'FATAL: TrainVerify revision changed during generation' >&2; exit 4;
}
[[ "$(git -C "$ROOT" status --porcelain --untracked-files=all)" == "" ]] || {
  echo 'FATAL: private TrainVerify materialization changed during generation' >&2; exit 4;
}
"$PYTHON" -S -m scripts.yoco_regen.atomic_publish "$STAGE" "$OUT"
trap - EXIT
STAGE=""
echo "authority generated atomically at $OUT"
