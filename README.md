
## 🚀 Installation
1. Create [conda](https://www.anaconda.com/download/success) environment.
    ```
    cd Verdict
    conda env create -f conda-environment.yml
    conda activate verdict
    cd ..
    cd nnscaler_genmodel
    pip install -r requirements.txt
    pip install -e .
    export NNSCALER_HOME=$(pwd)
    export PYTHONPATH=${NNSCALER_HOME}:$PYTHONPATH
    cd ..
    ```
2. Run genmodel/gen_mlp.py to generate execution plans for demo model.
    ```
    PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=1  \
    genmodel/gen_mlp.py --policy dp \
        --dim 128 \
        --layers 2 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 1 \
        --gbs 128 \
        --mbs 128 

    PYTHONPATH=.:$PYTHONPATH OMP_NUM_THREADS=4 torchrun  \
    --nproc_per_node=1  \
    genmodel/gen_mlp.py --policy tp \
        --dim 128 \
        --layers 1 \
        --dp_size 1 \
        --pp_size 1 \
        --tp_size 4 \
        --gbs 128 \
        --mbs 128
    ```
3. Run Verdict/graph_to_lean.py to generate Lean files from execution plans.
    ```
    python Verdict/graph_to_lean.py \
        --input_file genmodel/output/
    ```
4. Proof the lean files in `trainverify/denote`. The structure is:
    ```
    denote/
    ├── denote.lean   // operator definitions
    └── GeneratedData.lean // generated execution plans
    └── Goal_15.lean  // The goal file needing to be proved
    ```