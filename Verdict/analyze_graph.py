import sys
import argparse
from pathlib import Path
from pprint import pformat

# Add paths as in main.py to ensure imports work
sys.path.append(".")
sys.path.append("./genmodel")

from verdict.config import Config
from verdict.verifier import StageParallelVerifier
from verdict.log import setup_logger
from nnscaler_backend import nnScalerGraphBackend
from z3_backend import z3Backend
from verdict.graph import DFG
import z3

def prepare(cfg: Config):
    setup_logger(cfg.loglevel)
    z3.set_param("smt.random_seed", cfg.seed)
    z3.set_param("memory_max_size", 0)
    sys.setrecursionlimit(10000)

def dump_graph_structure(graph: DFG, name: str):
    """
    Analyzes and dumps the structure of the NNScalerDFG graph.
    """
    print(f"\n{'='*40}")
    print(f"Analyzing Graph: {name}")
    print(f"{'='*40}")
    
    if graph is None:
        print("Graph is None.")
        return

    print(f"Graph ID: {graph.ID}")
    nodes = graph.nodes()
    print(f"Total Nodes: {len(nodes)}")
    
    # Iterate through all nodes in the graph
    for i, node in enumerate(nodes):
        opname = graph.node_opname(node)
        kwargs = graph.node_kwargs(node)
        inputs = graph.node_inputs(node)
        outputs = graph.node_outputs(node)
        dtag = graph.node_dtag(node)
        
        print(f"\n[Node {i}] {node}")
        print(f"  OpName: {opname}")
        print(f"  DTag: {dtag}")
        
        if kwargs:
            print(f"  Kwargs: {pformat(kwargs)}")
            
        if inputs:
            print("  Inputs:")
            for t in inputs:
                shape = graph.tensor_shape(t)
                is_init = graph.is_initialized(t)
                print(f"    - Tensor(tid={t.tid}, shape={shape}, rank={t.rank}, mb={t.mb}, initialized={is_init})")
        else:
            print("  Inputs: []")
            
        if outputs:
            print("  Outputs:")
            for t in outputs:
                shape = graph.tensor_shape(t)
                print(f"    - Tensor(tid={t.tid}, shape={shape}, rank={t.rank}, mb={t.mb})")
        else:
            print("  Outputs: []")

def load_graphs(sm_path: str, pm_path: str):
    """
    Loads the Single Model (SM) and Parallel Model (PM) graphs.
    Returns:
        tuple: (graph_single, graph_parallel)
    """
    print(f"Loading SM from: {sm_path}")
    print(f"Loading PM from: {pm_path}")

    v = StageParallelVerifier(
        Gs_path=sm_path,
        Ws_path=None,
        Gp_path=pm_path,
        Wp_path=None,
        graph_backend=nnScalerGraphBackend,
        symbolic_backend=z3Backend,
    )
    
    return v.get_graph()

def main():
    parser = argparse.ArgumentParser(description="Analyze NNScalerDFG graphs (SM and PM)")
    # Default paths taken from main.py for convenience
    parser.add_argument("--sm", type=str, 
                        default="./genmodel/mgeners/llama3adptMegE_mgener_dp1_pp1_tp1_nm1_gbs64_ly1_h32_hi4096_sq128.pkl",
                        help="Path to the Single Model (SM) graph pickle file")
    parser.add_argument("--pm", type=str, 
                        default="./genmodel/mgeners/llama3adptMegE_mgener_dp2_pp2_tp8_nm1_gbs64_ly1_h32_hi4096_sq128.pkl",
                        help="Path to the Parallel Model (PM) graph pickle file")
    
    args, config_args = parser.parse_known_args()
    args.sm = "./genmodel/mgeners/mlp_mgener_dp1_pp1_tp1_nm1_gbs1024_dim1024_ly1.pkl"
    # args.pm = "./genmodel/mgeners/mlp_mgener_dp2_pp2_tp2_nm2_gbs1024_dim1024_ly1.pkl"
    args.pm = "./genmodel/mgeners/mlp_mgener_dp1_pp1_tp8_nm1_gbs1024_dim1024_ly1.pkl"
    # Initialize Config
    Config.update_from_args(config_args)
    prepare(Config)

    try:
        graph_single, graph_parallel = load_graphs(args.sm, args.pm)
        
        # Dump details for Single Model
        dump_graph_structure(graph_single, "Single Model (SM)")
        
        # Dump details for Parallel Model
        dump_graph_structure(graph_parallel, "Parallel Model (PM)")
        
    except Exception as e:
        print(f"Error analyzing graphs: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()
