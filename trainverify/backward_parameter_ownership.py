"""Authenticate reducer ownership coordinates against the captured world.

Parameter fullref/slice/gradient identity and exact original peer completeness
remain the caller's responsibilities. This shared check never invents a reducer
group, infers values from shapes, or equates different tensor-parallel slices.
"""


def validate_source_reducer_coordinates(world, ranks, coordinates):
    plan, runtime = world.plan_ndevs, world.runtime_ndevs
    if (type(plan) is not int or type(runtime) is not int or plan <= 0
            or runtime < plan or runtime % plan):
        raise ValueError('bw-wred valid original world scale topology required')
    if (not ranks or len(ranks) != len(coordinates)
            or any(type(rank) is not int or not 0 <= rank < runtime for rank in ranks)
            or len(set(ranks)) != len(ranks)):
        raise ValueError('bw-wred complete ordered original ranks required')
    pairs = []
    for rank, pair in zip(ranks, coordinates, strict=True):
        if (type(pair) not in (list, tuple) or len(pair) != 2
                or any(type(c) is not int or c < 0 for c in pair)):
            raise ValueError('bw-wred strict source DP/TP ownership coordinates required')
        # This is the original export_expanded_cells placement convention in
        # Verdict/nnscaler_backend/runtime_source_authority.py, not a shape guess.
        expected = (rank // plan, rank % plan)
        if tuple(pair) != expected:
            raise ValueError('bw-wred coordinate differs from original runtime-rank placement')
        pairs.append(tuple(pair))
    return [list(pair) for pair in pairs]
