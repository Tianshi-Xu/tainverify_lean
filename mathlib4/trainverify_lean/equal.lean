
import Std

open Std

abbrev Matrix := List (List Float)

inductive Op where
  | dataloader
  | fwLinear
  | bwLinear
  | fwSum
  | bwSum
  | chunk (dim : Nat) (idx : Nat)
  | allReduce
  | allGather (dim : Nat)
  | unknown
deriving Repr

structure Node where
  op : Op
  inputs : List Nat
  outputs : List Nat
deriving Repr

def toMap (xs : List (Nat × α)) : Std.HashMap Nat α :=
  xs.foldl (fun m (k,v) => m.insert k v) {}

def tensorShapesSM : List (Nat × List Nat × Bool) := [(15, [1], false), (16, [128, 128], true), (17, [128, 128], false), (20, [128, 128], true), (21, [4, 128], false), (23, [128, 128], false), (24, [128, 128], false), (25, [1], true)]

def tensorShapesPM : List (Nat × List Nat × Bool) := [(15, [1], false), (17, [128, 128], false), (20, [128, 128], true), (24, [128, 128], false), (25, [1], true), (26, [128, 16], false), (27, [128, 16], false), (28, [128, 16], false), (29, [128, 16], false), (30, [128, 16], false), (31, [128, 16], false), (32, [128, 16], false), (33, [128, 16], false), (34, [128, 16], true), (35, [128, 16], true), (36, [128, 16], true), (37, [128, 16], true), (38, [128, 16], true), (39, [128, 16], true), (40, [128, 16], true), (41, [128, 16], true), (42, [128, 128], false), (43, [128, 128], false), (44, [128, 128], false), (45, [128, 128], false), (46, [128, 128], false), (47, [128, 128], false), (48, [128, 128], false), (49, [128, 128], false), (66, [128, 16], false), (67, [128, 16], false), (68, [128, 16], false), (69, [128, 16], false), (70, [128, 16], false), (71, [128, 16], false), (72, [128, 16], false), (73, [128, 16], false), (74, [128, 16], false), (75, [128, 16], false), (76, [128, 16], false), (77, [128, 16], false), (78, [128, 16], false), (79, [128, 16], false), (80, [128, 16], false), (81, [128, 16], false), (82, [16, 128], false), (83, [16, 128], false), (84, [16, 128], false), (85, [16, 128], false), (86, [16, 128], false), (87, [16, 128], false), (88, [16, 128], false), (89, [16, 128], false), (90, [1], false), (91, [1], false), (92, [1], false), (93, [1], false), (94, [1], false), (95, [1], false), (96, [1], false), (97, [1], false), (114, [16, 128], false), (115, [16, 128], false), (116, [16, 128], false), (117, [16, 128], false), (118, [16, 128], false), (119, [16, 128], false), (120, [16, 128], false), (121, [16, 128], false)]

def smNodes : List Node := [{ op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.fwLinear, inputs := [20, 16], outputs := [17] },
  { op := Op.fwSum, inputs := [17], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 17], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 20, 16], outputs := [21, 23] }]

def pmNodes : List Node := [{ op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 0, inputs := [20], outputs := [26] },
  { op := Op.fwLinear, inputs := [26, 34], outputs := [42] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 0, inputs := [17], outputs := [82] },
  { op := Op.fwSum, inputs := [82], outputs := [90] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 82], outputs := [114] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 26, 34], outputs := [66, 67] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 1, inputs := [20], outputs := [27] },
  { op := Op.fwLinear, inputs := [27, 35], outputs := [43] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 1, inputs := [17], outputs := [83] },
  { op := Op.fwSum, inputs := [83], outputs := [91] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 83], outputs := [115] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 27, 35], outputs := [68, 69] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 2, inputs := [20], outputs := [28] },
  { op := Op.fwLinear, inputs := [28, 36], outputs := [44] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 2, inputs := [17], outputs := [84] },
  { op := Op.fwSum, inputs := [84], outputs := [92] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 84], outputs := [116] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 28, 36], outputs := [70, 71] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 3, inputs := [20], outputs := [29] },
  { op := Op.fwLinear, inputs := [29, 37], outputs := [45] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 3, inputs := [17], outputs := [85] },
  { op := Op.fwSum, inputs := [85], outputs := [93] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 85], outputs := [117] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 29, 37], outputs := [72, 73] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 4, inputs := [20], outputs := [30] },
  { op := Op.fwLinear, inputs := [30, 38], outputs := [46] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 4, inputs := [17], outputs := [86] },
  { op := Op.fwSum, inputs := [86], outputs := [94] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 86], outputs := [118] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 30, 38], outputs := [74, 75] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 5, inputs := [20], outputs := [31] },
  { op := Op.fwLinear, inputs := [31, 39], outputs := [47] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 5, inputs := [17], outputs := [87] },
  { op := Op.fwSum, inputs := [87], outputs := [95] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 87], outputs := [119] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 31, 39], outputs := [76, 77] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 6, inputs := [20], outputs := [32] },
  { op := Op.fwLinear, inputs := [32, 40], outputs := [48] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 6, inputs := [17], outputs := [88] },
  { op := Op.fwSum, inputs := [88], outputs := [96] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 88], outputs := [120] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 32, 40], outputs := [78, 79] },
  { op := Op.dataloader, inputs := [], outputs := [20] },
  { op := Op.chunk 1 7, inputs := [20], outputs := [33] },
  { op := Op.fwLinear, inputs := [33, 41], outputs := [49] },
  { op := Op.allReduce, inputs := [42, 43, 44, 45, 46, 47, 48, 49], outputs := [17] },
  { op := Op.chunk 0 7, inputs := [17], outputs := [89] },
  { op := Op.fwSum, inputs := [89], outputs := [97] },
  { op := Op.allReduce, inputs := [90, 91, 92, 93, 94, 95, 96, 97], outputs := [15] },
  { op := Op.bwSum, inputs := [25, 89], outputs := [121] },
  { op := Op.allGather 0, inputs := [114, 115, 116, 117, 118, 119, 120, 121], outputs := [24] },
  { op := Op.bwLinear, inputs := [24, 33, 41], outputs := [80, 81] }]


def smWeightTid : Nat := 16
def pmWeightTids : List (Nat × Nat) := [(34, 0), (35, 1), (36, 2), (37, 3), (38, 4), (39, 5), (40, 6), (41, 7)]  -- (tid, shardIdx)
def pmChunk : Nat := 16

-- deterministic pseudo-random (lightweight): value = scaled(seed + i + j)
def randFloat (state : Nat) : Float :=
  let v := (state % 1000).toFloat / 1000.0
  v * 2.0 - 1.0

def makeMatrix (rows cols seed : Nat) : Matrix :=
  List.range rows |>.map (fun i =>
    List.range cols |>.map (fun j => randFloat (seed + i + j)))

def zerosLike (shape : List Nat) : Matrix :=
  match shape with
  | [r, c] => List.replicate r (List.replicate c 0.0)
  | [r]    => [List.replicate r 0.0]
  | _      => []

def shapeMap (xs : List (Nat × List Nat × Bool)) : Std.HashMap Nat (List Nat) :=
  xs.foldl (fun m (k, s, _) => m.insert k s) {}

def initMap (xs : List (Nat × List Nat × Bool)) : Std.HashMap Nat Bool :=
  xs.foldl (fun m (k, _, b) => m.insert k b) {}

abbrev Store := Std.HashMap Nat Matrix

def getTensor (shapes : Std.HashMap Nat (List Nat)) (inits : Std.HashMap Nat Bool)
    (tid : Nat) (st : Store) : Matrix × Store :=
  match st.find? tid with
  | some v => (v, st)
  | none =>
    let shp := shapes.findD tid []
    let init := inits.findD tid false
    let seed := tid + 17
    -- shared base weight for SM and PM shards
    let baseShape := shapes.findD smWeightTid []
    let shardCols := pmChunk * pmWeightTids.length
    let rows := match baseShape with
      | [r, _] => r
      | _ =>
        match pmWeightTids.head? with
        | some (t, _) =>
            match shapes.findD t [] with
            | [r, _] => r
            | _ => 0
        | none => 0
    let cols := match baseShape with
      | [_ , c] => c
      | _ => shardCols
    let baseWeight : Matrix := makeMatrix rows cols 123
    let shardFromBase (idx : Nat) : Matrix := baseWeight.map (fun r => (r.drop (idx * pmChunk)).take pmChunk)
    let v := if init && shp.length = 2 then
      if tid = smWeightTid then baseWeight
      else match pmWeightTids.find? (fun (t, _) => t = tid) with
        | some (_, idx) => shardFromBase idx
        | none => makeMatrix (shp.get! 0) (shp.get! 1) seed
      else zerosLike shp
    (v, st.insert tid v)

def transpose (m : Matrix) : Matrix :=
  match m with
  | [] => []
  | row :: _ =>
    let cols := row.length
    List.range cols |>.map (fun j => m.map (fun r => r.getD j 0.0))

def dot (a b : List Float) : Float :=
  List.zipWith (· * ·) a b |> List.foldl (· + ·) 0.0

def matmul (a b : Matrix) : Matrix :=
  let bt := transpose b
  a.map (fun row => bt.map (dot row))

def sumAll (m : Matrix) : Float :=
  m.foldl (fun acc row => acc + row.foldl (· + ·) 0.0) 0.0

def sumRows (m : Matrix) : List Float :=
  m.foldl (fun acc row => if acc.length = 0 then row else List.zipWith (· + ·) acc row) []

def onesLike (shape : List Nat) : Matrix :=
  match shape with
  | [r, c] => List.replicate r (List.replicate c 1.0)
  | [r]    => [List.replicate r 1.0]
  | _      => []

def sliceCols (m : Matrix) (start count : Nat) : Matrix :=
  m.map (fun r => (r.drop start).take count)

def sliceRows (m : Matrix) (start count : Nat) : Matrix :=
  (m.drop start).take count

def concatCols (ms : List Matrix) : Matrix :=
  match ms with
  | [] => []
  | _ =>
    let rows := ms.head!.length
    List.range rows |>.map (fun i => ms.foldl (fun acc m => acc ++ m.get! i) [])

def concatRows (ms : List Matrix) : Matrix := ms.foldl (· ++ ·) []

def chunkBy (m : Matrix) (dim start count : Nat) : Matrix :=
  if dim = 0 then sliceRows m start count else sliceCols m start count

def gatherBy (dim : Nat) (parts : List Matrix) : Matrix :=
  if dim = 0 then concatRows parts else concatCols parts

def allReduce (ms : List Matrix) : Matrix :=
  match ms with
  | [] => []
  | m0 :: rest => rest.foldl (fun acc m => List.zipWith (fun r1 r2 => List.zipWith (· + ·) r1 r2) acc m) m0

def headTailN (n : Nat) (xs : List α) : List α :=
  if xs.length ≤ n then xs else xs.take n ++ xs.drop (xs.length - n)

def preview (rows cols : Nat) (m : Matrix) : Matrix :=
  let rsel := headTailN rows m
  rsel.map (fun row => headTailN cols row)

def outputsExist (tids : List Nat) (st : Store) : Bool := tids.all (fun t => st.contains t)

def inputsReady (inits : Std.HashMap Nat Bool) (tids : List Nat) (st : Store) : Bool :=
  tids.all (fun t => st.contains t || inits.findD t false)

def runNode (shapes : Std.HashMap Nat (List Nat)) (inits : Std.HashMap Nat Bool)
    (n : Node) (st : Store) : Store :=
  if outputsExist n.outputs st then st else
  match n.op with
  | Op.dataloader =>
      let shp := shapes.findD n.outputs.head! []
      let seed := n.outputs.head! + 7
      let v := if shp.length = 2 then makeMatrix (shp.get! 0) (shp.get! 1) seed else zerosLike shp
      st.insert n.outputs.head! v
  | Op.fwLinear =>
        if ¬ inputsReady inits n.inputs st then st else
      let (x, st) := getTensor shapes inits (n.inputs.get! 0) st
      let (w, st) := getTensor shapes inits (n.inputs.get! 1) st
      let y := matmul x (transpose w)
      st.insert (n.outputs.get! 0) y
  | Op.fwSum =>
        if ¬ inputsReady inits n.inputs st then st else
      let (x, st) := getTensor shapes inits (n.inputs.get! 0) st
      let s := sumAll x
      st.insert (n.outputs.get! 0) [[s]]
  | Op.bwSum =>
        if ¬ inputsReady inits n.inputs st then st else
      let (g, st) := getTensor shapes inits (n.inputs.get! 0) st
      let (x, st) := getTensor shapes inits (n.inputs.get! 1) st
      let scalar := match g.head? with | some row => row.headD 1.0 | none => 1.0
      let gx := x.map (fun row => row.map (fun _ => scalar))
      st.insert (n.outputs.get! 0) gx
  | Op.bwLinear =>
        if ¬ inputsReady inits n.inputs st then st else
      let (go, st) := getTensor shapes inits (n.inputs.get! 0) st
      let (x, st) := getTensor shapes inits (n.inputs.get! 1) st
      let (w, st) := getTensor shapes inits (n.inputs.get! 2) st
      let gx := matmul go w
      let gw := matmul (transpose x) go
      let st := st.insert (n.outputs.get! 0) gx
      st.insert (n.outputs.get! 1) gw
  | Op.chunk dim idx =>
        if ¬ inputsReady inits n.inputs st then st else
      let (x, st) := getTensor shapes inits (n.inputs.get! 0) st
      let shpOut := shapes.findD (n.outputs.get! 0) []
      let size := if shpOut.length = 2 then (if dim = 0 then shpOut.get! 0 else shpOut.get! 1) else 0
      let start := idx * size
      let part := chunkBy x dim start size
      st.insert (n.outputs.get! 0) part
  | Op.allGather dim =>
        if ¬ inputsReady inits n.inputs st then st else
      let (parts, st) := n.inputs.foldl (fun (ps, st) tid =>
        let (t, st) := getTensor shapes inits tid st
        (ps ++ [t], st)) ([], st)
      let y := gatherBy dim parts
      st.insert (n.outputs.get! 0) y
  | Op.allReduce =>
        if ¬ inputsReady inits n.inputs st then st else
      let (parts, st) := n.inputs.foldl (fun (ps, st) tid =>
        let (t, st) := getTensor shapes inits tid st
        (ps ++ [t], st)) ([], st)
      let y := allReduce parts
      st.insert (n.outputs.get! 0) y
  | Op.unknown => st

def runGraph (nodes : List Node) (shapes : Std.HashMap Nat (List Nat)) (inits : Std.HashMap Nat Bool) : Store :=
  let rec loop (st : Store) (fuel : Nat) : Store :=
    if fuel = 0 then st else
    let (st', progressed) := nodes.foldl (fun (st, prog) n =>
      let stNew := runNode shapes inits n st
      let prog' := prog || (¬ outputsExist n.outputs st) && outputsExist n.outputs stNew
      (stNew, prog')) (st, false)
    if progressed then loop st' (fuel - 1) else st'
  loop {} (5 * nodes.length + 5)

def smShapes := shapeMap tensorShapesSM
def smInits  := initMap tensorShapesSM
def pmShapes := shapeMap tensorShapesPM
def pmInits  := initMap tensorShapesPM

def smStore := runGraph smNodes smShapes smInits
def pmStore := runGraph pmNodes pmShapes pmInits

def smOut : Matrix := smStore.findD 15 []
def pmOut : Matrix := pmStore.findD 15 []

def same : Bool := smOut == pmOut

#eval same
#eval preview 10 10 smOut
#eval preview 10 10 pmOut
