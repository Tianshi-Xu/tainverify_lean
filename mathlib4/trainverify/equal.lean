
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

def tensorShapesPM : List (Nat × List Nat × Bool) := [(15, [1], false), (17, [128, 128], false), (20, [128, 128], true), (24, [128, 128], false), (25, [1], true), (26, [128, 16], false), (27, [128, 16], false), (28, [128, 16], false), (29, [128, 16], false), (30, [128, 16], false), (31, [128, 16], false), (32, [128, 16], false), (33, [128, 16], false), (34, [128, 16], true), (35, [128, 16], true), (36, [128, 16], true), (37, [128, 16], true), (38, [128, 16], true), (39, [128, 16], true), (40, [128, 16], true), (41, [128, 16], true), (42, [128, 128], false), (43, [128, 128], false), (44, [128, 128], false), (45, [128, 128], false), (46, [128, 128], false), (47, [128, 128], false), (48, [128, 128], false), (49, [128, 128], false), (66, [128, 16], false), (67, [128, 16], false), (68, [128, 16], false), (69, [128, 16], false), (70, [128, 16], false), (71, [128, 16], false), (72, [128, 16], false), (73, [128, 16], false), (74, [128, 16], false), (75, [128, 16], false), (76, [128, 16], false), (77, [128, 16], false), (78, [128, 16], false), (79, [128, 16], false), (80, [128, 16], false), (81, [128, 16], false), (82, [16, 128], false), (83, [16, 128], false), (84, [16, 128], false), (85, [16, 128], false), (86, [16, 128], false), (87, [16, 128], false), (88, [16, 128], false), (89, [16, 128], false), (90, [1], false), (91, [1], false), (92, [1], false), (93, [1], false), (94, [1], false), (95, [1], false), (96, [1], false), (97, [1], false), (114, [16, 128], false), (115, [16, 128], false), (116, [16, 128], false), (117, [16, 128], false), (118, [16, 128], false), (119, [16, 128], false), (120, [16, 128], false), (121, [16, 128], false), (122, [128, 128], true), (123, [128, 128], false), (124, [1], false), (125, [128, 128], false), (126, [128, 128], true), (127, [128, 128], false), (128, [1], false), (129, [128, 128], false), (130, [128, 128], true), (131, [128, 128], false), (132, [1], false), (133, [128, 128], false), (134, [128, 128], true), (135, [128, 128], false), (136, [1], false), (137, [128, 128], false), (138, [128, 128], true), (139, [128, 128], false), (140, [1], false), (141, [128, 128], false), (142, [128, 128], true), (143, [128, 128], false), (144, [1], false), (145, [128, 128], false), (146, [128, 128], true), (147, [128, 128], false), (148, [1], false), (149, [128, 128], false)]

def smNodes : List Node := [⟨Op.dataloader, [], [20]⟩,
  ⟨Op.fwLinear, [20, 16], [17]⟩,
  ⟨Op.fwSum, [17], [15]⟩,
  ⟨Op.bwSum, [25, 17], [24]⟩,
  ⟨Op.bwLinear, [24, 20, 16], [21, 23]⟩]

def pmNodes : List Node := [⟨Op.dataloader, [], [122]⟩,
  ⟨Op.chunk 1 0, [122], [26]⟩,
  ⟨Op.fwLinear, [26, 34], [42]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [123]⟩,
  ⟨Op.chunk 0 0, [123], [82]⟩,
  ⟨Op.fwSum, [82], [90]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [124]⟩,
  ⟨Op.bwSum, [25, 82], [114]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [125]⟩,
  ⟨Op.bwLinear, [125, 26, 34], [66, 67]⟩,
  ⟨Op.dataloader, [], [126]⟩,
  ⟨Op.chunk 1 1, [126], [27]⟩,
  ⟨Op.fwLinear, [27, 35], [43]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [127]⟩,
  ⟨Op.chunk 0 1, [127], [83]⟩,
  ⟨Op.fwSum, [83], [91]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [128]⟩,
  ⟨Op.bwSum, [25, 83], [115]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [129]⟩,
  ⟨Op.bwLinear, [129, 27, 35], [68, 69]⟩,
  ⟨Op.dataloader, [], [130]⟩,
  ⟨Op.chunk 1 2, [130], [28]⟩,
  ⟨Op.fwLinear, [28, 36], [44]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [131]⟩,
  ⟨Op.chunk 0 2, [131], [84]⟩,
  ⟨Op.fwSum, [84], [92]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [132]⟩,
  ⟨Op.bwSum, [25, 84], [116]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [133]⟩,
  ⟨Op.bwLinear, [133, 28, 36], [70, 71]⟩,
  ⟨Op.dataloader, [], [134]⟩,
  ⟨Op.chunk 1 3, [134], [29]⟩,
  ⟨Op.fwLinear, [29, 37], [45]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [135]⟩,
  ⟨Op.chunk 0 3, [135], [85]⟩,
  ⟨Op.fwSum, [85], [93]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [136]⟩,
  ⟨Op.bwSum, [25, 85], [117]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [137]⟩,
  ⟨Op.bwLinear, [137, 29, 37], [72, 73]⟩,
  ⟨Op.dataloader, [], [138]⟩,
  ⟨Op.chunk 1 4, [138], [30]⟩,
  ⟨Op.fwLinear, [30, 38], [46]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [139]⟩,
  ⟨Op.chunk 0 4, [139], [86]⟩,
  ⟨Op.fwSum, [86], [94]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [140]⟩,
  ⟨Op.bwSum, [25, 86], [118]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [141]⟩,
  ⟨Op.bwLinear, [141, 30, 38], [74, 75]⟩,
  ⟨Op.dataloader, [], [142]⟩,
  ⟨Op.chunk 1 5, [142], [31]⟩,
  ⟨Op.fwLinear, [31, 39], [47]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [143]⟩,
  ⟨Op.chunk 0 5, [143], [87]⟩,
  ⟨Op.fwSum, [87], [95]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [144]⟩,
  ⟨Op.bwSum, [25, 87], [119]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [145]⟩,
  ⟨Op.bwLinear, [145, 31, 39], [76, 77]⟩,
  ⟨Op.dataloader, [], [146]⟩,
  ⟨Op.chunk 1 6, [146], [32]⟩,
  ⟨Op.fwLinear, [32, 40], [48]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [147]⟩,
  ⟨Op.chunk 0 6, [147], [88]⟩,
  ⟨Op.fwSum, [88], [96]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [148]⟩,
  ⟨Op.bwSum, [25, 88], [120]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [149]⟩,
  ⟨Op.bwLinear, [149, 32, 40], [78, 79]⟩,
  ⟨Op.dataloader, [], [20]⟩,
  ⟨Op.chunk 1 7, [20], [33]⟩,
  ⟨Op.fwLinear, [33, 41], [49]⟩,
  ⟨Op.allReduce, [42, 43, 44, 45, 46, 47, 48, 49], [17]⟩,
  ⟨Op.chunk 0 7, [17], [89]⟩,
  ⟨Op.fwSum, [89], [97]⟩,
  ⟨Op.allReduce, [90, 91, 92, 93, 94, 95, 96, 97], [15]⟩,
  ⟨Op.bwSum, [25, 89], [121]⟩,
  ⟨Op.allGather 0, [114, 115, 116, 117, 118, 119, 120, 121], [24]⟩,
  ⟨Op.bwLinear, [24, 33, 41], [80, 81]⟩]


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
