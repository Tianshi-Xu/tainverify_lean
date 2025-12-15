SOSP '25, October 13–16, 2025, Seoul, Republic of Korea

Yunchi Lu, Youshan Miao, Cheng Tan, Peng Huang, Yi Zhu, Xian Zhang, and Fan Yang

Group Controlled Variable

global batch size
hidden dimension size
sequence length
heads

gbs hidden seqlen heads pp layers dp mb tp
2
*
2
512
2
32
2
512
2
pipeline parallelism 512
8
512
8
512
8
512
*
512

layers
data parallelism
micro batches
tensor parallelism

4096
*
128
4096
4096
4096
4096
4096
4096

128
128
*
128
128
128
128
128
128

32
32
32
*
32
32
32
32
32

32
32
32
32
32
*
32
32
32

2
2
2
2
2
16
*
16
16

2
2
2
2
2
8
8
*
8

2
2
2
2
*
4
4
4
4

b
c
d
e
f
g
h
i
j

Table 7. Configurations for variable controlled experiments.

CP 1 to partially counteract the anti-scaling 2 introduced
by weight reducers in data parallelism 3 , ensuring that the
final updates reflect per-input-sequence gradients. However,
when calculate-per-token-loss is enabled, the averaging
across the DP×CP communication group is skipped and instead
replaced by averaging over the total number of trained tokens
4 . In this case, the combination of 1 and 4 results in the
final gradients being over-scaled by a factor of CP.

TrainVerify can eliminate such bugs by comparing data
flow of shape-reduced symbolic tensors. While the violation
could be detected earlier via 𝐿 == 𝐿0, practical implementa-
tions typically do not enforce strict equivalence on distributed
losses. Moreover, adapted graphs from manually-parallelized
models lack the backward lineage, e.g. 𝑡 L
== (𝑡0, 𝑡1) that
is naturally preserved by auto-parallel systems. As a result,
TrainVerify detects the problem as soon as it visits a weight
tensor in backward pass, (e.g., 𝑔𝑤0) by checking that its final-
ized gradient 𝐺0 is consistent with 𝐺.

Such computational issues are subtle, making diagnosis
particularly challenging, especially when the code spans mul-
tiple modules. The issue post reflects a 10-day effort involving
users, developers, and volunteers to reproduce the problem
and identify its root cause, amid early misdiagnoses and user
concerns. In the year prior to that fix, over 5 issues were filed
on the same code snippets, across various training configura-
tions; some were misreported, while others were resolved after
extensive discussion. TrainVerify can effectively alleviate
such challenges and ensure verified correctness.

C Shape reduction correctness proof
For complete correctness proof of shape reduction, please refer
to our external document at https://arxiv.org/abs/2506.15961.
CT: minor: - use bold for tensors; normal for scalar -
0-indexing vs. 1-based indexing (using (cid:174)0 seems indicating
0-based) - indexing is in I not R.

When a DNN model involves large size tensors, such as
popular LLMs, it becomes infeasible for current solvers (e.g.,
Z3) to verify its parallel execution considering the complexity,
as tensors now have symbolic elements. In response, we
propose a verification for the same model architecture but

YM: consider
Natural Num-
bers N or
Integers Z
rather than I

with reduced tensor shapes, and prove that: the verification
conclusion on the shape-reduced model also applies to the
original model with larger tensor shapes.

C.1 Formalization
A DNN model consists of multiple operators, such as MatMul
and ReLU, which essentially are functions with data tensors
as input and output. Given input tensor(s), including tensors
representing weights, activation and optimizer state, such a
DNN function can produce corresponding output tensor(s).
Given a DNN function 𝑓 that executes on a single device,
there is an alternative function 𝑔 (𝑔 is different from 𝑓 ) that
can execute on either single device sequentially or multiple
devices concurrently. Our goal is to verify that regardless of
the inputs, 𝑓 and 𝑔 can always produce the same results—an
equivalence.

Definition 8 (Tensor). A tensor is an object that generalizes
scalars, vectors, and matrices to higher dimensions. Formally,
an order-𝑛 tensor (also called an 𝑛-th order tensor) is an
element of the tensor space:

T ∈ R𝑑1 ×𝑑2 ×···×𝑑𝑛
(1)
where R represents real number field and 𝑑1, 𝑑2, . . . , 𝑑𝑛

denote the dimensions along each mode of the tensor.

Tensors are used as primitive data in machine learning.

𝑓 : (R𝑑𝑎

Definition 9 (Functions). A general function that operates on
multiple tensors can be defined as:
2 ×···×𝑑𝑎
2 ×···×𝑑𝑏

𝑘
(2)
where 𝑓 takes one or more tensors as input and outputs a
tensor of a potentially different shape.

𝑚, · · · ) → R𝑑 𝑦

2 ×···×𝑑 𝑦

𝑛 , R𝑑𝑏

1 ×𝑑 𝑦

1 ×𝑑𝑎

1 ×𝑑𝑏

For simplicity, we assume a single-tensor input/output for
function 𝑓 throughout this proof. The proof can be naturally
extended to accommodate multiple input and output tensors.
We use bold symbols (e.g., x, y) to denote tensors and
non-bold symbols (e.g., 𝑥, 𝑦) to denote scalars. We also use
zero-based indexing; that is, for a vector v, the first element is
"v[0]".

TrainVerify: Equivalence-Based Verification for Distributed LLM Training

SOSP '25, October 13–16, 2025, Seoul, Republic of Korea

People have long observed that deep learning operators like
element-wise operations and convolution are SIMD (Single-
Instruction Multiple-Data): the operation consists of repeated,
homogeneous computations (the "kernel") over array elements.
This SIMD characteristic is the core enabler for our shape
reduction mechanism. Below, we formally define what is a
SIMD function.

Consider a function 𝑓 (x) → y, where x ∈ 𝑅𝑑𝑎

1 ×𝑑𝑎

2 ×···×𝑑𝑎

𝑚

and y ∈ 𝑅𝑑𝑏

1 ×𝑑𝑏

2 ×···×𝑑𝑏

𝑛 . So, 𝑟𝑎𝑛𝑘 (x) = 𝑚 and 𝑟𝑎𝑛𝑘 (y) = 𝑛.

If 𝑓 is a SIMD function, a kernel function 𝜃 associated
with 𝑓 takes a subtensor from x and outputs a scalar value.
Formally:

Definition 10 (Kernel function). A kerenel function 𝜃 is a
function that takes 𝑘 scalar inputs and produces a single
scalar output:

𝜃 : R𝑘 → R.

Next, we define which input subtensor is associated with
each output element. Consider the same function 𝑓 (x) → y.
A dependency mapping 𝜏 associated with 𝑓 is a function that
maps each index i in the output y to a list of indices in the
input x. Formally:

Definition 11 (Dependency mapping). A dependency map-
ping 𝜏 is an affine transformation that maps a vector of integers
(an index of tensor y) to a list of indices in another tensor (i.e.,
x):

𝜏 : 𝑖𝑑𝑥 (y) ∈ N𝑛 → [𝑖𝑑𝑥 (x), . . . ] ∈ N𝑘 ×𝑚,

where 𝑖𝑑𝑥 (·) is the indexing function of the tensor; 𝑛 and 𝑚
are ranks of x and y; and 𝑘 is the number of inputs in 𝜃 .

With dependency mapping and kernel function, we define

SIMD functions.

Definition 12 (SIMD function). A function 𝑓 (x) → y is a
SIMD function if, for each y[i], i ∈ N𝑛,

y[i] = 𝜃 (x1, x2, . . . , x𝑘 ),

where 𝜃 is the kernel function of 𝑓 , and

x𝑗 = x[𝜏 (i) [ 𝑗]],

1 ≤ 𝑗 ≤ 𝑘m

where 𝜏 is the dependency mapping of 𝑓 .

By fixing the latent representation – kernel function 𝜃
and a dependency mapping 𝜏 – one can define an SIMD
function. We denote an SIMD function 𝑓 using its 𝜃 𝑓 and 𝜏𝑓
as: y[i] = 𝜃 𝑓 (x[𝜏𝑓 (i)]).

Finally, we introduce another class of operators, reductional
opreations, such as sum. A reductional function 𝑓 : R𝑚 → R
returns a single output element from processing a reductional
operation among all elements in the input tensor, with the
operation satisfying the commutative and associative laws.

Definition 13 (Reductional function). For an input tensor
x ∈ R𝑚, the reductional function 𝑓⊙ applies a binary operation
⊙ to all elements of x such that:

𝑓⊙ (x) = x[0] ⊙ x[1] ⊙ · · · ⊙ x[𝑚 − 1],

and ⊙ satisfies commutativity (𝑎 ⊙ 𝑏 = 𝑏 ⊙ 𝑎) and associativity
((𝑎 ⊙ 𝑏) ⊙ 𝑐 = 𝑎 ⊙ (𝑏 ⊙ 𝑐)).

C.2 Observations: LLM operators are SIMD functions
Deep Neural Network (DNN) computations are characterized
by their application to high-dimensional data tensors. A closer
examination of commonly used DNN operations reveals that
a large number of elements in the output tensor share the
same computational logic, differing only in the specific input
elements they process. This computational pattern aligns
closely with our definition of SIMD functions.

C.2.1 Observation 1: LLM operators have kernel func-
tions. We observe that each computation operator in the
transformer architecture is associated with its own kernel
function, including Feed Forward layers, Multi-Head Atten-
tion layers (without masking), Add & Norm layers, ReLU,
Softmax, and Residual Addition.

Consider matrix multiplication (i.e., MatMul) as an example.
Given two matrices A ∈ R𝑚×𝑝 and B ∈ R𝑝 ×𝑛, the resulting
matrix C ∈ R𝑚×𝑛 has elements 𝑐𝑖,𝑗 (short for C[𝑖] [ 𝑗]) com-
puted by: 𝑐𝑖,𝑗 = (cid:205)𝑝
𝑎𝑖,𝑘 ·𝑏𝑘,𝑗 . Therefore, MatMul has a kernel
function:

𝑘=1

𝜃 (𝑎𝑖,1, . . . , 𝑎𝑖,𝑝, 𝑏1,𝑗, . . . , 𝑏𝑝,𝑗 ) = (cid:205)𝑝

𝑘=1

𝑎𝑖,𝑘 · 𝑏𝑘,𝑗

C.2.2 Observation 2: dependency mappings in LLM op-
erators share linear components. This property is intuitive,
as the "striding" of kernel functions across tensors typically
occurs at regular, constant intervals. Consequently, when
the input to the dependency mapping—corresponding to the
output tensor's index—changes, the resulting input indices
change linearly and follow the same pattern. That is, for each
input tensor, the mapping takes the affline transformations:

𝜏 (i) = [M · i + b1,

. . . , M · i + b𝑘 ].

For example, in the above MatMul case, the dependency
mapping 𝜏𝐴 for the first input matrix A can be written as affine
transformations:

YC: we need
to revisit
the example
as Mat-
mul=simd+redux+simd

𝜏𝐴 (

(cid:21)

(cid:20)𝑖
𝑗

) = [M𝐴

(cid:21)

(cid:20)𝑖
𝑗

M𝐴 =

(cid:18)1
0

(cid:19)

0
0

, b𝐴1 =

+ b𝐴1, . . . , M𝐴
(cid:18)0
1

, . . . , b𝐴𝑝 =

(cid:19)

(cid:19)

(cid:18)0
𝑝

(cid:21)

(cid:20)𝑖
𝑗

+ b𝐴𝑝 ], where

Above all, MatMul is a SIMD function because it has

• a kernel function:

𝜃 (𝑎𝑖,1, . . . , 𝑎𝑖,𝑝, 𝑏1,𝑗, . . . , 𝑏𝑝,𝑗 ) = (cid:205)𝑝

𝑘=1

𝑎𝑖,𝑘 · 𝑏𝑘,𝑗 ;

SOSP '25, October 13–16, 2025, Seoul, Republic of Korea

Yunchi Lu, Youshan Miao, Cheng Tan, Peng Huang, Yi Zhu, Xian Zhang, and Fan Yang

• a dependency mapping for each input tensor:

𝜏𝐴 ([𝑖, 𝑗]) = [[𝑖, 𝑘]|1 ≤ 𝑘 ≤ 𝑝],
𝜏 𝐵 ([𝑖, 𝑗]) = [[𝑘, 𝑗]|1 ≤ 𝑘 ≤ 𝑝],
where 𝜏𝐴 and 𝜏 𝐵 are dependency mappings for input matrix
A and B;

• and MatMul can be expressed as:

𝑐𝑖,𝑗 = 𝜃 (A[𝜏𝐴 ([𝑖, 𝑗])] ⊕ B[𝜏 𝐵 ([𝑖, 𝑗])]),

where ⊕ represents vector concatenation.

Fact 5. We observe that in practice, the dependency mapping
𝜏 (·) does not produce duplicated input indices. Meaning,

∀i, 𝜏 (i) = [j1, j2, . . . , j𝑘 ] ∈ N𝑘 ×𝑚,
for 1 ≤ 𝑎 ≠ 𝑏 ≤ 𝑘 in 𝜏 (i), j𝑎 ≠ j𝑏 .

Essentially, all elements in the inputs to the well-formed
kernel functions contribute to the final output. There is no
such input element that does not influcent the output.

C.3.2 Premises from SMT solver. In TrainVerify, we
use an SMT solver (Z3) to verify that a shape-reduced model
preserves parallelization equivalence. Specifically, if the solver
returns sat, it proves that for all inputs, the logical dataflow
graph of the shape-reduced model is equivalent to that of the
parallelized version.

This result yields a premise for each stage (§5.2) in Train-

Verify of the form:

∀x, ∀i ∈ I, 𝑓 (x) [i] = 𝑔(x) [i],

where I = {

𝑛
∑︁

𝑗=0

𝑎 𝑗 e𝑗

| 𝑎 𝑗 ∈ {0, 1} for all 𝑗 }

YC: we
may need a
clearer sep-
aration/clar-
ification of
whether our
SIMD include
the reduc-
tional op
(norm)

C.3 Correctness proof for shape reduction
This section establishes the correctness of TrainVerify's
shape reduction by proving the equivalence between two data
flow graphs (DFGs) at a reduced scale implies equivalence
at the original scale. We denote the original and transformed
DFGs—before and after applying parallelization techniques—
as functions 𝑓 and 𝑔, respectively.

C.3.1 Prerequisite relations. Before presenting the main
theorem, we begin with two equivalent definitions that serve
as the foundation for the proof.

Definition 14 (Mapping permutation equivalence). For two
dependency mappings 𝜏1 and 𝜏2, we call them mapping per-
mutation equivalence, denoted 𝜏1 (cid:27)𝑃 𝜏2, if there exists a
permutation function 𝑃, such that

∀𝑖, 𝑃 (𝜏1(𝑖)) = 𝜏2(𝑖)

Mapping permutation equivalence captures LLM operators
with commutative and associative properties, where permuting
the inputs does not affect the output. Similarly, we need
to define a corresponding equivalence relation for kernel
functions.

Definition 15 (Kernel permutation-set equivalence). For two
kernel functions 𝜃1 and 𝜃2, we call them kernel permutation-
set equivalence, denoted 𝜃1 (cid:27)𝑄 𝜃2, if there exists a non-empty
set 𝑄 of permutation functions, such that

∀𝑃 ∈ 𝑄, ∀x, 𝜃1(x) = 𝜃2(𝑃 (x))

Definition 16 (Well-formed kernel function). We call a kernel
function 𝜃 well-formed if,

∃x, x′, ∀𝑖, x[𝑖] ≠ x′ [𝑖] and ∀𝑗 ≠ 𝑖, x[ 𝑗] = x′ [ 𝑗]

𝜃 (x) ≠ 𝜃 (x′)

YC: the
"from" and
"to" relation
of the equa-
tion is not
clear; the
expression
is not well
aligned with
the def se-
mantics

In the equation, e𝑖 denotes the standard basis vectors in R𝑛,
defined as:

(e𝑖 ) 𝑗 =

(cid:40)

if 𝑗 = 𝑖,
1
0 otherwise.

Each e𝑖 ∈ N𝑛 is a column vector with a single 1 in the i-th
position and 0 elsewhere, except for 𝑒0 which is all 0s. For
example,

0
...
e0 = (cid:169)
(cid:173)
(cid:173)
0
(cid:171)

1
...
, e1 = (cid:169)
(cid:173)
(cid:173)
0
(cid:171)

0
...
, . . . , e𝑛 = (cid:169)
(cid:173)
(cid:173)
1
(cid:171)

(cid:170)
(cid:174)
(cid:174)
(cid:172)𝑛×1

(cid:170)
(cid:174)
(cid:174)
(cid:172)𝑛×1

(cid:170)
(cid:174)
(cid:174)
(cid:172)𝑛×1
The above premise holds due to Algorithm 2, line 12,
where TrainVerify enforces that, for any output dimension
of each operator—excluding those not involved in computation
(e.g., batch dimensions, or all dimensions in element-wise
operations)—both the logical and parallelized dataflow graphs
retain a size of at least two in those dimensions. Meanwhile,
the equivalence for abitrary input x is established by the
symbolic computation.

C.3.3 Main proofs. We now present the main proof of
shape reduction correctness. The argument proceeds in three
steps:
1. We first prove 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔 given the above premise.
2. We then prove 𝜏𝑓 (cid:27)𝑃 𝜏𝑔 based on the premise.
3. Finally, we apply 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔 and 𝜏𝑓 (cid:27)𝑃 𝜏𝑔 to establish the

shape reduction theorem.

Next, we consider 𝑓 (x) → y and 𝑔(x) → y′, where x ∈
𝑅𝑑𝑎
2 ×···×𝑑𝑎
𝑛 . So, 𝑟𝑎𝑛𝑘 (x) = 𝑚
and 𝑟𝑎𝑛𝑘 (y) = 𝑛.

𝑚 and y, y′ ∈ 𝑅𝑑𝑏

2 ×···×𝑑𝑏

1 ×𝑑𝑎

1 ×𝑑𝑏

We start with a claim that if for all inputs x, 𝑓 and 𝑔 give
the same output at position i, then the dependency mappings
share the same set of indices.

Claim 6. For two well-formed SIMD functions 𝑓 and 𝑔,

∀x, 𝑓 (x) [i] = 𝑔(x) [i] =⇒ ∃!𝑃, 𝑃 (𝜏𝑓 (i)) = 𝜏𝑔 (i).

There exists exactly one permutation 𝑃 between dependency
mappings 𝜏𝑓 and 𝜏𝑔.

Proof. Since 𝑓 and 𝑔 are SIMD functions, by Definition 12
and the premise, ∀x, 𝜃 𝑓 (x[𝜏𝑓 (i)]) = 𝜃𝑔 (x[𝜏𝑓 (i)]).

First, we prove the existence of 𝑃 by contradition—assume
there is no such a 𝑃: 𝑠𝑒𝑡 (𝜏𝑓 (i)) ≠ 𝑠𝑒𝑡 (𝜏𝑔 (i)). Then, there
exists some element j ∈ 𝜏𝑓 (i) but j ∉ 𝜏𝑔 (i). We can con-
struct an input ˆx such that all elements other than j-th are 0;
and ˆx[j] can be an arbitrary number. Note that by premise,
𝜃 𝑓 ( ˆx[𝜏𝑓 (i)]) = 𝜃𝑔 ( ˆx[𝜏𝑔 (i)]). By Definition 16, 𝑓 and 𝑔 are
well-formed, so each input contributes meaningfully. There-
fore, 𝜃 𝑓 ([0, . . . , ˆx[j], . . . , 0]) ≠ 𝜃𝑔 ((cid:174)0), a contradiction to the
premise. This means 𝑠𝑒𝑡 (𝜏𝑓 (i)) = 𝑠𝑒𝑡 (𝜏𝑔 (i)).

Finally, we prove 𝑃 is the only possible permutation. By
Fact 5, all elements in 𝑠𝑒𝑡 (𝜏𝑓 (i)), and correspondingly in
𝑠𝑒𝑡 (𝜏𝑔 (i)), are distinct scalars. Therefore, there exists a unique
□
permutation 𝑃 such that 𝑃 (𝜏𝑓 (i)) = 𝜏𝑔 (i).

Proof. Consider 𝑖 = 0; that is e0 = (cid:174)0.

∀x,𝑓 (x) [(cid:174)0] = 𝑔(x) [(cid:174)0]

⇒ 𝜃 𝑓 (x[𝜏𝑓 ((cid:174)0)]) = 𝜃𝑔 (x[𝜏𝑔 ((cid:174)0)])

[Definition 12]

⇒ 𝜃 𝑓 (x[M𝑓 · (cid:174)0 + b𝑓 ]) = 𝜃𝑔 (x[M𝑔 · (cid:174)0 + b𝑔])

[Definition 11, affine transformation]

⇒ 𝜃 𝑓 (x[[b𝑓 1, ..., b𝑓 𝑘 ]) = 𝜃𝑔 (x[[b𝑔1, ..., b𝑔𝑘 ]])

[expanding b]

By Claim 6, there exists a unique permutation, say 𝑃0, such
that 𝑃0([b𝑓 1, . . . , b𝑓 𝑘 ]) = [b𝑔1, . . . , b𝑔𝑘 ].

Similarly, consider 𝑖 = 1 for the premise, which gives

∀x, 𝑓 (x) [e1] = 𝑔(x) [e1], where e1 = [1, 0, 0, . . . ] ∈ N𝑛.

Lemma 7. For SIMD functions 𝑓 and 𝑔 with well-formed
kernel functions:

∀x, 𝑓 (x) [e0] = 𝑔(x) [e0] =⇒ 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔.

∀x,𝑓 (x) [e1] = 𝑔(x) [e1]

⇒ 𝜃 𝑓 (x[𝜏𝑓 (e1)]) = 𝜃𝑔 (x[𝜏𝑔 (e1)])
⇒ 𝜃 𝑓 (x[𝑀𝑓 · e1 + b𝑓 1], . . . ) = 𝜃𝑔 (x[𝑀𝑔 · e1 + b𝑔1], . . . )

Proof. Recall e0 = (cid:174)0 ∈ N𝑛. Then, we have ∀x, 𝑓 (x) [(cid:174)0] =
𝑔(x) [(cid:174)0]. Because 𝑓 and𝑔 are SIMD functions, ∀x, 𝜃 𝑓 (x[𝜏𝑓 ((cid:174)0)]) =
𝜃𝑔 (x[𝜏𝑔 ((cid:174)0)]). By Claim 6, there exists a permuation, say 𝑃0,
such that 𝑃0(𝜏𝑓 ((cid:174)0)) = 𝜏𝑔 ((cid:174)0).

We denote X = x[𝜏𝑓 ((cid:174)0)]. By Fact 5, 𝜏𝑓 ((cid:174)0) doesn't have du-
plicated indices, meaning X traces back to 𝑘 unique positions
of x. Hence, X covers all possible inputs of R𝑘 , becaue x is
an arbitrary R𝑑1 ×...𝑑𝑚 tensor.

So, we have:

∀x, 𝜃 𝑓 (x[𝜏𝑓 ((cid:174)0)]) = 𝜃𝑔 (x[𝜏𝑔 ((cid:174)0)])

⇒ 𝜃 𝑓 (x[𝜏𝑓 ((cid:174)0)]) = 𝜃𝑔 (x[𝑃0 (𝜏𝑓 ((cid:174)0))])
⇒ 𝜃 𝑓 (x[𝜏𝑓 ((cid:174)0)]) = 𝜃𝑔 (𝑃0(x[𝜏𝑓 ((cid:174)0)]))
⇒ 𝜃 𝑓 (X) = 𝜃𝑔 (𝑃0(X))
⇒ 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔

[Claim 6]

[tensor indexing]

[X = x[𝜏𝑓 ((cid:174)0)]]
[Definition 15]

In addition, 𝑃0 satisfies permutation requirments in Defini-

tion 15, hence:

By Claim 6, there exists a unique permutation, say 𝑃1, such
that 𝑃1([𝑀𝑓 · e1 + b𝑓 1, . . . ]) = [𝑀𝑔 · e1 + b𝑔1, . . . ].

We repeat this for all e𝑖, 𝑖 ∈ [0, 𝑛]. Then, we have:

𝑃0([b𝑓 1, . . . , b𝑓 𝑘 ]) = [b𝑔1, . . . , b𝑔𝑘 ]
𝑃1([M𝑓 · e1 + b𝑓 1, . . . ]) = [M𝑔 · e1 + b𝑔1, . . . ]
𝑃2([M𝑓 · e2 + b𝑓 1, . . . ]) = [M𝑔 · e2 + b𝑔1, . . . ]
...
𝑃𝑛 ([M𝑓 · e𝑛 + b𝑓 1, . . . ]) = [M𝑔 · e𝑛 + b𝑔1, . . . ]






By Claim 9 (which we prove below), all permutations are

equivalent, 𝑃0 = · · · = 𝑃𝑛.
Now, we prove 𝜏𝑓 (cid:27)𝑃0

𝜏𝑔. By Definition 14, we need to
prove ∀i ∈ N𝑛, 𝑃0(𝜏𝑓 (i)) = 𝜏𝑔 (i). Notice that e𝑖 's are standard
basis vectors, so any i is a linear combination of e𝑖 s:

i = 𝑎0e0 + 𝑎1e1 + 𝑎2e2 + · · · + 𝑎𝑛e𝑛

𝑃0 ∈ 𝑄,

where 𝑄 is the permutation set in 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔.

XXX: assume 𝑛 > 𝑘?

YC: we can
trivially as-
sume 𝑛 > 𝑘,
else the the
kernel func
cannot apply

Lemma 8. For SIMD functions 𝑓 and 𝑔 with well-formed
kernel functions:

∀x, ∀𝑖 ∈ {0, . . . , 𝑛}, 𝑓 (x) [e𝑖 ] = 𝑔(x) [e𝑖 ] =⇒ 𝜏𝑓 (cid:27)𝑃 𝜏𝑔.

(3)

□

where 𝑎𝑖 ∈ R.

𝜏𝑔 (i) = [

𝑛
∑︁

𝑖=1

𝑎𝑖𝑀𝑔1 · e𝑖 + b𝑔1,

𝑛
∑︁

𝑖=1

𝑎𝑖𝑀𝑔2 · e𝑖 + b𝑔2, . . . ]

= 𝑃0([

𝑛
∑︁

𝑖=1

𝑎𝑖𝑀𝑓 1 · e𝑖 + b𝑓 1,

𝑛
∑︁

𝑖=1

= 𝑃0(𝜏𝑓 (i))

𝑎𝑖𝑀𝑓 2 · e𝑖 + b𝑓 2, . . . ])

Therefore, 𝜏𝑓 (cid:27)𝑃0

𝜏𝑔.

□

SOSP '25, October 13–16, 2025, Seoul, Republic of Korea

Yunchi Lu, Youshan Miao, Cheng Tan, Peng Huang, Yi Zhu, Xian Zhang, and Fan Yang

Claim 9. Consider the following 𝑛 + 1 equations:

𝑃0([b𝑓 1, . . . , b𝑓 𝑘 ]) = [b𝑔1, . . . , b𝑔𝑘 ]
𝑃1([M𝑓 · e1 + b𝑓 1, . . . ]) = [M𝑔 · e1 + b𝑔1, . . . ]
𝑃2([M𝑓 · e2 + b𝑓 1, . . . ]) = [M𝑔 · e2 + b𝑔1, . . . ]
...
𝑃𝑛 ([M𝑓 · e𝑛 + b𝑓 1, . . . ]) = [M𝑔 · e𝑛 + b𝑔1, . . . ]

(4)






We claim that

∀𝑘, Equation 4 ⇒ 𝑃0 = · · · = 𝑃𝑛.

Proof. We prove this claim by contradiction. Without loss
of generality, consider 𝑃0 is identity mapping, and assume
𝑃1 ≠ 𝑃0, meaning

(cid:40)

[b𝑓 1, . . . , b𝑓 𝑘 ] = [b𝑔1, . . . , b𝑔𝑘 ]
𝑃1([M𝑓 · e1 + b𝑓 1, . . . ]) = [M𝑔 · e1 + b𝑔1, . . . ]
Next, we denote 𝑃1([M𝑓 ·e1+b𝑓 1, . . . ]) as [M𝑓 ·e1+b𝑃 1(𝑓 1), . . . ],
and replace b𝑔𝑖 with the corresponding b𝑓 𝑖 , so we have:

[M𝑓 · e1 + b𝑃 1(𝑓 1), . . . ] = [M𝑔 · e1 + b𝑓 1, . . . ]

By rearraning this, we get:




b𝑓 1 − b𝑃 1(𝑓 1) = (M𝑓 − M𝑔) · e1
b𝑓 2 − b𝑃 1(𝑓 2) = (M𝑓 − M𝑔) · e1
...
b𝑓 𝑘 − b𝑃 1(𝑓 𝑘 ) = (M𝑓 − M𝑔) · e1
Because 𝑃1 is not identity, by Fact 5, ∃𝑗 ∈ [1, 𝑘], b𝑓 𝑗 −
b𝑃 1(𝑓 𝑗 ) ≠ (cid:174)0 ∈ R𝑚, therefore



[b𝑓 1 [0], . . . ] − [b𝑃 1( 𝑓 1) [0], . . . ]
= [b𝑓 2 [0], . . . ] − [b𝑃 1(𝑓 2) [0], . . . ]
...
= [b𝑓 𝑘 [0], . . . ] − [b𝑃 1( 𝑓 𝑘 ) [0], . . . ]
≠ [0, 0, . . . ]






This means at least one dimension, say 𝑖 ∈ [0, 𝑚), have the

following equation:

b𝑓 1 [𝑖] − b𝑃 1(𝑓 1) [𝑖]
= b𝑓 2 [𝑖] − b𝑃 1(𝑓 2) [𝑖]
...
= b𝑓 𝑘 [𝑖] − b𝑃 1(𝑓 𝑘 ) [𝑖] ≠ 0






Consider the value b𝑓 1 [𝑖] − b𝑃 1(𝑓 1) [𝑖], which must be either
positive or negative (≠ 0). Without loss of generality, assume
it is positive; that is b𝑓 1 [𝑖] > b𝑃 1(𝑓 1) [𝑖]. Since 𝑃1 is a permua-
tion, one can always locate a corresponding term where b𝑃 1(𝑓1 )
appears as the minuend (the left operand of the subtraction).
This yields another inequality b𝑃 1(𝑓 1) [𝑖] > b𝑃 1(𝑓 𝑜 ) [𝑖]. By
repeating this reasoning iteratively, we eventually encounter

a subtraction in which b𝑓 1 [𝑖] appears as the subtrahend (the
right opearand). This results in a a contradition of the form
b𝑓1 [𝑖] > · · · > b𝑓1 [𝑖]. Hence, the contradiction implies that 𝑃1
must be equavalent to 𝑃0.

By applying the above reasoning for all e𝑖 s, we conclude

𝑃0 = · · · = 𝑃𝑛.

□

Next, we prove one of our main theorem below.

Theorem 10. For SIMD functions 𝑓 and 𝑔 with well-formed
kernel functions:

∀x, ∀𝑖 ∈ {0, . . . , 𝑛}, 𝑓 (x) [𝑒𝑖 ] = 𝑔(x) [𝑒𝑖 ] =⇒

∀j, x, 𝑓 (x) [j] = 𝑔(x) [j]

Proof. Given the premise:
• By Lemma 7, 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔.
• By Lemma 8, 𝜏𝑓 (cid:27)𝑃 𝜏𝑔.
• By Equation 3, 𝑃 ∈ 𝑄.

Finally, we prove

𝜃 𝑓 (cid:27)𝑄 𝜃𝑔 ∧ 𝜏𝑓 (cid:27)𝑃 𝜏𝑔 ∧ 𝑃 ∈ 𝑄 =⇒ 𝑓 = 𝑔

∀x, ∀𝑖, 𝑓 (x) [𝑖] = 𝜃 𝑓 (x(𝜏𝑓 (𝑖)))

= 𝜃𝑔 (𝑃 (x[𝜏𝑓 (𝑖)]))
= 𝜃𝑔 (x[𝑃 (𝜏𝑓 (𝑖))])
= 𝜃𝑔 (x[𝜏𝑔 (𝑖)])
= 𝑔(x) [𝑖]

[by Definition 12]
[by 𝜃 𝑓 (cid:27)𝑄 𝜃𝑔 ∧ 𝑃 ∈ 𝑄]
[by tensor indexing rules]
[by 𝜏𝑓 (cid:27)𝑃 𝜏𝑔]

Because for any input x, 𝑓 (x) and 𝑔(x) produce the same
result, therefore 𝑓 = 𝑔.

□

In the following, we prove the shape reduction equavalence

for reductional operations.

Theorem 11. Given reductional functions 𝑓⊙ and 𝑔⊕,

∀x ∈ R2, 𝑓⊙ (x) = 𝑔⊕ (x) =⇒ ∀x ∈ R𝑛, 𝑛 >= 2, 𝑓⊙ (x) = 𝑔⊕ (x).

Proof. We prove the lemma by mathematical induction.

Base case. Consider the base case, 𝑓 (x) = 𝑔(x)| x ∈ R2;
namely, ∀x, x[0] ⊙ x[1] = x[0] ⊕ x[1]. This equality holds
directly from the given premise.

Inductive step. Assume that 𝑓⊙ (x) = 𝑔⊕ (x) holds for ∀x ∈
R𝑘, 𝑘 >= 2. Next, we prove that 𝑓⊙ (x) = 𝑔⊕ (x) also holds for
∀x ∈ 𝑅𝑘+1.

TrainVerify: Equivalence-Based Verification for Distributed LLM Training

SOSP '25, October 13–16, 2025, Seoul, Republic of Korea

We denote x ∈ R𝑘+1 as [x[0..𝑘 − 1], x[𝑘]], then:
𝑓⊙ (x) = 𝑓⊙ (x[0..𝑘 − 1]) ⊙ x[𝑘]
= 𝑔⊕ (x[0..𝑘 − 1]) ⊙ x[𝑘]
= 𝑔⊕ (x[0..𝑘 − 1]) ⊕ x[𝑘]
= 𝑔⊕ (x)

[Definition 13]

[Inductive hypothesis]

[Base case]

[Definition 13]

□

C.4 Connecting theorems to practice
In this section, we prove that TrainVerify's checking algo-
rithm is correct, meaning if our verifier (i.e., Z3) accepts, then
the logical DFG is semantically equivalent to the parallelized
DFG executed by machines.

The key idea is that LLM operators are either SIMD func-
tions (Definition 12) or reductional functions (Definition 13),
or (semantically) combination of the two. TrainVerify veri-
fies equivalence by checking two small sub-tensors from the
outputs of the logical DFG and the parallelized DFG. Next, we
prove these sub-tensors are sufficient to guarantee that all other
corresponding parts of the outputs are identical. For example,
by theorem 10 and theorem 11, verifying the equivalence
of the operator MatMul(𝐴, 𝐵), where 𝐴 ∈ 𝑅 [𝑚,𝑘 ], 𝐵 ∈ 𝑅 [𝑘,𝑛]
with 𝑚, 𝑘, 𝑛 ∈ Z+, can be simplified by verifying the case of
𝑚, 𝑛, 𝑘 = 2.
