1.能直接引用的lemma千万不要用simp，否则编译速度会非常慢。
2.证明过程中不要中断询问用户意见。
3.实际上"lake build module.File"比"lake env lean"更快，因为有增量缓存。
4.新添加的引理必须放在它依赖的引理之后，否则会报"Unknown identifier"错误。
5.三元组目标（A ∧ B ∧ C）用`refine ⟨?_, ?_, ?_⟩`分解，而不是用`constructor`（只能分两部分）。
6.rewrite时注意顺序：先用`rw [hpm_list]`将PM侧重写为期望形式，再用`rw [← hbw]`应用主引理。
7.dW（权重梯度）和dX（输入梯度）的分布式计算引理是不同的，需要分别证明。
8.`simpa [def] using h`会展开定义，可能导致超时；改用`have h' := h; simp at h'; exact h'`。
9.`rw [h1] at h2`改写假设后，后续使用h2时表达式已变，不要再用原始形式。
10.Shape证明中，`bw_linear_snd_shape'`需要存在性witness，用`⟨a, b, proof⟩`构造。
11.不要写入tmp，没有权限。