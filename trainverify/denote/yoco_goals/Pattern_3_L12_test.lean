/-
  Quick test to see what mk_router 12 produces and what breaks.
  This will help us understand what needs to be implemented manually.
-/
import denote.yoco_goals.Pattern_3

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

-- Try mk_router 12 and see what happens
-- mk_router 12

-- Actually, mk_router depends on mk_nl, which depends on mk_attention, etc.
-- So we need to build from the bottom up.
-- Let's first see what the node indices would be for L12 according to the formulas:

#check (4818 + 54*(12-2))  -- Should be 5358 according to sliding window formula
-- But L12 actual is 5347 (off by 11!)

-- This confirms the formulas don't work for L12.
-- We need hand-written implementations.

end TrainVerify.Denote.GeneratedPatterns
