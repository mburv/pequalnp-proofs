-- Size-15 fan-in-2 circuit for the three matchings of L-meta-652.
-- Wires 10, 15 and 20 are the three outputs. This is only the upper bound.
import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Scratch652

open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩,
     ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩,
     ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 3]⟩,
     ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [13, 14]⟩,
     ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩,
     ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [18, 19]⟩],
   0⟩

set_option maxHeartbeats 8000000 in
theorem upper :
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧
      ∀ x : Fin 6 → Bool,
        (C.wires (List.ofFn x)).getD 10 false =
          ((x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) ∧
        (C.wires (List.ofFn x)).getD 15 false =
          ((x 0 && x 4) || (x 1 && x 5) || (x 2 && x 3)) ∧
        (C.wires (List.ofFn x)).getD 20 false =
          ((x 0 && x 5) || (x 1 && x 3) || (x 2 && x 4)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> simp
  · decide
  · decide

end PEqualNP.Scratch652
