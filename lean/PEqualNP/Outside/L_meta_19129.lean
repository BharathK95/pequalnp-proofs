import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19129

def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates :=
      [ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] },
        { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 12] } ],
    output := 13 }

end PEqualNP.Outside.L_meta_19129

theorem PEqualNP.Outside.L_meta_19129 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => xor (decide (u = 0)) (decide (v = 0))) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19129.circ, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19129.circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩
