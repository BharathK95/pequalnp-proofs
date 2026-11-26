import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19705_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [11, 18]⟩], 19⟩

theorem ok_gates : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19705_aux

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_meta_19705 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16254033 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_19705_aux.circuit, PEqualNP.Outside.L_meta_19705_aux.ok_gates, by decide, by decide +kernel⟩
