import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20029_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 15]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [6, 18]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [19, 21]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [11, 20]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [7, 22]⟩, ⟨.or, [11, 29]⟩, ⟨.or, [1, 27]⟩, ⟨.and, [6, 21]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [18, 26]⟩, ⟨.and, [24, 31]⟩, ⟨.or, [21, 28]⟩, ⟨.and, [26, 30]⟩, ⟨.or, [33, 35]⟩, ⟨.and, [25, 36]⟩, ⟨.or, [23, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [37, 41]⟩], 42⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20029_aux

set_option maxRecDepth 200000 in
theorem PEqualNP.Outside.L_meta_20029 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11624384703659074185 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  exact ⟨PEqualNP.Outside.L_meta_20029_aux.circuit, PEqualNP.Outside.L_meta_20029_aux.mono, by decide, by decide +kernel⟩
