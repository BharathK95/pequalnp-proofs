import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18675

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

private lemma main (n : ℕ) (gs : List Gate)
    (h : ∀ i : Fin gs.length,
      let g := gs.getD i.val ⟨GateOp.or, []⟩
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + i.val ∧ b < n + i.val) :
    IsAO2 n ⟨gs, 0⟩ ∧ ∀ g ∈ gs, g.inputs.Nodup := by
  have hi (j : ℕ) (hj : j < gs.length) :
      ((gs[j]'hj).op = GateOp.and ∨ (gs[j]'hj).op = GateOp.or) ∧
      ∃ a b : ℕ, (gs[j]'hj).inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j := by
    have h0 := h ⟨j, hj⟩
    dsimp only at h0
    rwa [List.getD_eq_getElem _ _ hj] at h0
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    exact (hi j hj).1
  · intro j hj w hw
    have hgate : gateAt ⟨gs, 0⟩ j = gs[j]'hj := by
      change gs.getD j _ = _
      exact List.getD_eq_getElem _ _ hj
    rw [hgate] at hw
    obtain ⟨a, b, hab, _, ha, hb⟩ := (hi j hj).2
    rw [hab] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨a, b, hab, _⟩ := (hi j hj).2
    rw [hab]
    rfl
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨a, b, hab, hne, _⟩ := (hi j hj).2
    rw [hab]
    simp [hne]

end PEqualNP.Outside.L_meta_18675


theorem PEqualNP.Outside.L_meta_18675 : (∀ (x1 : ℕ) (x2 : List PEqualNP.CircuitLowerBounds.Gate),   (∀ (x3 : Fin x2.length),       have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.getD ↑x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };       (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x4.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < x1 + ↑x3 ∧ x6 < x1 + ↑x3) →     PEqualNP.TopForm.IsAO2 x1 { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧ ∀ x4 ∈ x2, x4.inputs.Nodup) := by
  exact PEqualNP.Outside.L_meta_18675.main
