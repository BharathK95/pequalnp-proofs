import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17962

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.MetaComplexity.NestedCover

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem length_foldl_stepB (gs : List Gate) (w : List Bool) :
    (gs.foldl stepB w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepB, List.length_append, List.length_cons, List.length_nil]
    omega

theorem main_proof :
    ∀ (n : ℕ) (D : Circuit) (a b : ℕ), IsAO2 n D →
      (∀ g ∈ D.gates, g.inputs.Nodup) → a ≠ b → a < n + D.size → b < n + D.size →
      let C : Circuit := ⟨D.gates ++ [⟨.and, [a, b]⟩], n + D.size⟩
      IsAO2 n C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        ∀ (x : Fin n → Bool) (w : ℕ), w < n + D.size →
          PEqualNP.BlindGate.wireValue C n x w = PEqualNP.BlindGate.wireValue D n x w := by
  intro n D a b hAO hnd hab ha hb
  dsimp only
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · simp
  · intro j hj i hi
    by_cases hlt : j < D.gates.length
    · have hgat : gateAt ⟨D.gates ++ [⟨.and, [a, b]⟩], n + D.size⟩ j = gateAt D j := by
        simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hgat] at hi
      exact hAO.2.1 j hlt i hi
    · simp only [List.length_append, List.length_cons, List.length_nil] at hj
      have hjlen : j = D.gates.length := by omega
      subst hjlen
      have hgat : gateAt ⟨D.gates ++ [⟨.and, [a, b]⟩], n + D.size⟩ D.gates.length = ⟨.and, [a, b]⟩ := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hgat] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [Circuit.size] using ha
      · simpa [Circuit.size] using hb
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hnd g hg
    · simp [hab]
  · intro x w hw
    simp only [PEqualNP.BlindGate.wireValue, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (D.gates.foldl stepB (List.ofFn x)).length = n + D.size := by
      rw [length_foldl_stepB, List.length_ofFn]; rfl
    change ((D.gates.foldl stepB (List.ofFn x)) ++ [_]).getD w false =
      (D.gates.foldl stepB (List.ofFn x)).getD w false
    exact List.getD_append _ _ _ _ (by omega)

end PEqualNP.Outside.L_meta_17962

theorem PEqualNP.Outside.L_meta_17962 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →       x3 ≠ x4 →         x3 < x1 + x2.size →           x4 < x1 + x2.size →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };             PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), ∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) := by
  exact PEqualNP.Outside.L_meta_17962.main_proof
