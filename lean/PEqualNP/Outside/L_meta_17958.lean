import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17958

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
    ∀ (C : Circuit) (a b : ℕ), IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      a ≠ b → a < 26 + C.size → b < 26 + C.size →
      ∃ (D : Circuit) (j : ℕ), D.size ≤ C.size + 1 ∧ IsAO2 26 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        D.output = 26 + j ∧
        D.gates[j]? = some { op := GateOp.and, inputs := [a, b] : Gate } ∧
        ∀ (x : Fin 26 → Bool) (i : ℕ), i < 26 + C.size →
          PEqualNP.BlindGate.wireValue D 26 x i = PEqualNP.BlindGate.wireValue C 26 x i := by
  intro C a b hAO hnd hab ha hb
  let D : Circuit := ⟨C.gates ++ [⟨.and, [a, b]⟩], 26 + C.size⟩
  refine ⟨D, C.size, ?_, ⟨?_, ?_, ?_⟩, ?_, rfl, ?_, ?_⟩
  · simp [D, Circuit.size]
  · intro g hg
    simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · simp
  · intro j hj i hi
    by_cases hlt : j < C.gates.length
    · have hgat : gateAt D j = gateAt C j := by
        simp [D, gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hgat] at hi
      exact hAO.2.1 j hlt i hi
    · simp only [D, List.length_append, List.length_cons, List.length_nil] at hj
      have hjlen : j = C.gates.length := by omega
      subst hjlen
      have hgat : gateAt D C.gates.length = ⟨.and, [a, b]⟩ := by
        simp [D, gateAt, List.getD_eq_getElem?_getD]
      rw [hgat] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [Circuit.size] using ha
      · simpa [Circuit.size] using hb
  · intro g hg
    simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl
  · intro g hg
    simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl
    · exact hnd g hg
    · simp [hab]
  · simp [D, Circuit.size]
  · intro x w hw
    simp only [PEqualNP.BlindGate.wireValue, D, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (C.gates.foldl stepB (List.ofFn x)).length = 26 + C.size := by
      rw [length_foldl_stepB, List.length_ofFn]; rfl
    change ((C.gates.foldl stepB (List.ofFn x)) ++ [_]).getD w false =
      (C.gates.foldl stepB (List.ofFn x)).getD w false
    exact List.getD_append _ _ _ _ (by omega)

end PEqualNP.Outside.L_meta_17958

theorem PEqualNP.Outside.L_meta_17958 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → x2 ≠ x3 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x9.size ≤ x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12) := by
  exact PEqualNP.Outside.L_meta_17958.main_proof
