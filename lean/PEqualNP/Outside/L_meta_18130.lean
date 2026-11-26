import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18130

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [4, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [4, 1]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [5, 11]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.or, [11, 5]⟩,
    ⟨.and, [16, 15]⟩,
    ⟨.and, [19, 20]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.or, [22, 6]⟩,
    ⟨.and, [23, 21]⟩,
    ⟨.and, [6, 22]⟩,
    ⟨.or, [24, 18]⟩,
    ⟨.or, [25, 26]⟩], 27⟩

def isOkGate (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem basis : FanInTwo witness := by
  have hall : witness.gates.all isOkGate = true := by decide
  intro g hg
  have h := List.all_eq_true.mp hall g hg
  simp only [isOkGate, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  cases hop : g.op <;> simp [hop] at h ⊢

theorem check_all : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    witness.eval [b0, b1, b2, b3, b4, b5, b6] = decide (4 ≤ [b0, b1, b2, b3, b4, b5, b6].count true) := by
  decide

theorem ofFn_seven (x : Fin 7 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

theorem eval_eq : ∀ x : Fin 7 → Bool,
    witness.eval (List.ofFn x) = decide (4 ≤ (List.ofFn x).count true) := by
  intro x
  rw [ofFn_seven]
  exact check_all (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

end PEqualNP.Outside.L_meta_18130

theorem PEqualNP.Outside.L_meta_18130 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => decide (4 ≤ (List.ofFn x).count true)) 21) := by
  exact ⟨PEqualNP.Outside.L_meta_18130.witness, PEqualNP.Outside.L_meta_18130.basis, by decide, PEqualNP.Outside.L_meta_18130.eval_eq⟩
