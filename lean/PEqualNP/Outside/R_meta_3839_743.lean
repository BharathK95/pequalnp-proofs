import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3839_743
    (hNot2 :
      let f : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size = 14 →
        2 ≤ C.gates.countP (fun g => g.op.eval [false]) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) ≠ f x)
    (hAnd :
      let f : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let row : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size = 13 →
        C.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
        ∀ i j : Fin 10, i < j →
        ∃ x : Fin 9 → Bool,
          C.eval (row x ++ [(row x).getD i.val false && (row x).getD j.val false]) ≠ f x)
    (hOr3 :
      let f : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let row : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size = 13 →
        C.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
        ∀ i : Fin 9,
        ∃ x : Fin 9 → Bool,
          C.eval (row x ++ [x i || (x 0 || x 6)]) ≠ f x)
    (hOr2 :
      let f : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5
      let row : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size = 13 →
        C.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
        ∀ i j : Fin 9, i < j →
        ∃ x : Fin 9 → Bool,
          C.eval (row x ++ [x i || x j]) ≠ f x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → ∀ (x6 x7 : Fin (10 : ℕ)) (x8 : Bool), x6 < x7 → ∃ (x10 : Fin (9 : ℕ) → Bool), x3.eval (x2 x10 ++ [if x8 = Bool.true then (x2 x10).getD (↑x6) Bool.false || (x2 x10).getD (↑x7) Bool.false else (x2 x10).getD (↑x6) Bool.false && (x2 x10).getD (↑x7) Bool.false]) ≠ x1 x10 := by
  dsimp only
  intro C hC hsz i j disj hij
  by_cases hnot : 2 ≤ C.gates.countP (fun g => g.op.eval [false])
  · let g0 : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨if disj then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [i.val, j.val]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: C.gates, C.output⟩
    have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      simp only [D, List.mem_cons] at hg
      rcases hg with rfl | hg
      · cases disj <;> simp [g0]
      · exact hC g hg
    have hDsz : D.size = 14 := congrArg Nat.succ hsz
    have hDnot : 2 ≤ D.gates.countP (fun g => g.op.eval [false]) := by
      have hg0 : g0.op.eval [false] = false := by cases disj <;> rfl
      change 2 ≤ (g0 :: C.gates).countP (fun g => g.op.eval [false])
      rw [List.countP_cons, hg0]
      exact hnot
    obtain ⟨x, hx⟩ := hNot2 D hDfan hDsz hDnot
    refine ⟨x, ?_⟩
    have heval : D.eval (List.ofFn x ++ [x 0 || x 6]) =
        C.eval ((List.ofFn x ++ [x 0 || x 6]) ++
          [if disj = true then (List.ofFn x ++ [x 0 || x 6]).getD i.val false || (List.ofFn x ++ [x 0 || x 6]).getD j.val false
           else (List.ofFn x ++ [x 0 || x 6]).getD i.val false && (List.ofFn x ++ [x 0 || x 6]).getD j.val false]) := by
      cases disj with
      | false =>
        change C.eval ((List.ofFn x ++ [x 0 || x 6]) ++
          [((List.ofFn x ++ [x 0 || x 6]).getD i.val false && ((List.ofFn x ++ [x 0 || x 6]).getD j.val false && true))]) =
          C.eval ((List.ofFn x ++ [x 0 || x 6]) ++
          [((List.ofFn x ++ [x 0 || x 6]).getD i.val false && (List.ofFn x ++ [x 0 || x 6]).getD j.val false)])
        rw [Bool.and_true]
      | true =>
        change C.eval ((List.ofFn x ++ [x 0 || x 6]) ++
          [((List.ofFn x ++ [x 0 || x 6]).getD i.val false || ((List.ofFn x ++ [x 0 || x 6]).getD j.val false || false))]) =
          C.eval ((List.ofFn x ++ [x 0 || x 6]) ++
          [((List.ofFn x ++ [x 0 || x 6]).getD i.val false || (List.ofFn x ++ [x 0 || x 6]).getD j.val false)])
        rw [Bool.or_false]
    rwa [← heval]
  · have hle1 : C.gates.countP (fun g => g.op.eval [false]) ≤ 1 := by omega
    cases disj with
    | false =>
      simpa using hAnd C hC hsz hle1 i j hij
    | true =>
      have get_lt (x : Fin 9 → Bool) (k : Fin 9) :
          (List.ofFn x ++ [x 0 || x 6]).getD k.val false = x k := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
        simp only [List.getElem?_ofFn, k.isLt, dite_true, Option.getD_some]
      have get_9 (x : Fin 9 → Bool) :
          (List.ofFn x ++ [x 0 || x 6]).getD 9 false = (x 0 || x 6) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      by_cases hj9 : j.val = 9
      · have hi9 : i.val < 9 := by
          have : i.val < j.val := hij
          omega
        obtain ⟨x, hx⟩ := hOr3 C hC hsz hle1 ⟨i.val, hi9⟩
        refine ⟨x, ?_⟩
        simp only [ite_true]
        rw [hj9, get_9 x]
        have hi_eq : (List.ofFn x ++ [x 0 || x 6]).getD i.val false = x ⟨i.val, hi9⟩ := get_lt x ⟨i.val, hi9⟩
        rw [hi_eq]
        exact hx
      · have hjlt : j.val < 9 := by omega
        have hilt : i.val < 9 := by
          have : i.val < j.val := hij
          omega
        obtain ⟨x, hx⟩ := hOr2 C hC hsz hle1 ⟨i.val, hilt⟩ ⟨j.val, hjlt⟩ hij
        refine ⟨x, ?_⟩
        simp only [ite_true]
        have hi_eq : (List.ofFn x ++ [x 0 || x 6]).getD i.val false = x ⟨i.val, hilt⟩ := get_lt x ⟨i.val, hilt⟩
        have hj_eq : (List.ofFn x ++ [x 0 || x 6]).getD j.val false = x ⟨j.val, hjlt⟩ := get_lt x ⟨j.val, hjlt⟩
        rw [hi_eq, hj_eq]
        exact hx
