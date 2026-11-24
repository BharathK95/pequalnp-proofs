import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1676_3 :
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 10 D →
      (∀ g ∈ D.gates, g.inputs.Nodup) →
      D.size = 14 →
      (∃ h : PEqualNP.CircuitLowerBounds.Gate, h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        D.gates.filter (fun g => decide (4 ∈ g.inputs)) = [h]) →
      (∃ g ∈ D.gates, 0 ∈ g.inputs) →
      (∀ i ∈ ([0, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2) →
      (∀ i : Fin 9, (D.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3) →
      ¬ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 || y 4]) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))) →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
      (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      (∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      D.size = 14 →
      (∃ h : PEqualNP.CircuitLowerBounds.Gate, h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        D.gates.filter (fun g => decide (4 ∈ g.inputs)) = [h]) →
      (∃ g ∈ D.gates, 0 ∈ g.inputs) →
      (∀ i ∈ ([0, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2) →
      (∀ i : Fin 9, (D.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3) →
      ¬ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 || y 4]) = ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5))) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro hDel4 hDel0 hMono14 hNot14 C hCfan hFirst hCfun
  by_contra hlt16
  have hCsz : C.size ≤ 15 := by omega
  let F9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let F8d4 : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let F8d0 : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)
  have hCev : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) = F9 y := fun y => congrFun hCfun y
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have list_le2 : ∀ l : List ℕ, l.length ≤ 2 → l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
    intro l hl
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨a, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
    · simp at hl
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro w; simp
    | append_singleton gs g ih =>
      intro w
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((gs.foldl stepW w) ++ [_]).length = w.length + (gs ++ [g]).length
      simp only [List.length_append, List.length_cons, List.length_nil, ih]
      omega
  have getD_snoc_lt : ∀ {α : Type} (l : List α) (a d : α) (i : ℕ), i < l.length →
      (l ++ [a]).getD i d = l.getD i d := by
    intro α l a d i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ {α : Type} (l : List α) (a d : α),
      (l ++ [a]).getD l.length d = a := by
    intro α l a d
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length)]
    simp
  have getD_ge : ∀ {α : Type} (l : List α) (d : α) (i : ℕ), l.length ≤ i →
      l.getD i d = d := by
    intro α l d i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro _ _ _; rfl
    | append_singleton gs g ih =>
      intro w i hi
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlt : i < (gs.foldl stepW w).length := by rw [foldl_len]; omega
      change ((gs.foldl stepW w) ++ [_]).getD i false = w.getD i false
      rw [getD_snoc_lt _ _ _ i hlt]
      exact ih w i hi
  have filter_le_card : ∀ (gs : List Gate) (P : Gate → Bool) (S : Finset ℕ),
      (∀ j < gs.length, ∀ g, gs[j]? = some g → P g = true → j ∈ S) →
      (gs.filter P).length ≤ S.card := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => intro _ _ _; simp
    | append_singleton gs g ih =>
      intro P S hS
      rw [List.filter_append]
      cases hp : P g
      · have hnil : [g].filter P = [] := by simp [hp]
        rw [hnil, List.append_nil]
        apply ih P S
        intro j hj g' hgj hpg'
        apply hS j (by simp; omega) g'
        · rw [List.getElem?_append_left hj]; exact hgj
        · exact hpg'
      · have hsn : [g].filter P = [g] := by simp [hp]
        rw [hsn, List.length_append, List.length_singleton]
        have hmem : gs.length ∈ S := by
          apply hS gs.length (by simp) g
          · rw [List.getElem?_append_right (le_refl gs.length)]; simp
          · exact hp
        have hsub := ih P (S.erase gs.length) (by
          intro j hj g' hgj hpg'
          refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
          apply hS j (by simp; omega) g'
          · rw [List.getElem?_append_left hj]; exact hgj
          · exact hpg')
        have hcard : (S.erase gs.length).card + 1 = S.card := Finset.card_erase_add_one hmem
        omega
  -- General circuit simplifier & constant-propagation pass with dropped-gate accounting
  have simplify : ∀ (m n_in n_out : ℕ)
      (w_in w_out : (Fin m → Bool) → List Bool)
      (init : List (ℕ ⊕ Bool)) (gs : List Gate),
      (∀ y, (w_in y).length = n_in) →
      (∀ y, (w_out y).length = n_out) →
      init.length = n_in →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i < n_in, ∀ y : Fin m → Bool,
        Sum.elim (fun w => (w_out y).getD w false) id (init.getD i (Sum.inr false)) = (w_in y).getD i false) →
      (∀ i < n_in, ∀ w, init.getD i (Sum.inr false) = Sum.inl w → w < n_out) →
      ∃ (gs' : List Gate) (env : List (ℕ ⊕ Bool)) (dropped : Finset ℕ),
        env.length = n_in + gs.length ∧
        (∀ i < n_in, env.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
        (∀ j ∈ dropped, j < gs.length) ∧
        gs'.length + dropped.card ≤ gs.length ∧
        (∀ j < gs.length, ∀ g : Gate, gs[j]? = some g →
          ((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
           ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a ∈ g.inputs, a < n_in + j ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b)) →
          j ∈ dropped) ∧
        (∀ j < gs.length, ∀ g : Gate, gs[j]? = some g →
          ((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
           (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a < n_in + j ∧ env.getD a (Sum.inr false) = Sum.inr false)) →
          ∃ b, env.getD (n_in + j) (Sum.inr false) = Sum.inr b) ∧
        (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        (∀ j < gs'.length, ∀ i ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
        (∀ g ∈ gs', (g.op = GateOp.not → g.inputs.length = 1) ∧
          (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
        (∀ k < env.length, ∀ w, env.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs'.length) ∧
        (∀ k < env.length, ∀ y : Fin m → Bool,
          Sum.elim (fun w => (gs'.foldl stepW (w_out y)).getD w false) id (env.getD k (Sum.inr false)) =
            (gs.foldl stepW (w_in y)).getD k false) := by
    intro m n_in n_out w_in w_out init gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ _ hlen _ heval hbd
      refine ⟨[], init, ∅, by simp [hlen], fun _ _ => rfl, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ hj; simp at hj
      · intro _ hj; simp at hj
      · intro _ hj; simp at hj
      · intro _ hg; simp at hg
      · intro _ hj; simp at hj
      · intro _ hg; simp at hg
      · intro k hk w hw; rw [hlen] at hk; simpa using hbd k hk w hw
      · intro k hk y; rw [hlen] at hk; simpa using heval k hk y
    | append_singleton gs g ih =>
      intro hwin hwout hlen hfan heval hbd
      have hfan_gs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
        fun h hh => hfan h (List.mem_append_left _ hh)
      have hfan_g : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
        hfan g (List.mem_append_right _ (List.mem_singleton_self g))
      obtain ⟨gs', env, dropped, henv_len, hinit_eq, hdrop_lt, hsz, hdrop_c, hprop_c,
        hgs'_fan, hgs'_rb, hgs'_clean, hgs'_bd, hgs'_ev⟩ :=
        ih hwin hwout hlen hfan_gs heval hbd
      let lookup : ℕ → ℕ ⊕ Bool := fun i =>
        if i < env.length then env.getD i (Sum.inr false) else Sum.inr false
      have lookup_bd : ∀ i w, lookup i = Sum.inl w → w < n_out + gs'.length := by
        intro i w hw
        dsimp [lookup] at hw
        by_cases hi : i < env.length
        · simp only [hi, ↓reduceIte] at hw; exact hgs'_bd i hi w hw
        · simp only [hi, ↓reduceIte] at hw; cases hw
      have lookup_ev : ∀ i (y : Fin m → Bool),
          Sum.elim (fun w => (gs'.foldl stepW (w_out y)).getD w false) id (lookup i) =
            (gs.foldl stepW (w_in y)).getD i false := by
        intro i y
        dsimp [lookup]
        by_cases hi : i < env.length
        · simp only [hi, ↓reduceIte]; exact hgs'_ev i hi y
        · simp only [hi, ↓reduceIte]
          have hglen : (gs.foldl stepW (w_in y)).length = env.length := by
            rw [foldl_len, hwin y, henv_len]
          symm; exact getD_ge _ false i (by omega)
      -- Helper: finish with NO new gate added (insert gs.length into dropped)
      have finish_no_add : ∀ (v_out : ℕ ⊕ Bool),
          (((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + gs.length ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
            (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a < n_in + gs.length ∧ env.getD a (Sum.inr false) = Sum.inr false)) →
            ∃ b, v_out = Sum.inr b) →
          (∀ w, v_out = Sum.inl w → w < n_out + gs'.length) →
          (∀ y : Fin m → Bool,
            Sum.elim (fun w => (gs'.foldl stepW (w_out y)).getD w false) id v_out =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepW (w_in y)).getD i false)) →
          ∃ (gs1 : List Gate) (env1 : List (ℕ ⊕ Bool)) (drop1 : Finset ℕ),
            env1.length = n_in + (gs ++ [g]).length ∧
            (∀ i < n_in, env1.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
            (∀ j ∈ drop1, j < (gs ++ [g]).length) ∧
            gs1.length + drop1.card ≤ (gs ++ [g]).length ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b)) →
              j ∈ drop1) ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               (h.op = GateOp.and ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ env1.getD a (Sum.inr false) = Sum.inr false)) →
              ∃ b, env1.getD (n_in + j) (Sum.inr false) = Sum.inr b) ∧
            (∀ h ∈ gs1, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
            (∀ j < gs1.length, ∀ i ∈ (gs1.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
            (∀ h ∈ gs1, (h.op = GateOp.not → h.inputs.length = 1) ∧
              (h.op ≠ GateOp.not → h.inputs.length = 2 ∧ h.inputs.Nodup)) ∧
            (∀ k < env1.length, ∀ w, env1.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs1.length) ∧
            (∀ k < env1.length, ∀ y : Fin m → Bool,
              Sum.elim (fun w => (gs1.foldl stepW (w_out y)).getD w false) id (env1.getD k (Sum.inr false)) =
                ((gs ++ [g]).foldl stepW (w_in y)).getD k false) := by
        intro v_out hv_prop hv_bd hv_ev
        refine ⟨gs', env ++ [v_out], insert gs.length dropped, ?_, ?_, ?_, ?_, ?_, ?_, hgs'_fan, hgs'_rb, hgs'_clean, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, henv_len]; omega
        · intro i hi; rw [getD_snoc_lt env v_out _ i (by omega)]; exact hinit_eq i hi
        · intro j hj
          simp only [List.length_append, List.length_cons, List.length_nil]
          rcases Finset.mem_insert.mp hj with rfl | hjd
          · omega
          · have := hdrop_lt j hjd; omega
        · have hnotmem : gs.length ∉ dropped := fun hm => by have := hdrop_lt gs.length hm; omega
          rw [Finset.card_insert_of_notMem hnotmem]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            refine Finset.mem_insert_of_mem (hdrop_c j hlt h hgj ?_)
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨hao, a, hain, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb
              exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb
              exact Or.inr ⟨hao, a, hain, halt, b, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            exact Finset.mem_insert_self _ _
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            rw [getD_snoc_lt env v_out _ (n_in + j) (by omega)]
            apply hprop_c j hlt h hgj
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb
              exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb
              exact Or.inr ⟨ha, a, hain, halt, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            rw [← henv_len, getD_snoc_eq]
            apply hv_prop
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb
              exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env v_out _ a (by omega)] at hb
              exact Or.inr ⟨ha, a, hain, halt, hb⟩
        · intro k hk w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env v_out _ k hlt] at hw; exact hgs'_bd k hlt w hw
          · have hkeq : k = env.length := by omega
            subst hkeq; rw [getD_snoc_eq] at hw; exact hv_bd w hw
        · intro k hk y
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hglen : (gs.foldl stepW (w_in y)).length = env.length := by rw [foldl_len, hwin y, henv_len]
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env v_out _ k hlt]
            change _ = ((gs.foldl stepW (w_in y)) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega)]
            exact hgs'_ev k hlt y
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq, hv_ev y, ← hglen]
            change _ = ((gs.foldl stepW (w_in y)) ++ [_]).getD (gs.foldl stepW (w_in y)).length false
            rw [getD_snoc_eq]
      -- Helper: finish with ONE new clean gate `g_new` added
      have finish_add : ∀ (g_new : Gate),
          ¬ ((g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in + gs.length ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b) ∨
             ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a ∈ g.inputs, a < n_in + gs.length ∧ ∃ b, env.getD a (Sum.inr false) = Sum.inr b)) →
          (g_new.op = GateOp.and ∨ g_new.op = GateOp.or ∨ g_new.op = GateOp.not) ∧ g_new.inputs.length ≤ 2 →
          (∀ i ∈ g_new.inputs, i < n_out + gs'.length) →
          (g_new.op = GateOp.not → g_new.inputs.length = 1) ∧
            (g_new.op ≠ GateOp.not → g_new.inputs.length = 2 ∧ g_new.inputs.Nodup) →
          (∀ y : Fin m → Bool,
            g_new.op.eval (g_new.inputs.map fun i => (gs'.foldl stepW (w_out y)).getD i false) =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepW (w_in y)).getD i false)) →
          ∃ (gs1 : List Gate) (env1 : List (ℕ ⊕ Bool)) (drop1 : Finset ℕ),
            env1.length = n_in + (gs ++ [g]).length ∧
            (∀ i < n_in, env1.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
            (∀ j ∈ drop1, j < (gs ++ [g]).length) ∧
            gs1.length + drop1.card ≤ (gs ++ [g]).length ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b)) →
              j ∈ drop1) ∧
            (∀ j < (gs ++ [g]).length, ∀ h : Gate, (gs ++ [g])[j]? = some h →
              ((h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in + j ∧ ∃ b, env1.getD a (Sum.inr false) = Sum.inr b) ∨
               (h.op = GateOp.and ∧ ∃ a ∈ h.inputs, a < n_in + j ∧ env1.getD a (Sum.inr false) = Sum.inr false)) →
              ∃ b, env1.getD (n_in + j) (Sum.inr false) = Sum.inr b) ∧
            (∀ h ∈ gs1, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
            (∀ j < gs1.length, ∀ i ∈ (gs1.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
            (∀ h ∈ gs1, (h.op = GateOp.not → h.inputs.length = 1) ∧
              (h.op ≠ GateOp.not → h.inputs.length = 2 ∧ h.inputs.Nodup)) ∧
            (∀ k < env1.length, ∀ w, env1.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs1.length) ∧
            (∀ k < env1.length, ∀ y : Fin m → Bool,
              Sum.elim (fun w => (gs1.foldl stepW (w_out y)).getD w false) id (env1.getD k (Sum.inr false)) =
                ((gs ++ [g]).foldl stepW (w_in y)).getD k false) := by
        intro g_new hno_c hgn_fan hgn_rb hgn_clean hgn_ev
        refine ⟨gs' ++ [g_new], env ++ [Sum.inl (n_out + gs'.length)], dropped, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, henv_len]; omega
        · intro i hi; rw [getD_snoc_lt env _ _ i (by omega)]; exact hinit_eq i hi
        · intro j hj; simp only [List.length_append, List.length_cons, List.length_nil]; have := hdrop_lt j hj; omega
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            apply hdrop_c j hlt h hgj
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨hao, a, hain, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨hao, a, hain, halt, b, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            exfalso; apply hno_c
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨hao, a, hain, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨hao, a, hain, halt, b, hb⟩
        · intro j hj h hgj hcond
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs.length
          · rw [List.getElem?_append_left hlt] at hgj
            rw [getD_snoc_lt env _ _ (n_in + j) (by omega)]
            apply hprop_c j hlt h hgj
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨ha, a, hain, halt, hb⟩
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getElem?_append_right (le_refl gs.length)] at hgj
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hgj
            subst hgj
            exfalso; apply hno_c
            rcases hcond with ⟨hn, a, hhd, halt, b, hb⟩ | ⟨ha, a, hain, halt, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inl ⟨hn, a, hhd, halt, b, hb⟩
            · rw [getD_snoc_lt env _ _ a (by omega)] at hb; exact Or.inr ⟨Or.inl ha, a, hain, halt, false, hb⟩
        · intro h hh
          rcases List.mem_append.mp hh with h1 | h2
          · exact hgs'_fan h h1
          · rw [List.mem_singleton.mp h2]; exact hgn_fan
        · intro j hj i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs'.length
          · rw [getD_snoc_lt gs' g_new _ j hlt] at hi; exact hgs'_rb j hlt i hi
          · have hjeq : j = gs'.length := by omega
            subst hjeq; rw [getD_snoc_eq] at hi; exact hgn_rb i hi
        · intro h hh
          rcases List.mem_append.mp hh with h1 | h2
          · exact hgs'_clean h h1
          · rw [List.mem_singleton.mp h2]; exact hgn_clean
        · intro k hk w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hk ⊢
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env _ _ k hlt] at hw; have := hgs'_bd k hlt w hw; omega
          · have hkeq : k = env.length := by omega
            subst hkeq; rw [getD_snoc_eq] at hw; injection hw with hw'; omega
        · intro k hk y
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hglen : (gs.foldl stepW (w_in y)).length = env.length := by rw [foldl_len, hwin y, henv_len]
          have hglen' : (gs'.foldl stepW (w_out y)).length = n_out + gs'.length := by rw [foldl_len, hwout y]
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env _ _ k hlt]
            change _ = ((gs.foldl stepW (w_in y)) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k (by omega)]
            have hprev := hgs'_ev k hlt y
            rcases hval : env.getD k (Sum.inr false) with w | b
            · rw [hval] at hprev
              dsimp only [Sum.elim_inl] at hprev ⊢
              have hwlt : w < (gs'.foldl stepW (w_out y)).length := by
                have := hgs'_bd k hlt w hval; omega
              change ((gs'.foldl stepW (w_out y)) ++ [_]).getD w false = _
              rw [getD_snoc_lt _ _ _ w hwlt]
              exact hprev
            · rw [hval] at hprev; exact hprev
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq]
            dsimp only [Sum.elim_inl]
            rw [← hglen', ← hglen]
            change ((gs'.foldl stepW (w_out y)) ++ [_]).getD (gs'.foldl stepW (w_out y)).length false =
              ((gs.foldl stepW (w_in y)) ++ [_]).getD (gs.foldl stepW (w_in y)).length false
            rw [getD_snoc_eq, getD_snoc_eq]
            exact hgn_ev y
      -- Case split on g.op
      rcases hfan_g.1 with hop | hop | hop
      · -- g.op = GateOp.and
        rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr true) (fun _ => ⟨true, rfl⟩) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_and]; rfl)
        · refine finish_no_add (lookup a) ?_ (lookup_bd a) (fun y => by
            rw [hop, hins, eval_and]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact lookup_ev a y)
          intro hc
          rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
          · rw [hop] at hn; exact GateOp.noConfusion hn
          · rw [hins, List.mem_singleton] at hc_in
            subst hc_in
            refine ⟨false, ?_⟩
            dsimp [lookup]
            have hlt : c < env.length := by omega
            simp only [hlt, ↓reduceIte, hcf]
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                refine finish_no_add (Sum.inl w1) ?_
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl] at ha hb ⊢
                    rw [← ha, ← hb, Bool.and_self])
                intro hc
                exfalso
                rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hins] at hc_in
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                  have hlt : c < env.length := by omega
                  rcases hc_in with rfl | rfl
                  · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                  · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hcf] at hub; cases hub
              · have hno_c : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
                    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc)) := by
                  intro hc
                  rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, bc, hbc⟩
                  · rw [hop] at hn; exact GateOp.noConfusion hn
                  · rw [hins] at hc_in
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                    have hlt : c < env.length := by omega
                    rcases hc_in with rfl | rfl
                    · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbc] at hua; cases hua
                    · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hbc] at hub; cases hub
                refine finish_add ⟨GateOp.and, [w1, w2]⟩ hno_c ⟨Or.inl rfl, le_refl 2⟩ ?_ ?_ ?_
                · intro i hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with h | h
                  · rw [h]; exact lookup_bd a w1 hua
                  · rw [h]; exact lookup_bd b w2 hub
                · exact ⟨fun h => GateOp.noConfusion h, fun _ => ⟨rfl, by simp [heq]⟩⟩
                · intro y
                  rw [hop, hins]
                  simp only [eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl] at ha hb
                  rw [ha, hb]
            · cases b2
              · exact finish_no_add (Sum.inr false) (fun _ => ⟨false, rfl⟩) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_and]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.and_false])
              · refine finish_no_add (Sum.inl w1) ?_
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_and]
                    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                    rw [← ha, ← hb, Bool.and_true])
                intro hc; exfalso
                rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
                · rw [hop] at hn; exact GateOp.noConfusion hn
                · rw [hins] at hc_in
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                  have hlt : c < env.length := by omega
                  rcases hc_in with rfl | rfl
                  · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                  · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hcf] at hub; cases hub
          · cases b1
            · exact finish_no_add (Sum.inr false) (fun _ => ⟨false, rfl⟩) (fun _ h => by cases h) (fun y => by
                rw [hop, hins, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha ⊢
                rw [← ha, Bool.false_and])
            · refine finish_no_add (lookup b) ?_ (lookup_bd b) (fun y => by
                rw [hop, hins, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.true_and]
                exact lookup_ev b y)
              intro hc
              rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, hcf⟩
              · rw [hop] at hn; exact GateOp.noConfusion hn
              · rw [hins] at hc_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                have hlt : c < env.length := by omega
                rcases hc_in with rfl | rfl
                · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hcf] at hua; cases hua
                · refine ⟨false, ?_⟩; dsimp [lookup]; simp only [hlt, ↓reduceIte, hcf]
      · -- g.op = GateOp.or
        have hor_vac : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
            (g.op = GateOp.and ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ env.getD c (Sum.inr false) = Sum.inr false)) := by
          intro hc
          rcases hc with ⟨hn, _⟩ | ⟨ha, _⟩ <;> (rw [hop] at *; exact GateOp.noConfusion (by assumption))
        rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr false) (fun hc => False.elim (hor_vac hc)) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_or]; rfl)
        · exact finish_no_add (lookup a) (fun hc => False.elim (hor_vac hc)) (lookup_bd a) (fun y => by
            rw [hop, hins, eval_or]
            simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact lookup_ev a y)
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                exact finish_no_add (Sum.inl w1) (fun hc => False.elim (hor_vac hc))
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl] at ha hb ⊢
                    rw [← ha, ← hb, Bool.or_self])
              · have hno_c : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
                    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc)) := by
                  intro hc
                  rcases hc with ⟨hn, _⟩ | ⟨_, c, hc_in, hc_lt, bc, hbc⟩
                  · rw [hop] at hn; exact GateOp.noConfusion hn
                  · rw [hins] at hc_in
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                    have hlt : c < env.length := by omega
                    rcases hc_in with rfl | rfl
                    · dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbc] at hua; cases hua
                    · dsimp [lookup] at hub; simp only [hlt, ↓reduceIte, hbc] at hub; cases hub
                refine finish_add ⟨GateOp.or, [w1, w2]⟩ hno_c ⟨Or.inr (Or.inl rfl), le_refl 2⟩ ?_ ?_ ?_
                · intro i hi
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with h | h
                  · rw [h]; exact lookup_bd a w1 hua
                  · rw [h]; exact lookup_bd b w2 hub
                · exact ⟨fun h => GateOp.noConfusion h, fun _ => ⟨rfl, by simp [heq]⟩⟩
                · intro y
                  rw [hop, hins]
                  simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl] at ha hb
                  rw [ha, hb]
            · cases b2
              · exact finish_no_add (Sum.inl w1) (fun hc => False.elim (hor_vac hc))
                  (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                    rw [hop, hins, eval_or]
                    simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                    have ha := lookup_ev a y; rw [hua] at ha
                    have hb := lookup_ev b y; rw [hub] at hb
                    dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                    rw [← ha, ← hb, Bool.or_false])
              · exact finish_no_add (Sum.inr true) (fun hc => False.elim (hor_vac hc)) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.or_true])
          · cases b1
            · exact finish_no_add (lookup b) (fun hc => False.elim (hor_vac hc)) (lookup_bd b) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.false_or]
                exact lookup_ev b y)
            · exact finish_no_add (Sum.inr true) (fun hc => False.elim (hor_vac hc)) (fun _ h => by cases h) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha ⊢
                rw [← ha, Bool.true_or])
      · -- g.op = GateOp.not
        rcases hins : g.inputs with _ | ⟨a, rest⟩
        · exact finish_no_add (Sum.inr true) (fun _ => ⟨true, rfl⟩) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_not]; rfl)
        · rcases hua : lookup a with w1 | b1
          · have hno_c : ¬ ((g.op = GateOp.not ∧ ∃ c, g.inputs.head? = some c ∧ c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc) ∨
                ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ c ∈ g.inputs, c < n_in + gs.length ∧ ∃ bc, env.getD c (Sum.inr false) = Sum.inr bc)) := by
              intro hc
              rcases hc with ⟨_, c, hc_hd, hc_lt, bc, hbc⟩ | ⟨hao, _⟩
              · rw [hins] at hc_hd
                simp only [List.head?_cons, Option.some.injEq] at hc_hd
                rw [hc_hd] at hua
                have hlt : c < env.length := by omega
                dsimp [lookup] at hua; simp only [hlt, ↓reduceIte, hbc] at hua; cases hua
              · rcases hao with h1 | h1 <;> (rw [hop] at h1; exact GateOp.noConfusion h1)
            refine finish_add ⟨GateOp.not, [w1]⟩ hno_c ⟨Or.inr (Or.inr rfl), by simp⟩ ?_ ?_ ?_
            · intro i hi; rw [List.mem_singleton.mp hi]; exact lookup_bd a w1 hua
            · exact ⟨fun _ => rfl, fun h => False.elim (h rfl)⟩
            · intro y
              rw [hop, hins]
              simp only [eval_not, List.map_cons, List.headD_cons]
              have ha := lookup_ev a y; rw [hua] at ha
              dsimp only [Sum.elim_inl] at ha
              rw [ha]
          · exact finish_no_add (Sum.inr (!b1)) (fun _ => ⟨!b1, rfl⟩) (fun _ h => by cases h) (fun y => by
              rw [hop, hins, eval_not]
              simp only [List.map_cons, List.headD_cons]
              have ha := lookup_ev a y; rw [hua] at ha
              dsimp only [Sum.elim_inr, id_eq] at ha ⊢
              rw [← ha])
  -- Step 1: Peel first gate of C (which computes wire 9 = y 0 || y 4) and clean the tail
  rcases hCg : C.gates with _ | ⟨g0, tail⟩
  · have hbad := hFirst (fun _ => true)
    change (C.gates.foldl stepW (List.ofFn (fun _ : Fin 9 => true))).getD 9 false = true at hbad
    rw [hCg, List.foldl_nil] at hbad
    rw [getD_ge _ false 9 (by simp)] at hbad
    exact Bool.noConfusion hbad
  have hstep0 : ∀ y : Fin 9 → Bool,
      stepW (List.ofFn y) g0 = List.ofFn y ++ [y 0 || y 4] := by
    intro y
    have h := hFirst y
    change (C.gates.foldl stepW (List.ofFn y)).getD 9 false = (y 0 || y 4) at h
    rw [hCg, List.foldl_cons] at h
    have hlen0 : (stepW (List.ofFn y) g0).length = 10 := by
      change ((List.ofFn y) ++ [_]).length = 10
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
    rw [foldl_getD_lt tail _ 9 (by omega)] at h
    have hval : g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) = (y 0 || y 4) := by
      have h9 := getD_snoc_eq (List.ofFn y) (g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)) false
      rw [List.length_ofFn] at h9
      exact h9.symm.trans h
    change List.ofFn y ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false)] = _
    rw [hval]
  have htail_ev : ∀ y : Fin 9 → Bool,
      (tail.foldl stepW (List.ofFn y ++ [y 0 || y 4])).getD C.output false = F9 y := by
    intro y
    have hc := hCev y
    change (C.gates.foldl stepW (List.ofFn y)).getD C.output false = F9 y at hc
    rw [hCg, List.foldl_cons, hstep0 y] at hc
    exact hc
  have htail_len : tail.length ≤ 14 := by
    change C.gates.length ≤ 15 at hCsz
    rw [hCg, List.length_cons] at hCsz
    omega
  have htail_fan : ∀ g ∈ tail, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hCfan g (by rw [hCg]; exact List.mem_cons_of_mem _ hg)
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  let init10 : List (ℕ ⊕ Bool) := List.ofFn (fun i : Fin 10 => Sum.inl i.val)
  obtain ⟨gs1, env1, drop1, henv1_len, _, _, hsz1, _, _, hgs1_fan, hgs1_rb, hgs1_clean, _, hgs1_ev⟩ :=
    simplify 9 10 10 (fun y => List.ofFn y ++ [y 0 || y 4]) (fun y => List.ofFn y ++ [y 0 || y 4])
      init10 tail (by intro y; simp) (by intro y; simp) (by simp [init10]) htail_fan
      (by
        intro i hi y
        simp only [init10, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.elim_inl])
      (by
        intro i hi w hw
        simp only [init10, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.inl.injEq] at hw
        omega)
  have hCout_lt : C.output < env1.length := by
    by_contra hge
    have h1 := htail_ev (fun _ => true)
    have hge' : (tail.foldl stepW (List.ofFn (fun _ : Fin 9 => true) ++ [true || true])).length ≤ C.output := by
      rw [foldl_len]; simp; omega
    have hval : (tail.foldl stepW (List.ofFn (fun _ : Fin 9 => true) ++ [true || true])).getD C.output false = false :=
      getD_ge _ false C.output hge'
    rw [hval] at h1
    exact Bool.noConfusion h1
  rcases hout1 : env1.getD C.output (Sum.inr false) with out1 | b_const
  · let D : Circuit := ⟨gs1, out1⟩
    have hD_ev : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [y 0 || y 4]) = F9 y := by
      intro y
      have h := hgs1_ev C.output hCout_lt y
      rw [hout1] at h
      dsimp only [Sum.elim_inl] at h
      change (gs1.foldl stepW (List.ofFn y ++ [y 0 || y 4])).getD out1 false = F9 y
      exact h.trans (htail_ev y)
    have hD_le14 : gs1.length ≤ 14 := by omega
    -- Wire-insensitivity lemma: if two base inputs agree on all wires outside `bad`, and no gate reads `bad`,
    -- then every wire outside `bad` agrees on both inputs.
    have wire_agree : ∀ (gs : List Gate) (w1 w2 : List Bool) (bad : ℕ → Prop),
        w1.length = w2.length →
        (∀ i < w1.length, ¬ bad i → w1.getD i false = w2.getD i false) →
        (∀ j < gs.length, ∀ g, gs[j]? = some g → ¬ bad (w1.length + j) → ∀ i ∈ g.inputs, ¬ bad i) →
        ∀ k < (gs.foldl stepW w1).length, ¬ bad k →
          (gs.foldl stepW w1).getD k false = (gs.foldl stepW w2).getD k false := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro w1 w2 bad _ hbase _ k hk hnb
        simp only [List.foldl_nil] at hk ⊢
        exact hbase k hk hnb
      | append_singleton gs g ih =>
        intro w1 w2 bad hlen hbase hstep k hk hnb
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hk ⊢
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hl1 : (gs.foldl stepW w1).length = w1.length + gs.length := foldl_len gs w1
        have hl2 : (gs.foldl stepW w2).length = w1.length + gs.length := by rw [foldl_len, ← hlen]
        have hprev_eq : ∀ u < w1.length + gs.length, ¬ bad u →
            (gs.foldl stepW w1).getD u false = (gs.foldl stepW w2).getD u false := by
          intro u hu hnu
          apply ih w1 w2 bad hlen hbase (by
            intro j hj g' hgj hnb'
            apply hstep j (by simp; omega) g' (by rw [List.getElem?_append_left hj]; exact hgj) hnb') u (by omega) hnu
        change k < ((gs.foldl stepW w1) ++ [_]).length at hk
        simp only [List.length_append, List.length_cons, List.length_nil] at hk
        by_cases hlt : k < w1.length + gs.length
        · change ((gs.foldl stepW w1) ++ [_]).getD k false = ((gs.foldl stepW w2) ++ [_]).getD k false
          rw [getD_snoc_lt _ _ _ k (by omega), getD_snoc_lt _ _ _ k (by omega)]
          exact hprev_eq k hlt hnb
        · have hkeq : k = w1.length + gs.length := by omega
          subst hkeq
          change ((gs.foldl stepW w1) ++ [_]).getD (w1.length + gs.length) false =
            ((gs.foldl stepW w2) ++ [_]).getD (w1.length + gs.length) false
          rw [← hl1, getD_snoc_eq, hl1, ← hl2, getD_snoc_eq]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hna : ¬ bad a := hstep gs.length (by simp) g
            (by rw [List.getElem?_append_right (le_refl gs.length)]; simp) hnb a ha
          by_cases halt : a < w1.length + gs.length
          · exact hprev_eq a halt hna
          · rw [getD_ge _ false a (by omega), getD_ge _ false a (by omega)]
    -- Fact A: at least 1 gate in gs1 reads input 4 (and out1 ≠ 4)
    have hout1_ne4 : out1 ≠ 4 := by
      intro heq
      have h := hD_ev (fun k => decide (k = 4))
      change (gs1.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 4)) ++ [false || true])).getD out1 false = _ at h
      rw [heq, foldl_getD_lt gs1 _ 4 (by simp)] at h
      have hl : (List.ofFn (fun k : Fin 9 => decide (k = 4)) ++ [false || true]).getD 4 false = true := by decide
      have hr : F9 (fun k => decide (k = 4)) = false := by decide
      rw [hl, hr] at h
      exact Bool.noConfusion h
    have hout1_ne0 : out1 ≠ 0 := by
      intro heq
      have h := hD_ev (fun k => decide (k = 0))
      change (gs1.foldl stepW (List.ofFn (fun k : Fin 9 => decide (k = 0)) ++ [true || false])).getD out1 false = _ at h
      rw [heq, foldl_getD_lt gs1 _ 0 (by simp)] at h
      have hl : (List.ofFn (fun k : Fin 9 => decide (k = 0)) ++ [true || false]).getD 0 false = true := by decide
      have hr : F9 (fun k => decide (k = 0)) = false := by decide
      rw [hl, hr] at h
      exact Bool.noConfusion h
    have hout1_lt10 : out1 < 10 + gs1.length := by
      by_contra hge
      have h := hD_ev (fun _ => true)
      change (gs1.foldl stepW (List.ofFn (fun _ : Fin 9 => true) ++ [true])).getD out1 false = _ at h
      rw [getD_ge _ false out1 (by rw [foldl_len]; simp; omega)] at h
      exact Bool.noConfusion h
    have hr4_pos : 1 ≤ (gs1.filter (fun g => decide (4 ∈ g.inputs))).length := by
      by_contra h0
      have hnone : ∀ g ∈ gs1, 4 ∉ g.inputs := by
        intro g hg h4
        have hmem : g ∈ gs1.filter (fun g => decide (4 ∈ g.inputs)) :=
          List.mem_filter.mpr ⟨hg, decide_eq_true h4⟩
        have hpos : 0 < (gs1.filter (fun g => decide (4 ∈ g.inputs))).length :=
          List.length_pos_of_mem hmem
        omega
      let u1 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 3)
      let u2 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 3 ∨ k = 4)
      have heq := wire_agree gs1 (List.ofFn u1 ++ [u1 0 || u1 4]) (List.ofFn u2 ++ [u2 0 || u2 4])
        (fun i => i = 4) (by simp)
        (by
          intro i hi hne
          have hchk : ∀ j : Fin 10, j.val ≠ 4 →
              (List.ofFn u1 ++ [u1 0 || u1 4]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 || u2 4]).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne)
        (by
          intro j _ g hgj _ i hi heq4
          subst heq4
          exact hnone g (List.mem_of_getElem? hgj) hi)
        out1 (by rw [foldl_len]; simp; omega) hout1_ne4
      have h1 := hD_ev u1
      have h2 := hD_ev u2
      change (gs1.foldl stepW _).getD out1 false = F9 u1 at h1
      change (gs1.foldl stepW _).getD out1 false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
    have hr0_pos : 1 ≤ (gs1.filter (fun g => decide (0 ∈ g.inputs))).length := by
      by_contra h0
      have hnone : ∀ g ∈ gs1, 0 ∉ g.inputs := by
        intro g hg h0m
        have hmem : g ∈ gs1.filter (fun g => decide (0 ∈ g.inputs)) :=
          List.mem_filter.mpr ⟨hg, decide_eq_true h0m⟩
        have hpos : 0 < (gs1.filter (fun g => decide (0 ∈ g.inputs))).length :=
          List.length_pos_of_mem hmem
        omega
      let u1 : Fin 9 → Bool := fun k => decide (k = 4 ∨ k = 5)
      let u2 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 4 ∨ k = 5)
      have heq := wire_agree gs1 (List.ofFn u1 ++ [u1 0 || u1 4]) (List.ofFn u2 ++ [u2 0 || u2 4])
        (fun i => i = 0) (by simp)
        (by
          intro i hi hne
          have hchk : ∀ j : Fin 10, j.val ≠ 0 →
              (List.ofFn u1 ++ [u1 0 || u1 4]).getD j.val false =
              (List.ofFn u2 ++ [u2 0 || u2 4]).getD j.val false := by decide
          exact hchk ⟨i, by simpa using hi⟩ hne)
        (by
          intro j _ g hgj _ i hi heq0
          subst heq0
          exact hnone g (List.mem_of_getElem? hgj) hi)
        out1 (by rw [foldl_len]; simp; omega) hout1_ne0
      have h1 := hD_ev u1
      have h2 := hD_ev u2
      change (gs1.foldl stepW _).getD out1 false = F9 u1 at h1
      change (gs1.foldl stepW _).getD out1 false = F9 u2 at h2
      have hdiff : F9 u1 ≠ F9 u2 := by decide
      exact hdiff (h1.symm.trans (heq.trans h2))
    -- Step 2: Restrict gs1 at y 4 = false -> F8d4 (contradicts hDel4 if ≥ 2 gates drop or gs1.length ≤ 13)
    let ext4 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y =>
      ![y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7]
    have hF9_ext4 : ∀ y : Fin 8 → Bool, F9 (ext4 y) = F8d4 y := by
      intro y
      have h8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
          ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && false) || (false && a0) ||
           (a0 && a4) || (a1 && a5) || (a2 && a6) || (a3 && a7) ||
           (a4 && a6) || (a5 && a7) || (a7 && a4)) =
          ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a0 && a4) || (a1 && a5) ||
           (a2 && a6) || (a3 && a7) || (a4 && a6) || (a5 && a7) || (a7 && a4)) := by decide
      exact h8 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    let init_d4 : List (ℕ ⊕ Bool) :=
      [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr false,
       Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 0]
    obtain ⟨gs_d4, env_d4, drop_d4, henv_d4_len, hinit_d4_eq, _, hsz_d4, hdrop_d4_c, hprop_d4_c,
      hgs_d4_fan, _, _, _, hgs_d4_ev⟩ :=
      simplify 8 10 8 (fun y => List.ofFn (ext4 y) ++ [ext4 y 0 || ext4 y 4]) (fun y => List.ofFn y)
        init_d4 gs1 (by intro y; simp) (by intro y; simp) rfl hgs1_fan
        (by
          intro i hi y
          have hchk : ∀ j : Fin 10,
              Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d4.getD j.val (Sum.inr false)) =
                (List.ofFn (ext4 y) ++ [ext4 y 0 || ext4 y 4]).getD j.val false := by
            intro j
            fin_cases j <;> simp [init_d4, ext4]
          exact hchk ⟨i, hi⟩)
        (by
          intro i hi w hw
          have hchk : ∀ j : Fin 10, ∀ u, init_d4.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
            intro j u hu; fin_cases j <;> simp [init_d4] at hu <;> omega
          exact hchk ⟨i, hi⟩ w hw)
    have hd4_ge13 : 13 ≤ gs_d4.length := by
      by_contra hle12
      rcases hout_d4 : env_d4.getD out1 (Sum.inr false) with out_d4 | b_d4
      · apply hDel4
        refine ⟨⟨gs_d4, out_d4⟩, ?_, by change gs_d4.length ≤ 12; omega, ?_⟩
        · intro g hg
          have h := hgs_d4_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_d4_ev out1 (by omega) y
          rw [hout_d4] at h
          dsimp only [Sum.elim_inl] at h
          have hd := hD_ev (ext4 y)
          change (gs1.foldl stepW _).getD out1 false = F9 (ext4 y) at hd
          change (gs_d4.foldl stepW (List.ofFn y)).getD out_d4 false = F8d4 y
          rw [h, hd, hF9_ext4]
      · have h0 := hgs_d4_ev out1 (by omega) (fun _ => false)
        have h1 := hgs_d4_ev out1 (by omega) (fun _ => true)
        rw [hout_d4] at h0 h1
        dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hD_ev (ext4 (fun _ => false))
        have hd1 := hD_ev (ext4 (fun _ => true))
        change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
        rw [hd0] at h0; rw [hd1] at h1
        have hne : F9 (ext4 (fun _ => false)) ≠ F9 (ext4 (fun _ => true)) := by decide
        exact hne (h0.symm.trans h1)
    have h4_in_drop : ∀ j < gs1.length, ∀ g, gs1[j]? = some g → decide (4 ∈ g.inputs) = true → j ∈ drop_d4 := by
      intro j hj g hgj h4
      have h4m : 4 ∈ g.inputs := of_decide_eq_true h4
      have h4c : env_d4.getD 4 (Sum.inr false) = Sum.inr false := hinit_d4_eq 4 (by omega)
      have hcl := hgs1_clean g (List.mem_of_getElem? hgj)
      apply hdrop_d4_c j hj g hgj
      rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
      · exact Or.inr ⟨Or.inl hop, 4, h4m, by omega, false, h4c⟩
      · exact Or.inr ⟨Or.inr hop, 4, h4m, by omega, false, h4c⟩
      · refine Or.inl ⟨hop, 4, ?_, by omega, false, h4c⟩
        have hl1 := hcl.1 hop
        rcases hins : g.inputs with _ | ⟨a, rest⟩
        · rw [hins] at hl1; simp at hl1
        · rw [hins] at hl1 h4m
          simp only [List.length_cons] at hl1
          have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hnil; simp only [List.mem_singleton] at h4m; subst h4m; rfl
    have hdrop_d4_le1 : drop_d4.card ≤ 1 := by omega
    have hr4_le1 : (gs1.filter (fun g => decide (4 ∈ g.inputs))).length ≤ 1 :=
      (filter_le_card gs1 (fun g => decide (4 ∈ g.inputs)) drop_d4 h4_in_drop).trans hdrop_d4_le1
    have hr4_eq1 : (gs1.filter (fun g => decide (4 ∈ g.inputs))).length = 1 := by omega
    have hgs1_eq14 : gs1.length = 14 := by
      have : 1 ≤ drop_d4.card := by
        have := filter_le_card gs1 (fun g => decide (4 ∈ g.inputs)) drop_d4 h4_in_drop
        omega
      omega
    -- Extract the unique gate h in gs1 reading input 4, and prove h.op = GateOp.or
    have hunique4 : ∃ h : Gate, h.op = GateOp.or ∧ gs1.filter (fun g => decide (4 ∈ g.inputs)) = [h] := by
      rcases hfl : gs1.filter (fun g => decide (4 ∈ g.inputs)) with _ | ⟨h, rest⟩
      · rw [hfl] at hr4_eq1; simp at hr4_eq1
      · rw [hfl] at hr4_eq1
        simp only [List.length_cons] at hr4_eq1
        have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hnil
        have hh_mem : h ∈ gs1 ∧ 4 ∈ h.inputs := by
          have hm : h ∈ gs1.filter (fun g => decide (4 ∈ g.inputs)) := by rw [hfl]; simp
          have hm' := List.mem_filter.mp hm
          exact ⟨hm'.1, of_decide_eq_true hm'.2⟩
        obtain ⟨pos, hpos_lt, hpos_eq⟩ := List.getElem_of_mem hh_mem.1
        have hpos_some : gs1[pos]? = some h := by rw [List.getElem?_eq_getElem hpos_lt, hpos_eq]
        have hpos_drop : pos ∈ drop_d4 := h4_in_drop pos hpos_lt h hpos_some (decide_eq_true hh_mem.2)
        -- Prove h.op = GateOp.or by ruling out and / not
        have hhop : h.op = GateOp.or := by
          rcases (hgs1_fan h hh_mem.1).1 with hand | hor | hnot
          · exfalso
            have h4c : env_d4.getD 4 (Sum.inr false) = Sum.inr false := hinit_d4_eq 4 (by omega)
            obtain ⟨bh, hbh⟩ := hprop_d4_c pos hpos_lt h hpos_some
              (Or.inr ⟨hand, 4, hh_mem.2, by omega, h4c⟩)
            -- Either some later gate reads 10 + pos (giving 2nd dropped gate) or none does (dead gate contradiction)
            by_cases hread : ∃ j < gs1.length, ∃ g', gs1[j]? = some g' ∧ (10 + pos) ∈ g'.inputs
            · obtain ⟨j, hj_lt, g', hgj, hmem_j⟩ := hread
              have hj_gt : pos < j := by
                have hrb := hgs1_rb j hj_lt (10 + pos)
                have hget : gs1.getD j ⟨GateOp.or, []⟩ = g' := by
                  simp only [List.getD_eq_getElem?_getD, hgj, Option.getD_some]
                rw [hget] at hrb
                have := hrb hmem_j
                omega
              have hj_drop : j ∈ drop_d4 := by
                have hcl' := hgs1_clean g' (List.mem_of_getElem? hgj)
                apply hdrop_d4_c j hj_lt g' hgj
                rcases (hgs1_fan g' (List.mem_of_getElem? hgj)).1 with hop' | hop' | hop'
                · exact Or.inr ⟨Or.inl hop', 10 + pos, hmem_j, by omega, bh, hbh⟩
                · exact Or.inr ⟨Or.inr hop', 10 + pos, hmem_j, by omega, bh, hbh⟩
                · refine Or.inl ⟨hop', 10 + pos, ?_, by omega, bh, hbh⟩
                  have hl1 := hcl'.1 hop'
                  rcases hins : g'.inputs with _ | ⟨a, rest'⟩
                  · rw [hins] at hl1; simp at hl1
                  · rw [hins] at hl1 hmem_j
                    simp only [List.length_cons] at hl1
                    have hnil' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
                    subst hnil'; simp only [List.mem_singleton] at hmem_j; subst hmem_j; rfl
              have hcard2 : 2 ≤ drop_d4.card := by
                have hsub : ({pos, j} : Finset ℕ) ⊆ drop_d4 := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
                have hpc : ({pos, j} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
                have := Finset.card_le_card hsub
                omega
              omega
            · push Not at hread
              have hout_ne_pos : out1 ≠ 10 + pos := by
                intro heq
                have h0 := hgs_d4_ev out1 (by omega) (fun _ => false)
                have h1 := hgs_d4_ev out1 (by omega) (fun _ => true)
                rw [heq, hbh] at h0 h1
                dsimp only [Sum.elim_inr, id_eq] at h0 h1
                have hd0 := hD_ev (ext4 (fun _ => false))
                have hd1 := hD_ev (ext4 (fun _ => true))
                change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
                rw [heq] at hd0 hd1
                rw [hd0] at h0; rw [hd1] at h1
                have hne : F9 (ext4 (fun _ => false)) ≠ F9 (ext4 (fun _ => true)) := by decide
                exact hne (h0.symm.trans h1)
              -- Only pos reads 4, and nothing reads 10 + pos, so wire out1 agrees on {0,3} and {0,3,4}
              let u1 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 3)
              let u2 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 3 ∨ k = 4)
              have heq := wire_agree gs1 (List.ofFn u1 ++ [u1 0 || u1 4]) (List.ofFn u2 ++ [u2 0 || u2 4])
                (fun i => i = 4 ∨ i = 10 + pos) (by simp)
                (by
                  intro i hi hnb
                  have hne4 : i ≠ 4 := fun h => hnb (Or.inl h)
                  have hchk : ∀ j : Fin 10, j.val ≠ 4 →
                      (List.ofFn u1 ++ [u1 0 || u1 4]).getD j.val false =
                      (List.ofFn u2 ++ [u2 0 || u2 4]).getD j.val false := by decide
                  exact hchk ⟨i, by simpa using hi⟩ hne4)
                (by
                  intro j hj g' hgj hnb i hi hibad
                  rcases hibad with rfl | rfl
                  · have hj_drop : j ∈ drop_d4 := h4_in_drop j hj g' hgj (decide_eq_true hi)
                    have hj_eq : j = pos := by
                      by_contra hne
                      have hsub : ({pos, j} : Finset ℕ) ⊆ drop_d4 := by
                        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption
                      have hpc : ({pos, j} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hne)
                      have := Finset.card_le_card hsub; omega
                    apply hnb
                    right; simp [hj_eq]
                  · exact hread j hj g' hgj hi)
                out1 (by rw [foldl_len]; simp; omega)
                (fun hb => by rcases hb with h1 | h2; exact hout1_ne4 h1; exact hout_ne_pos h2)
              have h1 := hD_ev u1
              have h2 := hD_ev u2
              change (gs1.foldl stepW _).getD out1 false = F9 u1 at h1
              change (gs1.foldl stepW _).getD out1 false = F9 u2 at h2
              have hdiff : F9 u1 ≠ F9 u2 := by decide
              exact hdiff (h1.symm.trans (heq.trans h2))
          · exact hor
          · exfalso
            have h4c : env_d4.getD 4 (Sum.inr false) = Sum.inr false := hinit_d4_eq 4 (by omega)
            have hl1 := (hgs1_clean h hh_mem.1).1 hnot
            have hhd4 : h.inputs.head? = some 4 := by
              have h4m := hh_mem.2
              rcases hins : h.inputs with _ | ⟨a, rest'⟩
              · rw [hins] at hl1; simp at hl1
              · rw [hins] at hl1 h4m
                simp only [List.length_cons] at hl1
                have hnil' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst hnil'; simp only [List.mem_singleton] at h4m; subst h4m; rfl
            obtain ⟨bh, hbh⟩ := hprop_d4_c pos hpos_lt h hpos_some
              (Or.inl ⟨hnot, 4, hhd4, by omega, false, h4c⟩)
            by_cases hread : ∃ j < gs1.length, ∃ g', gs1[j]? = some g' ∧ (10 + pos) ∈ g'.inputs
            · obtain ⟨j, hj_lt, g', hgj, hmem_j⟩ := hread
              have hj_gt : pos < j := by
                have hrb := hgs1_rb j hj_lt (10 + pos)
                have hget : gs1.getD j ⟨GateOp.or, []⟩ = g' := by
                  simp only [List.getD_eq_getElem?_getD, hgj, Option.getD_some]
                rw [hget] at hrb
                have := hrb hmem_j
                omega
              have hj_drop : j ∈ drop_d4 := by
                have hcl' := hgs1_clean g' (List.mem_of_getElem? hgj)
                apply hdrop_d4_c j hj_lt g' hgj
                rcases (hgs1_fan g' (List.mem_of_getElem? hgj)).1 with hop' | hop' | hop'
                · exact Or.inr ⟨Or.inl hop', 10 + pos, hmem_j, by omega, bh, hbh⟩
                · exact Or.inr ⟨Or.inr hop', 10 + pos, hmem_j, by omega, bh, hbh⟩
                · refine Or.inl ⟨hop', 10 + pos, ?_, by omega, bh, hbh⟩
                  have hl1' := hcl'.1 hop'
                  rcases hins : g'.inputs with _ | ⟨a, rest'⟩
                  · rw [hins] at hl1'; simp at hl1'
                  · rw [hins] at hl1' hmem_j
                    simp only [List.length_cons] at hl1'
                    have hnil' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
                    subst hnil'; simp only [List.mem_singleton] at hmem_j; subst hmem_j; rfl
              have hcard2 : 2 ≤ drop_d4.card := by
                have hsub : ({pos, j} : Finset ℕ) ⊆ drop_d4 := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
                have hpc : ({pos, j} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
                have := Finset.card_le_card hsub
                omega
              omega
            · push Not at hread
              have hout_ne_pos : out1 ≠ 10 + pos := by
                intro heq
                have h0 := hgs_d4_ev out1 (by omega) (fun _ => false)
                have h1 := hgs_d4_ev out1 (by omega) (fun _ => true)
                rw [heq, hbh] at h0 h1
                dsimp only [Sum.elim_inr, id_eq] at h0 h1
                have hd0 := hD_ev (ext4 (fun _ => false))
                have hd1 := hD_ev (ext4 (fun _ => true))
                change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
                rw [heq] at hd0 hd1
                rw [hd0] at h0; rw [hd1] at h1
                have hne : F9 (ext4 (fun _ => false)) ≠ F9 (ext4 (fun _ => true)) := by decide
                exact hne (h0.symm.trans h1)
              let u1 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 3)
              let u2 : Fin 9 → Bool := fun k => decide (k = 0 ∨ k = 3 ∨ k = 4)
              have heq := wire_agree gs1 (List.ofFn u1 ++ [u1 0 || u1 4]) (List.ofFn u2 ++ [u2 0 || u2 4])
                (fun i => i = 4 ∨ i = 10 + pos) (by simp)
                (by
                  intro i hi hnb
                  have hne4 : i ≠ 4 := fun h => hnb (Or.inl h)
                  have hchk : ∀ j : Fin 10, j.val ≠ 4 →
                      (List.ofFn u1 ++ [u1 0 || u1 4]).getD j.val false =
                      (List.ofFn u2 ++ [u2 0 || u2 4]).getD j.val false := by decide
                  exact hchk ⟨i, by simpa using hi⟩ hne4)
                (by
                  intro j hj g' hgj hnb i hi hibad
                  rcases hibad with rfl | rfl
                  · have hj_drop : j ∈ drop_d4 := h4_in_drop j hj g' hgj (decide_eq_true hi)
                    have hj_eq : j = pos := by
                      by_contra hne
                      have hsub : ({pos, j} : Finset ℕ) ⊆ drop_d4 := by
                        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                        rcases hx with rfl | rfl <;> assumption
                      have hpc : ({pos, j} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hne)
                      have := Finset.card_le_card hsub; omega
                    apply hnb
                    right; simp [hj_eq]
                  · exact hread j hj g' hgj hi)
                out1 (by rw [foldl_len]; simp; omega)
                (fun hb => by rcases hb with h1 | h2; exact hout1_ne4 h1; exact hout_ne_pos h2)
              have h1 := hD_ev u1
              have h2 := hD_ev u2
              change (gs1.foldl stepW _).getD out1 false = F9 u1 at h1
              change (gs1.foldl stepW _).getD out1 false = F9 u2 at h2
              have hdiff : F9 u1 ≠ F9 u2 := by decide
              exact hdiff (h1.symm.trans (heq.trans h2))
        exact ⟨h, hhop, hfl⟩
    -- Step 3: Restrict gs1 at y 0 = false -> F8d0 (proves deg(0) ≤ 2)
    let ext0 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y =>
      ![false, y 0, y 1, y 2, y 6, y 7, y 4, y 5, y 3]
    have hF9_ext0 : ∀ y : Fin 8 → Bool, F9 (ext0 y) = F8d0 y := by
      intro y
      have h8 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
          ((false && a0) || (a0 && a1) || (a1 && a2) || (a2 && a6) || (a6 && false) ||
           (false && a7) || (a0 && a4) || (a1 && a5) || (a2 && a3) ||
           (a7 && a5) || (a4 && a3) || (a3 && a7)) =
          ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
           (a1 && a5) || (a2 && a6) || (a3 && a7) || (a5 && a7)) := by decide
      exact h8 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
    let init_d0 : List (ℕ ⊕ Bool) :=
      [Sum.inr false, Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 6,
       Sum.inl 7, Sum.inl 4, Sum.inl 5, Sum.inl 3, Sum.inl 6]
    obtain ⟨gs_d0, env_d0, drop_d0, henv_d0_len, hinit_d0_eq, _, hsz_d0, hdrop_d0_c, _,
      hgs_d0_fan, _, _, _, hgs_d0_ev⟩ :=
      simplify 8 10 8 (fun y => List.ofFn (ext0 y) ++ [ext0 y 0 || ext0 y 4]) (fun y => List.ofFn y)
        init_d0 gs1 (by intro y; simp) (by intro y; simp) rfl hgs1_fan
        (by
          intro i hi y
          have hchk : ∀ j : Fin 10,
              Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d0.getD j.val (Sum.inr false)) =
                (List.ofFn (ext0 y) ++ [ext0 y 0 || ext0 y 4]).getD j.val false := by
            intro j; fin_cases j <;> simp [init_d0, ext0]
          exact hchk ⟨i, hi⟩)
        (by
          intro i hi w hw
          have hchk : ∀ j : Fin 10, ∀ u, init_d0.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
            intro j u hu; fin_cases j <;> simp [init_d0] at hu <;> omega
          exact hchk ⟨i, hi⟩ w hw)
    have hd0_ge12 : 12 ≤ gs_d0.length := by
      by_contra hle11
      rcases hout_d0 : env_d0.getD out1 (Sum.inr false) with out_d0 | b_d0
      · apply hDel0
        refine ⟨⟨gs_d0, out_d0⟩, ?_, by change gs_d0.length ≤ 11; omega, ?_⟩
        · intro g hg
          have h := hgs_d0_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · intro y
          have h := hgs_d0_ev out1 (by omega) y
          rw [hout_d0] at h
          dsimp only [Sum.elim_inl] at h
          have hd := hD_ev (ext0 y)
          change (gs1.foldl stepW _).getD out1 false = F9 (ext0 y) at hd
          change (gs_d0.foldl stepW (List.ofFn y)).getD out_d0 false = F8d0 y
          rw [h, hd, hF9_ext0]
      · have h0 := hgs_d0_ev out1 (by omega) (fun _ => false)
        have h1 := hgs_d0_ev out1 (by omega) (fun _ => true)
        rw [hout_d0] at h0 h1
        dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hd0 := hD_ev (ext0 (fun _ => false))
        have hd1 := hD_ev (ext0 (fun _ => true))
        change (gs1.foldl stepW _).getD out1 false = _ at hd0 hd1
        rw [hd0] at h0; rw [hd1] at h1
        have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
        exact hne (h0.symm.trans h1)
    have hr0_le2 : (gs1.filter (fun g => decide (0 ∈ g.inputs))).length ≤ 2 := by
      have h0_in_drop : ∀ j < gs1.length, ∀ g, gs1[j]? = some g → decide (0 ∈ g.inputs) = true → j ∈ drop_d0 := by
        intro j hj g hgj h0
        have h0m : 0 ∈ g.inputs := of_decide_eq_true h0
        have h0c : env_d0.getD 0 (Sum.inr false) = Sum.inr false := hinit_d0_eq 0 (by omega)
        have hcl := hgs1_clean g (List.mem_of_getElem? hgj)
        apply hdrop_d0_c j hj g hgj
        rcases (hgs1_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, 0, h0m, by omega, false, h0c⟩
        · exact Or.inr ⟨Or.inr hop, 0, h0m, by omega, false, h0c⟩
        · refine Or.inl ⟨hop, 0, ?_, by omega, false, h0c⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 h0m
            simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at h0m; subst h0m; rfl
      have := filter_le_card gs1 (fun g => decide (0 ∈ g.inputs)) drop_d0 h0_in_drop
      omega
    -- Step 4: Automorphisms of P - v9 to bound fan-out of {6, 7} (≤ 2) and {1, 2, 3, 5, 8} (≤ 3)
    let aut : Fin 9 → Fin 9 := ![1, 2, 3, 8, 6, 0, 7, 4, 5]
    have aut_inv : ∀ y : Fin 9 → Bool, F9 (y ∘ aut) = F9 y := by
      intro y; dsimp [F9, aut, Function.comp_def]; ac_rfl
    have aut_pow_inv : ∀ (k : ℕ) (y : Fin 9 → Bool), F9 (y ∘ aut^[k]) = F9 y := by
      intro k
      induction k with
      | zero => intro y; rfl
      | succ k ih =>
        intro y
        rw [Function.iterate_succ]
        exact (aut_inv (y ∘ aut^[k])).trans (ih y)
    let gs_full : List Gate := ⟨GateOp.or, [0, 4]⟩ :: gs1
    have hfull_len : gs_full.length = 15 := by simp [gs_full, hgs1_eq14]
    have hfull_fan : ∀ g ∈ gs_full, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hmem
      · exact ⟨Or.inr (Or.inl rfl), le_refl 2⟩
      · exact hgs1_fan g hmem
    have hfull_clean : ∀ g ∈ gs_full, (g.op = GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup) := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hmem
      · exact ⟨fun h => GateOp.noConfusion h, fun _ => ⟨rfl, by decide⟩⟩
      · exact hgs1_clean g hmem
    have hfull_ev : ∀ y : Fin 9 → Bool, (gs_full.foldl stepW (List.ofFn y)).getD out1 false = F9 y := by
      intro y
      dsimp only [gs_full]
      rw [List.foldl_cons]
      have hs0 : stepW (List.ofFn y) ⟨GateOp.or, [0, 4]⟩ = List.ofFn y ++ [y 0 || y 4] := by
        change List.ofFn y ++ [GateOp.or.eval _] = _
        rw [eval_or]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have h0 : (List.ofFn y).getD 0 false = y 0 := by simp [List.getD_eq_getElem?_getD]
        have h4 : (List.ofFn y).getD 4 false = y 4 := by simp [List.getD_eq_getElem?_getD]
        rw [h0, h4]
      rw [hs0]
      exact hD_ev y
    -- Generic restriction of gs_full at any v ≠ 0, 4 via an automorphism p = aut^[k]
    have deg_bound_del4 : ∀ (v : Fin 9) (k : ℕ), v.val ≠ 0 → v.val ≠ 4 → aut^[k] v = 4 →
        (gs1.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ 2 := by
      intro v k hv0 hv4 hpk
      let p : Fin 9 → Fin 9 := aut^[k]
      let map4 : Fin 9 → ℕ ⊕ Bool := fun i => init_d4.getD (p i).val (Sum.inr false)
      have hmap4_eval : ∀ (i : Fin 9) (y : Fin 8 → Bool),
          Sum.elim (fun w => (List.ofFn y).getD w false) id (map4 i) = ext4 y (p i) := by
        intro i y
        have hchk : ∀ j : Fin 9,
            Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d4.getD j.val (Sum.inr false)) = ext4 y j := by
          intro j; fin_cases j <;> simp [init_d4, ext4]
        exact hchk (p i)
      have hmap4_bd : ∀ (i : Fin 9) (w : ℕ), map4 i = Sum.inl w → w < 8 := by
        intro i w hw
        have hchk : ∀ j : Fin 9, ∀ u, init_d4.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
          intro j u hu; fin_cases j <;> simp [init_d4] at hu <;> omega
        exact hchk (p i) w hw
      let init_v : List (ℕ ⊕ Bool) := List.ofFn map4
      obtain ⟨gs_v, env_v, drop_v, henv_v_len, hinit_v_eq, _, hsz_v, hdrop_v_c, _,
        hgs_v_fan, _, _, _, hgs_v_ev⟩ :=
        simplify 8 9 8 (fun y => List.ofFn (ext4 y ∘ p)) (fun y => List.ofFn y)
          init_v gs_full (by intro y; simp) (by intro y; simp) (by simp [init_v]) hfull_fan
          (by
            intro i hi y
            have hi1 : init_v.getD i (Sum.inr false) = map4 ⟨i, hi⟩ := by
              simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
            have hi2 : (List.ofFn (ext4 y ∘ p)).getD i false = ext4 y (p ⟨i, hi⟩) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, Function.comp_def]
            rw [hi1, hi2]
            exact hmap4_eval ⟨i, hi⟩ y)
          (by
            intro i hi w hw
            simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
              Option.getD_some] at hw
            exact hmap4_bd ⟨i, hi⟩ w hw)
      have hgs_v_ge13 : 13 ≤ gs_v.length := by
        by_contra hle12
        rcases hout_v : env_v.getD out1 (Sum.inr false) with out_v | b_v
        · apply hDel4
          refine ⟨⟨gs_v, out_v⟩, ?_, by change gs_v.length ≤ 12; omega, ?_⟩
          · intro g hg
            have h := hgs_v_fan g hg
            exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
          · intro y
            have h := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) y
            rw [hout_v] at h
            dsimp only [Sum.elim_inl] at h
            change (gs_v.foldl stepW (List.ofFn y)).getD out_v false = F8d4 y
            rw [h, hfull_ev (ext4 y ∘ p), aut_pow_inv k, hF9_ext4]
        · have h0 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => false)
          have h1 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => true)
          rw [hout_v] at h0 h1
          dsimp only [Sum.elim_inr, id_eq] at h0 h1
          rw [hfull_ev, aut_pow_inv k] at h0
          rw [hfull_ev, aut_pow_inv k] at h1
          have hne : F9 (ext4 (fun _ => false)) ≠ F9 (ext4 (fun _ => true)) := by decide
          exact hne (h0.symm.trans h1)
      have hvc : env_v.getD v.val (Sum.inr false) = Sum.inr false := by
        rw [hinit_v_eq v.val v.isLt]
        simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        dsimp only [map4, p]
        rw [hpk]; rfl
      have hv_drop : ∀ j < gs_full.length, ∀ g, gs_full[j]? = some g → decide (v.val ∈ g.inputs) = true → j ∈ drop_v := by
        intro j hj g hgj hvm
        have hvm' : v.val ∈ g.inputs := of_decide_eq_true hvm
        have hcl := hfull_clean g (List.mem_of_getElem? hgj)
        apply hdrop_v_c j hj g hgj
        rcases (hfull_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, v.val, hvm', by omega, false, hvc⟩
        · exact Or.inr ⟨Or.inr hop, v.val, hvm', by omega, false, hvc⟩
        · refine Or.inl ⟨hop, v.val, ?_, by omega, false, hvc⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 hvm'
            simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at hvm'; subst hvm'; rfl
      have hle_drop := filter_le_card gs_full (fun g => decide (v.val ∈ g.inputs)) drop_v hv_drop
      have hfilt_eq : gs_full.filter (fun g => decide (v.val ∈ g.inputs)) =
          gs1.filter (fun g => decide (v.val ∈ g.inputs)) := by
        dsimp only [gs_full]
        rw [List.filter_cons]
        have hnot04 : decide (v.val ∈ ([0, 4] : List ℕ)) = false := by
          simp [hv0, hv4]
        simp only [hnot04, Bool.false_eq_true, ↓reduceIte]
      rw [hfilt_eq] at hle_drop
      omega
    have deg_bound_del0 : ∀ (v : Fin 9) (k : ℕ), v.val ≠ 0 → v.val ≠ 4 → aut^[k] v = 0 →
        (gs1.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ 3 := by
      intro v k hv0 hv4 hpk
      let p : Fin 9 → Fin 9 := aut^[k]
      let map0 : Fin 9 → ℕ ⊕ Bool := fun i => init_d0.getD (p i).val (Sum.inr false)
      have hmap0_eval : ∀ (i : Fin 9) (y : Fin 8 → Bool),
          Sum.elim (fun w => (List.ofFn y).getD w false) id (map0 i) = ext0 y (p i) := by
        intro i y
        have hchk : ∀ j : Fin 9,
            Sum.elim (fun w => (List.ofFn y).getD w false) id (init_d0.getD j.val (Sum.inr false)) = ext0 y j := by
          intro j; fin_cases j <;> simp [init_d0, ext0]
        exact hchk (p i)
      have hmap0_bd : ∀ (i : Fin 9) (w : ℕ), map0 i = Sum.inl w → w < 8 := by
        intro i w hw
        have hchk : ∀ j : Fin 9, ∀ u, init_d0.getD j.val (Sum.inr false) = Sum.inl u → u < 8 := by
          intro j u hu; fin_cases j <;> simp [init_d0] at hu <;> omega
        exact hchk (p i) w hw
      let init_v : List (ℕ ⊕ Bool) := List.ofFn map0
      obtain ⟨gs_v, env_v, drop_v, henv_v_len, hinit_v_eq, _, hsz_v, hdrop_v_c, _,
        hgs_v_fan, _, _, _, hgs_v_ev⟩ :=
        simplify 8 9 8 (fun y => List.ofFn (ext0 y ∘ p)) (fun y => List.ofFn y)
          init_v gs_full (by intro y; simp) (by intro y; simp) (by simp [init_v]) hfull_fan
          (by
            intro i hi y
            have hi1 : init_v.getD i (Sum.inr false) = map0 ⟨i, hi⟩ := by
              simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
            have hi2 : (List.ofFn (ext0 y ∘ p)).getD i false = ext0 y (p ⟨i, hi⟩) := by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, Function.comp_def]
            rw [hi1, hi2]
            exact hmap0_eval ⟨i, hi⟩ y)
          (by
            intro i hi w hw
            simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
              Option.getD_some] at hw
            exact hmap0_bd ⟨i, hi⟩ w hw)
      have hgs_v_ge12 : 12 ≤ gs_v.length := by
        by_contra hle11
        rcases hout_v : env_v.getD out1 (Sum.inr false) with out_v | b_v
        · apply hDel0
          refine ⟨⟨gs_v, out_v⟩, ?_, by change gs_v.length ≤ 11; omega, ?_⟩
          · intro g hg
            have h := hgs_v_fan g hg
            exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
          · intro y
            have h := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) y
            rw [hout_v] at h
            dsimp only [Sum.elim_inl] at h
            change (gs_v.foldl stepW (List.ofFn y)).getD out_v false = F8d0 y
            rw [h, hfull_ev (ext0 y ∘ p), aut_pow_inv k, hF9_ext0]
        · have h0 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => false)
          have h1 := hgs_v_ev out1 (by rw [henv_v_len, hfull_len]; omega) (fun _ => true)
          rw [hout_v] at h0 h1
          dsimp only [Sum.elim_inr, id_eq] at h0 h1
          rw [hfull_ev, aut_pow_inv k] at h0
          rw [hfull_ev, aut_pow_inv k] at h1
          have hne : F9 (ext0 (fun _ => false)) ≠ F9 (ext0 (fun _ => true)) := by decide
          exact hne (h0.symm.trans h1)
      have hvc : env_v.getD v.val (Sum.inr false) = Sum.inr false := by
        rw [hinit_v_eq v.val v.isLt]
        simp only [init_v, List.getD_eq_getElem?_getD, List.getElem?_ofFn, v.isLt, ↓reduceDIte,
          Option.getD_some, Fin.eta]
        dsimp only [map0, p]
        rw [hpk]; rfl
      have hv_drop : ∀ j < gs_full.length, ∀ g, gs_full[j]? = some g → decide (v.val ∈ g.inputs) = true → j ∈ drop_v := by
        intro j hj g hgj hvm
        have hvm' : v.val ∈ g.inputs := of_decide_eq_true hvm
        have hcl := hfull_clean g (List.mem_of_getElem? hgj)
        apply hdrop_v_c j hj g hgj
        rcases (hfull_fan g (List.mem_of_getElem? hgj)).1 with hop | hop | hop
        · exact Or.inr ⟨Or.inl hop, v.val, hvm', by omega, false, hvc⟩
        · exact Or.inr ⟨Or.inr hop, v.val, hvm', by omega, false, hvc⟩
        · refine Or.inl ⟨hop, v.val, ?_, by omega, false, hvc⟩
          have hl1 := hcl.1 hop
          rcases hins : g.inputs with _ | ⟨a, rest⟩
          · rw [hins] at hl1; simp at hl1
          · rw [hins] at hl1 hvm'
            simp only [List.length_cons] at hl1
            have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
            subst hnil; simp only [List.mem_singleton] at hvm'; subst hvm'; rfl
      have hle_drop := filter_le_card gs_full (fun g => decide (v.val ∈ g.inputs)) drop_v hv_drop
      have hfilt_eq : gs_full.filter (fun g => decide (v.val ∈ g.inputs)) =
          gs1.filter (fun g => decide (v.val ∈ g.inputs)) := by
        dsimp only [gs_full]
        rw [List.filter_cons]
        have hnot04 : decide (v.val ∈ ([0, 4] : List ℕ)) = false := by
          simp [hv0, hv4]
        simp only [hnot04, Bool.false_eq_true, ↓reduceIte]
      rw [hfilt_eq] at hle_drop
      omega
    have hr6_le2 : (gs1.filter (fun g => decide (6 ∈ g.inputs))).length ≤ 2 :=
      deg_bound_del4 6 2 (by decide) (by decide) (by decide)
    have hr7_le2 : (gs1.filter (fun g => decide (7 ∈ g.inputs))).length ≤ 2 :=
      deg_bound_del4 7 1 (by decide) (by decide) (by decide)
    have hr_all_le3 : ∀ i : Fin 9, (gs1.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3 := by
      intro i
      fin_cases i
      · exact hr0_le2.trans (by omega)
      · exact deg_bound_del0 1 5 (by decide) (by decide) (by decide)
      · exact deg_bound_del0 2 4 (by decide) (by decide) (by decide)
      · exact deg_bound_del0 3 3 (by decide) (by decide) (by decide)
      · exact hr4_le1.trans (by omega)
      · exact deg_bound_del0 5 1 (by decide) (by decide) (by decide)
      · exact hr6_le2.trans (by omega)
      · exact hr7_le2.trans (by omega)
      · exact deg_bound_del0 8 2 (by decide) (by decide) (by decide)
    -- Step 5: Split on presence of a NOT gate in D
    have hD_fan : FanInTwo D := by
      intro g hg
      have h := hgs1_fan g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
    have hD_rb : ReadsBack 10 D := hgs1_rb
    have hr0_ex : ∃ g ∈ D.gates, 0 ∈ g.inputs := by
      rcases hfl : gs1.filter (fun g => decide (0 ∈ g.inputs)) with _ | ⟨g, _⟩
      · rw [hfl] at hr0_pos; simp at hr0_pos
      · have hm : g ∈ gs1.filter (fun g => decide (0 ∈ g.inputs)) := by rw [hfl]; simp
        have hm' := List.mem_filter.mp hm
        exact ⟨g, hm'.1, of_decide_eq_true hm'.2⟩
    have hr067 : ∀ i ∈ ([0, 6, 7] : List ℕ), (D.gates.filter (fun g => decide (i ∈ g.inputs))).length ≤ 2 := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact hr0_le2
      · exact hr6_le2
      · exact hr7_le2
    by_cases hhasNot : ∃ g ∈ D.gates, g.op = GateOp.not
    · exact hNot14 D hD_fan hD_rb hgs1_clean hhasNot hgs1_eq14 hunique4 hr0_ex hr067 hr_all_le3 hD_ev
    · have hAO : AndOrOnly D := by
        intro g hg
        rcases (hgs1_fan g hg).1 with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact False.elim (hhasNot ⟨g, hg, h1⟩)
      have hlen2 : ∀ g ∈ D.gates, g.inputs.length = 2 := fun g hg =>
        ((hgs1_clean g hg).2 (fun h => hhasNot ⟨g, hg, h⟩)).1
      have hnodup : ∀ g ∈ D.gates, g.inputs.Nodup := fun g hg =>
        ((hgs1_clean g hg).2 (fun h => hhasNot ⟨g, hg, h⟩)).2
      exact hMono14 D ⟨hAO, hD_rb, hlen2⟩ hnodup hgs1_eq14 hunique4 hr0_ex hr067 hr_all_le3 hD_ev
  · -- Impossible: C.output mapped to constant b_const
    have h0 := hgs1_ev C.output hCout_lt (fun _ => false)
    have h1 := hgs1_ev C.output hCout_lt (fun _ => true)
    rw [hout1] at h0 h1
    dsimp only [Sum.elim_inr, id_eq] at h0 h1
    rw [htail_ev] at h0 h1
    have hne : F9 (fun _ => false) ≠ F9 (fun _ => true) := by decide
    exact hne (h0.symm.trans h1)
