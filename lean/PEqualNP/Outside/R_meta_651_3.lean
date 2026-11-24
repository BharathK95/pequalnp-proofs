import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_651_3 :
    (¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 10 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      C.size ≤ 19 →
      (∀ i : Fin 10, (C.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3) →
      ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 C →
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
        (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      C.size ≤ 19 →
      (∀ i : Fin 10, (C.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3) →
      ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) →
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 19 := by
  intro hP9 hMono hNot hHas
  let F10 : (Fin 10 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
    (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let F9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
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
  -- Core circuit simplifier & constant-propagation pass (for both cleaning and gate elimination)
  have simplify : ∀ (n_in n_out : ℕ) (x_of : (Fin n_out → Bool) → (Fin n_in → Bool))
      (init : List (ℕ ⊕ Bool)) (killP : Gate → Bool) (gs : List Gate),
      init.length = n_in →
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ i : ℕ, i < n_in → ∀ y : Fin n_out → Bool,
        Sum.elim (fun w => (List.ofFn y).getD w false) id (init.getD i (Sum.inr false)) =
          (List.ofFn (x_of y)).getD i false) →
      (∀ i : ℕ, i < n_in → ∀ w, init.getD i (Sum.inr false) = Sum.inl w → w < n_out) →
      (∀ g ∈ gs, killP g = true →
        (g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in ∧ ∃ b, init.getD a (Sum.inr false) = Sum.inr b) ∨
        ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a ∈ g.inputs, a < n_in ∧ ∃ b, init.getD a (Sum.inr false) = Sum.inr b)) →
      ∃ (gs' : List Gate) (env : List (ℕ ⊕ Bool)),
        env.length = n_in + gs.length ∧
        (∀ i : ℕ, i < n_in → env.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
        gs'.length + (gs.filter killP).length ≤ gs.length ∧
        (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        (∀ j < gs'.length, ∀ i ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
        (∀ g ∈ gs', (g.op = GateOp.not → g.inputs.length = 1) ∧
          (g.op ≠ GateOp.not → g.inputs.length = 2 ∧ g.inputs.Nodup)) ∧
        (∀ k < env.length, ∀ w, env.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs'.length) ∧
        (∀ k < env.length, ∀ y : Fin n_out → Bool,
          Sum.elim (fun w => (gs'.foldl stepW (List.ofFn y)).getD w false) id (env.getD k (Sum.inr false)) =
            (gs.foldl stepW (List.ofFn (x_of y))).getD k false) := by
    intro n_in n_out x_of init killP gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro hlen _ heval hbd _
      refine ⟨[], init, by simp [hlen], fun _ _ => rfl, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ hg; simp at hg
      · intro _ hj; simp at hj
      · intro _ hg; simp at hg
      · intro k hk w hw
        rw [hlen] at hk
        simpa using hbd k hk w hw
      · intro k hk y
        rw [hlen] at hk
        simpa using heval k hk y
    | append_singleton gs g ih =>
      intro hlen hfan heval hbd hkill
      have hfan_gs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
        fun h hh => hfan h (List.mem_append_left _ hh)
      have hfan_g : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
        hfan g (List.mem_append_right _ (List.mem_singleton_self g))
      have hkill_gs : ∀ h ∈ gs, killP h = true →
          (h.op = GateOp.not ∧ ∃ a, h.inputs.head? = some a ∧ a < n_in ∧ ∃ b, init.getD a (Sum.inr false) = Sum.inr b) ∨
          ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ ∃ a ∈ h.inputs, a < n_in ∧ ∃ b, init.getD a (Sum.inr false) = Sum.inr b) :=
        fun h hh => hkill h (List.mem_append_left _ hh)
      have hkill_g : killP g = true →
          (g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < n_in ∧ ∃ b, init.getD a (Sum.inr false) = Sum.inr b) ∨
          ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a ∈ g.inputs, a < n_in ∧ ∃ b, init.getD a (Sum.inr false) = Sum.inr b) :=
        hkill g (List.mem_append_right _ (List.mem_singleton_self g))
      obtain ⟨gs', env, henv_len, hinit_eq, hsz, hgs'_fan, hgs'_rb, hgs'_clean, hgs'_bd, hgs'_ev⟩ :=
        ih hlen hfan_gs heval hbd hkill_gs
      let lookup : ℕ → ℕ ⊕ Bool := fun i =>
        if i < env.length then env.getD i (Sum.inr false) else Sum.inr false
      have lookup_bd : ∀ i w, lookup i = Sum.inl w → w < n_out + gs'.length := by
        intro i w hw
        dsimp [lookup] at hw
        by_cases hi : i < env.length
        · simp only [hi, ↓reduceIte] at hw
          exact hgs'_bd i hi w hw
        · simp only [hi, ↓reduceIte] at hw
          cases hw
      have lookup_ev : ∀ i (y : Fin n_out → Bool),
          Sum.elim (fun w => (gs'.foldl stepW (List.ofFn y)).getD w false) id (lookup i) =
            (gs.foldl stepW (List.ofFn (x_of y))).getD i false := by
        intro i y
        dsimp [lookup]
        by_cases hi : i < env.length
        · simp only [hi, ↓reduceIte]
          exact hgs'_ev i hi y
        · simp only [hi, ↓reduceIte]
          have hglen : (gs.foldl stepW (List.ofFn (x_of y))).length = env.length := by
            rw [foldl_len, List.length_ofFn, henv_len]
          symm
          exact getD_ge _ false i (by omega)
      have lookup_init : ∀ a, a < n_in → lookup a = init.getD a (Sum.inr false) := by
        intro a ha
        dsimp [lookup]
        have halt : a < env.length := by omega
        simp only [halt, ↓reduceIte]
        exact hinit_eq a ha
      -- Helper: finish with NO new gate added (`add = []`, output `v_out`)
      have finish_no_add : ∀ (v_out : ℕ ⊕ Bool),
          (∀ w, v_out = Sum.inl w → w < n_out + gs'.length) →
          (∀ y : Fin n_out → Bool,
            Sum.elim (fun w => (gs'.foldl stepW (List.ofFn y)).getD w false) id v_out =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn (x_of y))).getD i false)) →
          ∃ (gs1 : List Gate) (env1 : List (ℕ ⊕ Bool)),
            env1.length = n_in + (gs ++ [g]).length ∧
            (∀ i : ℕ, i < n_in → env1.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
            gs1.length + ((gs ++ [g]).filter killP).length ≤ (gs ++ [g]).length ∧
            (∀ h ∈ gs1, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
            (∀ j < gs1.length, ∀ i ∈ (gs1.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
            (∀ h ∈ gs1, (h.op = GateOp.not → h.inputs.length = 1) ∧
              (h.op ≠ GateOp.not → h.inputs.length = 2 ∧ h.inputs.Nodup)) ∧
            (∀ k < env1.length, ∀ w, env1.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs1.length) ∧
            (∀ k < env1.length, ∀ y : Fin n_out → Bool,
              Sum.elim (fun w => (gs1.foldl stepW (List.ofFn y)).getD w false) id (env1.getD k (Sum.inr false)) =
                ((gs ++ [g]).foldl stepW (List.ofFn (x_of y))).getD k false) := by
        intro v_out hv_bd hv_ev
        refine ⟨gs', env ++ [v_out], ?_, ?_, ?_, hgs'_fan, hgs'_rb, hgs'_clean, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, henv_len]; omega
        · intro i hi
          rw [getD_snoc_lt env v_out _ i (by omega)]
          exact hinit_eq i hi
        · rw [List.filter_append, List.length_append, List.length_append]
          have hfl : ([g].filter killP).length ≤ 1 := by
            have := List.length_filter_le killP [g]
            simpa using this
          simp only [List.length_cons, List.length_nil] at hfl ⊢
          omega
        · intro k hk w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env v_out _ k hlt] at hw
            exact hgs'_bd k hlt w hw
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq] at hw
            exact hv_bd w hw
        · intro k hk y
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hglen : (gs.foldl stepW (List.ofFn (x_of y))).length = env.length := by
            rw [foldl_len, List.length_ofFn, henv_len]
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env v_out _ k hlt]
            have hlt2 : k < (gs.foldl stepW (List.ofFn (x_of y))).length := by omega
            change _ = ((gs.foldl stepW (List.ofFn (x_of y))) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k hlt2]
            exact hgs'_ev k hlt y
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq]
            rw [hv_ev y, ← hglen]
            change _ = ((gs.foldl stepW (List.ofFn (x_of y))) ++ [_]).getD (gs.foldl stepW (List.ofFn (x_of y))).length false
            rw [getD_snoc_eq]
      -- Helper: finish with ONE new clean gate `g_new` added (`killP g = false`)
      have finish_add : ∀ (g_new : Gate),
          killP g = false →
          (g_new.op = GateOp.and ∨ g_new.op = GateOp.or ∨ g_new.op = GateOp.not) ∧ g_new.inputs.length ≤ 2 →
          (∀ i ∈ g_new.inputs, i < n_out + gs'.length) →
          (g_new.op = GateOp.not → g_new.inputs.length = 1) ∧
            (g_new.op ≠ GateOp.not → g_new.inputs.length = 2 ∧ g_new.inputs.Nodup) →
          (∀ y : Fin n_out → Bool,
            g_new.op.eval (g_new.inputs.map fun i => (gs'.foldl stepW (List.ofFn y)).getD i false) =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn (x_of y))).getD i false)) →
          ∃ (gs1 : List Gate) (env1 : List (ℕ ⊕ Bool)),
            env1.length = n_in + (gs ++ [g]).length ∧
            (∀ i : ℕ, i < n_in → env1.getD i (Sum.inr false) = init.getD i (Sum.inr false)) ∧
            gs1.length + ((gs ++ [g]).filter killP).length ≤ (gs ++ [g]).length ∧
            (∀ h ∈ gs1, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧
            (∀ j < gs1.length, ∀ i ∈ (gs1.getD j ⟨GateOp.or, []⟩).inputs, i < n_out + j) ∧
            (∀ h ∈ gs1, (h.op = GateOp.not → h.inputs.length = 1) ∧
              (h.op ≠ GateOp.not → h.inputs.length = 2 ∧ h.inputs.Nodup)) ∧
            (∀ k < env1.length, ∀ w, env1.getD k (Sum.inr false) = Sum.inl w → w < n_out + gs1.length) ∧
            (∀ k < env1.length, ∀ y : Fin n_out → Bool,
              Sum.elim (fun w => (gs1.foldl stepW (List.ofFn y)).getD w false) id (env1.getD k (Sum.inr false)) =
                ((gs ++ [g]).foldl stepW (List.ofFn (x_of y))).getD k false) := by
        intro g_new hkf hgn_fan hgn_rb hgn_clean hgn_ev
        refine ⟨gs' ++ [g_new], env ++ [Sum.inl (n_out + gs'.length)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil, henv_len]; omega
        · intro i hi
          rw [getD_snoc_lt env _ _ i (by omega)]
          exact hinit_eq i hi
        · rw [List.filter_append]
          have hfk : [g].filter killP = [] := by simp [hkf]
          rw [hfk, List.append_nil]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · intro h hh
          rcases List.mem_append.mp hh with h1 | h2
          · exact hgs'_fan h h1
          · rw [List.mem_singleton.mp h2]; exact hgn_fan
        · intro j hj i hi
          simp only [List.length_append, List.length_cons, List.length_nil] at hj
          by_cases hlt : j < gs'.length
          · rw [getD_snoc_lt gs' g_new _ j hlt] at hi
            exact hgs'_rb j hlt i hi
          · have hjeq : j = gs'.length := by omega
            subst hjeq
            rw [getD_snoc_eq] at hi
            exact hgn_rb i hi
        · intro h hh
          rcases List.mem_append.mp hh with h1 | h2
          · exact hgs'_clean h h1
          · rw [List.mem_singleton.mp h2]; exact hgn_clean
        · intro k hk w hw
          simp only [List.length_append, List.length_cons, List.length_nil] at hk ⊢
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env _ _ k hlt] at hw
            have := hgs'_bd k hlt w hw
            omega
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq] at hw
            injection hw with hw'
            omega
        · intro k hk y
          simp only [List.length_append, List.length_cons, List.length_nil] at hk
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hglen : (gs.foldl stepW (List.ofFn (x_of y))).length = env.length := by
            rw [foldl_len, List.length_ofFn, henv_len]
          have hglen' : (gs'.foldl stepW (List.ofFn y)).length = n_out + gs'.length := by
            rw [foldl_len, List.length_ofFn]
          by_cases hlt : k < env.length
          · rw [getD_snoc_lt env _ _ k hlt]
            have hlt2 : k < (gs.foldl stepW (List.ofFn (x_of y))).length := by omega
            change _ = ((gs.foldl stepW (List.ofFn (x_of y))) ++ [_]).getD k false
            rw [getD_snoc_lt _ _ _ k hlt2]
            have hprev := hgs'_ev k hlt y
            rcases hval : env.getD k (Sum.inr false) with w | b
            · rw [hval] at hprev
              dsimp only [Sum.elim_inl] at hprev ⊢
              have hwlt : w < (gs'.foldl stepW (List.ofFn y)).length := by
                have := hgs'_bd k hlt w hval; omega
              change ((gs'.foldl stepW (List.ofFn y)) ++ [_]).getD w false = _
              rw [getD_snoc_lt _ _ _ w hwlt]
              exact hprev
            · rw [hval] at hprev
              exact hprev
          · have hkeq : k = env.length := by omega
            subst hkeq
            rw [getD_snoc_eq]
            dsimp only [Sum.elim_inl]
            rw [← hglen', ← hglen]
            change ((gs'.foldl stepW (List.ofFn y)) ++ [_]).getD (gs'.foldl stepW (List.ofFn y)).length false =
              ((gs.foldl stepW (List.ofFn (x_of y))) ++ [_]).getD (gs.foldl stepW (List.ofFn (x_of y))).length false
            rw [getD_snoc_eq, getD_snoc_eq]
            exact hgn_ev y
      -- Case split on g.op
      rcases hfan_g.1 with hop | hop | hop
      · -- g.op = GateOp.and
        rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr true) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_and]; rfl)
        · exact finish_no_add (lookup a) (lookup_bd a) (fun y => by
            rw [hop, hins, eval_and]
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact lookup_ev a y)
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                exact finish_no_add (Sum.inl w1) (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                  rw [hop, hins, eval_and]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl] at ha hb ⊢
                  rw [← ha, ← hb, Bool.and_self])
              · have hkf : killP g = false := by
                  cases hk : killP g
                  · rfl
                  · exfalso
                    rcases hkill_g hk with ⟨hnot, _⟩ | ⟨_, c, hc_in, hc_lt, bc, hbc⟩
                    · rw [hop] at hnot; exact GateOp.noConfusion hnot
                    · rw [hins] at hc_in
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                      rcases hc_in with rfl | rfl
                      · have h1 := lookup_init c hc_lt; rw [hua, hbc] at h1; cases h1
                      · have h2 := lookup_init c hc_lt; rw [hub, hbc] at h2; cases h2
                refine finish_add ⟨GateOp.and, [w1, w2]⟩ hkf ⟨Or.inl rfl, le_refl 2⟩ ?_ ?_ ?_
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
              · exact finish_no_add (Sum.inr false) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_and]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.and_false])
              · exact finish_no_add (Sum.inl w1) (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                  rw [hop, hins, eval_and]
                  simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                  rw [← ha, ← hb, Bool.and_true])
          · cases b1
            · exact finish_no_add (Sum.inr false) (fun _ h => by cases h) (fun y => by
                rw [hop, hins, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha ⊢
                rw [← ha, Bool.false_and])
            · exact finish_no_add (lookup b) (lookup_bd b) (fun y => by
                rw [hop, hins, eval_and]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.true_and]
                exact lookup_ev b y)
      · -- g.op = GateOp.or
        rcases list_le2 g.inputs hfan_g.2 with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
        · exact finish_no_add (Sum.inr false) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_or]; rfl)
        · exact finish_no_add (lookup a) (lookup_bd a) (fun y => by
            rw [hop, hins, eval_or]
            simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact lookup_ev a y)
        · rcases hua : lookup a with w1 | b1
          · rcases hub : lookup b with w2 | b2
            · by_cases heq : w1 = w2
              · subst heq
                exact finish_no_add (Sum.inl w1) (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                  rw [hop, hins, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl] at ha hb ⊢
                  rw [← ha, ← hb, Bool.or_self])
              · have hkf : killP g = false := by
                  cases hk : killP g
                  · rfl
                  · exfalso
                    rcases hkill_g hk with ⟨hnot, _⟩ | ⟨_, c, hc_in, hc_lt, bc, hbc⟩
                    · rw [hop] at hnot; exact GateOp.noConfusion hnot
                    · rw [hins] at hc_in
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc_in
                      rcases hc_in with rfl | rfl
                      · have h1 := lookup_init c hc_lt; rw [hua, hbc] at h1; cases h1
                      · have h2 := lookup_init c hc_lt; rw [hub, hbc] at h2; cases h2
                refine finish_add ⟨GateOp.or, [w1, w2]⟩ hkf ⟨Or.inr (Or.inl rfl), le_refl 2⟩ ?_ ?_ ?_
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
              · exact finish_no_add (Sum.inl w1) (fun _ h => by injection h with h'; subst h'; exact lookup_bd a w1 hua) (fun y => by
                  rw [hop, hins, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have ha := lookup_ev a y; rw [hua] at ha
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ha hb ⊢
                  rw [← ha, ← hb, Bool.or_false])
              · exact finish_no_add (Sum.inr true) (fun _ h => by cases h) (fun y => by
                  rw [hop, hins, eval_or]
                  simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  have hb := lookup_ev b y; rw [hub] at hb
                  dsimp only [Sum.elim_inr, id_eq] at hb ⊢
                  rw [← hb, Bool.or_true])
          · cases b1
            · exact finish_no_add (lookup b) (lookup_bd b) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha
                rw [← ha, Bool.false_or]
                exact lookup_ev b y)
            · exact finish_no_add (Sum.inr true) (fun _ h => by cases h) (fun y => by
                rw [hop, hins, eval_or]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                have ha := lookup_ev a y; rw [hua] at ha
                dsimp only [Sum.elim_inr, id_eq] at ha ⊢
                rw [← ha, Bool.true_or])
      · -- g.op = GateOp.not
        rcases hins : g.inputs with _ | ⟨a, rest⟩
        · exact finish_no_add (Sum.inr true) (fun _ h => by cases h) (fun y => by
            rw [hop, hins, eval_not]; rfl)
        · rcases hua : lookup a with w1 | b1
          · have hkf : killP g = false := by
              cases hk : killP g
              · rfl
              · exfalso
                rcases hkill_g hk with ⟨_, c, hc_hd, hc_lt, bc, hbc⟩ | ⟨hao, _⟩
                · rw [hins] at hc_hd
                  simp only [List.head?_cons, Option.some.injEq] at hc_hd
                  rw [hc_hd] at hua
                  have h1 := lookup_init c hc_lt; rw [hua, hbc] at h1; cases h1
                · rcases hao with h1 | h1 <;> (rw [hop] at h1; exact GateOp.noConfusion h1)
            refine finish_add ⟨GateOp.not, [w1]⟩ hkf ⟨Or.inr (Or.inr rfl), by simp⟩ ?_ ?_ ?_
            · intro i hi
              rw [List.mem_singleton.mp hi]
              exact lookup_bd a w1 hua
            · exact ⟨fun _ => rfl, fun h => False.elim (h rfl)⟩
            · intro y
              rw [hop, hins]
              simp only [eval_not, List.map_cons, List.headD_cons]
              have ha := lookup_ev a y; rw [hua] at ha
              dsimp only [Sum.elim_inl] at ha
              rw [ha]
          · exact finish_no_add (Sum.inr (!b1)) (fun _ h => by cases h) (fun y => by
              rw [hop, hins, eval_not]
              simp only [List.map_cons, List.headD_cons]
              have ha := lookup_ev a y; rw [hua] at ha
              dsimp only [Sum.elim_inr, id_eq] at ha ⊢
              rw [← ha])
  -- Step 1: Clean the 19-gate circuit C for F10 into C1
  obtain ⟨C, hCfan, hCsz, hCev⟩ := hHas
  have hCfan' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hCfan g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  let init10 : List (ℕ ⊕ Bool) := List.ofFn (fun i : Fin 10 => Sum.inl i.val)
  obtain ⟨gs1, env1, henv1_len, _, hsz1, hgs1_fan, hgs1_rb, hgs1_clean, _, hgs1_ev⟩ :=
    simplify 10 10 id init10 (fun _ => false) C.gates
      (by simp [init10]) hCfan'
      (by
        intro i hi y
        simp only [init10, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.elim_inl, id_eq])
      (by
        intro i hi w hw
        simp only [init10, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, Sum.inl.injEq] at hw
        omega)
      (by intro _ _ h; exact Bool.noConfusion h)
  have hCout_lt : C.output < env1.length := by
    by_contra hge
    have h1 := hCev (fun _ => true)
    have hge' : (C.wires (List.ofFn (fun _ : Fin 10 => true))).length ≤ C.output := by
      change (C.gates.foldl stepW (List.ofFn (fun _ : Fin 10 => true))).length ≤ C.output
      rw [foldl_len, List.length_ofFn]; omega
    have hval : C.eval (List.ofFn (fun _ : Fin 10 => true)) = false := by
      change (C.wires (List.ofFn (fun _ : Fin 10 => true))).getD C.output false = false
      exact getD_ge _ false C.output hge'
    rw [hval] at h1
    exact Bool.noConfusion h1
  rcases hout1 : env1.getD C.output (Sum.inr false) with out1 | b_const
  · let C1 : Circuit := ⟨gs1, out1⟩
    have hC1_ev : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = F10 x := by
      intro x
      have h := hgs1_ev C.output hCout_lt x
      rw [hout1] at h
      dsimp only [Sum.elim_inl] at h
      have hc := hCev x
      change (C.gates.foldl stepW (List.ofFn x)).getD C.output false = F10 x at hc
      change (gs1.foldl stepW (List.ofFn x)).getD out1 false = F10 x
      exact h.trans hc
    have hC1_sz : C1.size ≤ 19 := by
      change gs1.length ≤ 19
      change C.gates.length ≤ 19 at hCsz
      omega
    have hC1_fan : FanInTwo C1 := by
      intro g hg
      have h := hgs1_fan g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
    have hC1_rb : ReadsBack 10 C1 := hgs1_rb
    -- Step 2: Check whether any input has fan-out ≥ 4 in C1
    by_cases hhigh : ∃ v : Fin 10, 4 ≤ (C1.gates.filter (fun g => decide (v.val ∈ g.inputs))).length
    · obtain ⟨v, hv4⟩ := hhigh
      -- Petersen automorphisms mapping any v to 9
      let rot : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]
      let sw : Fin 10 → Fin 10 := ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0]
      have rot_inv : ∀ x : Fin 10 → Bool, F10 (x ∘ rot) = F10 x := by
        intro x; dsimp [F10, rot, Function.comp_def]; ac_rfl
      have sw_inv : ∀ x : Fin 10 → Bool, F10 (x ∘ sw) = F10 x := by
        intro x; dsimp [F10, sw, Function.comp_def]; ac_rfl
      have rot_inj : Function.Injective rot := by decide
      have sw_inj : Function.Injective sw := by decide
      have rot_pow_inv : ∀ (k : ℕ) (x : Fin 10 → Bool), F10 (x ∘ rot^[k]) = F10 x := by
        intro k
        induction k with
        | zero => intro x; rfl
        | succ k ih =>
          intro x
          rw [Function.iterate_succ]
          have h1 : F10 ((x ∘ rot^[k]) ∘ rot) = F10 (x ∘ rot^[k]) := rot_inv (x ∘ rot^[k])
          exact h1.trans (ih x)
      have rot_pow_inj : ∀ k : ℕ, Function.Injective (rot^[k]) := by
        intro k
        induction k with
        | zero => exact Function.injective_id
        | succ k ih => rw [Function.iterate_succ]; exact ih.comp rot_inj
      have hex_aut : ∃ p : Fin 10 → Fin 10, p v = 9 ∧ Function.Injective p ∧ ∀ x, F10 (x ∘ p) = F10 x := by
        by_cases hv5 : v.val < 5
        · refine ⟨sw ∘ rot^[5 - v.val], ?_, sw_inj.comp (rot_pow_inj _), ?_⟩
          · have hchk : ∀ u : Fin 10, u.val < 5 → (sw ∘ rot^[5 - u.val]) u = 9 := by decide
            exact hchk v hv5
          · intro x
            have h1 : F10 ((x ∘ sw) ∘ rot^[5 - v.val]) = F10 (x ∘ sw) := rot_pow_inv _ (x ∘ sw)
            exact h1.trans (sw_inv x)
        · refine ⟨rot^[9 - v.val], ?_, rot_pow_inj _, rot_pow_inv _⟩
          have hchk : ∀ u : Fin 10, ¬ (u.val < 5) → (rot^[9 - u.val]) u = 9 := by decide
          exact hchk v hv5
      obtain ⟨p, hpv, hpinj, hpinv⟩ := hex_aut
      have hF10_snoc : ∀ y : Fin 9 → Bool, F10 (Fin.snoc y false) = F9 y := by
        intro y
        have h9 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
            ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
             (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a4 && false) ||
             (a5 && a7) || (a7 && false) || (false && a6) || (a6 && a8) || (a8 && a5)) =
            ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) ||
             (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) ||
             (a5 && a7) || (a6 && a8) || (a8 && a5)) := by decide
        exact h9 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
      let init9 : List (ℕ ⊕ Bool) :=
        List.ofFn (fun i : Fin 10 => if (p i).val < 9 then Sum.inl (p i).val else Sum.inr false)
      have hinit9_v : init9.getD v.val (Sum.inr false) = Sum.inr false := by
        have hvlt : v.val < 10 := v.isLt
        simp only [init9, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hvlt, ↓reduceDIte,
          Option.getD_some, Fin.eta, hpv]
        rfl
      obtain ⟨gs2, env2, henv2_len, _, hsz2, hgs2_fan, _, _, _, hgs2_ev⟩ :=
        simplify 10 9 (fun y => Fin.snoc y false ∘ p) init9
          (fun g => decide (v.val ∈ g.inputs)) gs1
          (by simp [init9]) hgs1_fan
          (by
            intro i hi y
            simp only [init9, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
              Option.getD_some, Function.comp_def]
            by_cases hp9 : (p ⟨i, hi⟩).val < 9
            · simp only [hp9, ↓reduceIte, Sum.elim_inl, ↓reduceDIte, Option.getD_some, Fin.snoc, cast_eq]
              rfl
            · simp only [hp9, ↓reduceIte, Sum.elim_inr, id_eq]
              have hpeq : p ⟨i, hi⟩ = Fin.last 9 := by
                ext; have := (p ⟨i, hi⟩).isLt; change (p ⟨i, hi⟩).val = 9; omega
              rw [hpeq, Fin.snoc_last])
          (by
            intro i hi w hw
            simp only [init9, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
              Option.getD_some] at hw
            by_cases hp9 : (p ⟨i, hi⟩).val < 9
            · simp only [hp9, ↓reduceIte, Sum.inl.injEq] at hw; omega
            · simp only [hp9, ↓reduceIte] at hw; cases hw)
          (by
            intro g hg hk
            have hvmem : v.val ∈ g.inputs := of_decide_eq_true hk
            have hcl := hgs1_clean g hg
            rcases (hgs1_fan g hg).1 with hop | hop | hop
            · exact Or.inr ⟨Or.inl hop, v.val, hvmem, v.isLt, false, hinit9_v⟩
            · exact Or.inr ⟨Or.inr hop, v.val, hvmem, v.isLt, false, hinit9_v⟩
            · refine Or.inl ⟨hop, v.val, ?_, v.isLt, false, hinit9_v⟩
              have hl1 : g.inputs.length = 1 := hcl.1 hop
              rcases hins : g.inputs with _ | ⟨a, rest⟩
              · rw [hins] at hl1; simp at hl1
              · rw [hins] at hl1 hvmem
                simp only [List.length_cons] at hl1
                have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
                subst hnil
                simp only [List.mem_singleton] at hvmem
                subst hvmem; rfl)
      have hout1_lt : out1 < env2.length := by
        by_contra hge
        have h1 := hC1_ev (fun _ => true)
        have hge' : (C1.wires (List.ofFn (fun _ : Fin 10 => true))).length ≤ out1 := by
          change (gs1.foldl stepW (List.ofFn (fun _ : Fin 10 => true))).length ≤ out1
          rw [foldl_len, List.length_ofFn]; omega
        have hval : C1.eval (List.ofFn (fun _ : Fin 10 => true)) = false := by
          change (C1.wires (List.ofFn (fun _ : Fin 10 => true))).getD out1 false = false
          exact getD_ge _ false out1 hge'
        rw [hval] at h1
        exact Bool.noConfusion h1
      rcases hout2 : env2.getD out1 (Sum.inr false) with out2 | b2
      · apply hP9
        refine ⟨⟨gs2, out2⟩, ?_, ?_, ?_⟩
        · intro g hg
          have h := hgs2_fan g hg
          exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
        · change gs2.length ≤ 15
          change gs1.length ≤ 19 at hC1_sz
          change 4 ≤ (gs1.filter (fun g => decide (v.val ∈ g.inputs))).length at hv4
          omega
        · intro y
          have h := hgs2_ev out1 hout1_lt y
          rw [hout2] at h
          dsimp only [Sum.elim_inl] at h
          have hc1 := hC1_ev (Fin.snoc y false ∘ p)
          change (gs1.foldl stepW (List.ofFn (Fin.snoc y false ∘ p))).getD out1 false = _ at hc1
          change (gs2.foldl stepW (List.ofFn y)).getD out2 false = F9 y
          rw [h, hc1, hpinv, hF10_snoc]
      · exfalso
        have h0 := hgs2_ev out1 hout1_lt (fun _ => false)
        have h1 := hgs2_ev out1 hout1_lt (fun _ => true)
        rw [hout2] at h0 h1
        dsimp only [Sum.elim_inr, id_eq] at h0 h1
        have hc0 := hC1_ev (Fin.snoc (fun _ : Fin 9 => false) false ∘ p)
        have hc1 := hC1_ev (Fin.snoc (fun _ : Fin 9 => true) false ∘ p)
        change (gs1.foldl stepW (List.ofFn _)).getD out1 false = _ at hc0 hc1
        rw [hc0, hpinv, hF10_snoc] at h0
        rw [hc1, hpinv, hF10_snoc] at h1
        have hne : F9 (fun _ => false) ≠ F9 (fun _ => true) := by decide
        exact hne (h0.symm.trans h1)
    · -- Step 3: Every input has fan-out ≤ 3 in C1; split on presence of a NOT gate
      have hlow : ∀ i : Fin 10, (C1.gates.filter (fun g => decide (i.val ∈ g.inputs))).length ≤ 3 := by
        intro i
        by_contra hgt
        exact hhigh ⟨i, by omega⟩
      by_cases hhasNot : ∃ g ∈ C1.gates, g.op = GateOp.not
      · exact hNot C1 hC1_fan hC1_rb hgs1_clean hhasNot hC1_sz hlow hC1_ev
      · have hAO : AndOrOnly C1 := by
          intro g hg
          rcases (hgs1_fan g hg).1 with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
          · exact False.elim (hhasNot ⟨g, hg, h1⟩)
        have hlen2 : ∀ g ∈ C1.gates, g.inputs.length = 2 := by
          intro g hg
          exact ((hgs1_clean g hg).2 (fun h => hhasNot ⟨g, hg, h⟩)).1
        have hnodup : ∀ g ∈ C1.gates, g.inputs.Nodup := by
          intro g hg
          exact ((hgs1_clean g hg).2 (fun h => hhasNot ⟨g, hg, h⟩)).2
        exact hMono C1 ⟨hAO, hC1_rb, hlen2⟩ hnodup hC1_sz hlow hC1_ev
  · -- Impossible: C.output mapped to constant b_const, contradicting F10 non-constancy
    have h0 := hgs1_ev C.output hCout_lt (fun _ => false)
    have h1 := hgs1_ev C.output hCout_lt (fun _ => true)
    rw [hout1] at h0 h1
    dsimp only [Sum.elim_inr, id_eq] at h0 h1
    have hc0 := hCev (fun _ => false)
    have hc1 := hCev (fun _ => true)
    change (C.gates.foldl stepW (List.ofFn _)).getD C.output false = _ at hc0 hc1
    rw [hc0] at h0; rw [hc1] at h1
    have hne : F10 (fun _ => false) ≠ F10 (fun _ => true) := by decide
    exact hne (h0.symm.trans h1)
