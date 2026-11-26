import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18668

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ k, w1.getD k false = true → w2.getD k false = true) →
      ∀ k, (gs.foldl step w1).getD k false = true → (gs.foldl step w2).getD k false = true := by
  induction gs with
  | nil => intro w1 w2 _ hw k hk; exact hw k hk
  | cons g rest ih =>
    intro w1 w2 hlen hw
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step w1 g) (step w2 g)
    · simp [step, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have h1 : (step w1 g).getD k false = w1.getD k false := by
          simp only [step]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hlt,
            List.getElem_append_left hlt]
        have h2 : (step w2 g).getD k false = w2.getD k false := by
          simp only [step]
          rw [List.getD_eq_getElem _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by omega), List.getElem_append_left (by omega)]
        rw [h1] at hk
        rw [h2]
        exact hw k hk
      · by_cases heq : k = w1.length
        · subst heq
          have h1 : (step w1 g).getD w1.length false =
              g.op.eval (g.inputs.map fun i => w1.getD i false) := by
            simp only [step]
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
            simp
          have h2 : (step w2 g).getD w1.length false =
              g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            simp only [step]
            rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_append_right (by omega)]
            simp [hlen]
          rw [h1] at hk
          rw [h2]
          rcases hgs g List.mem_cons_self with hop | hop
          · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hk ⊢
            rintro _ ⟨i, hi, rfl⟩
            exact hw i (hk _ ⟨i, hi, rfl⟩)
          · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk ⊢
            obtain ⟨_, ⟨i, hi, rfl⟩, htrue⟩ := hk
            exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hw i htrue⟩
        · have hge : (step w1 g).length ≤ k := by simp [step]; omega
          rw [List.getD_eq_default _ _ hge] at hk
          cases hk

private lemma main (C : Circuit) (hM : Monotone2 C) (x y : Fin 24 → Bool)
    (hxy : ∀ i : Fin 24, x i = true → y i = true) (k : ℕ)
    (hk : (C.wires (List.ofFn x)).getD k false = true) :
    (C.wires (List.ofFn y)).getD k false = true := by
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := (hM g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  apply foldl_mono C.gates hgs (List.ofFn x) (List.ofFn y) (by simp) _ k hk
  intro i hi
  by_cases hilt : i < 24
  · rw [List.getD_eq_getElem _ _ (by simpa using hilt), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hilt), List.getElem_ofFn]
    exact hxy ⟨i, hilt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

end PEqualNP.Outside.L_meta_18668


theorem PEqualNP.Outside.L_meta_18668 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (24 : ℕ) → Bool), (∀ (x5 : Fin (24 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true) := by
  exact PEqualNP.Outside.L_meta_18668.main
