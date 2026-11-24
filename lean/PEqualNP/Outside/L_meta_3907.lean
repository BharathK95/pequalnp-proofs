import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3907 : have x1 : (Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) → Bool ⊕ Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) (x2 : Bool ⊕ Fin (17 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => Sum.elim id (fun (x4 : Fin (17 : ℕ)) => x1 x4 x3) x2; have x2 : (Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) → Fin (17 : ℕ) → Prop := fun (x2 : Fin (17 : ℕ) → (Fin (9 : ℕ) → Bool) → Bool) (x3 : Fin (17 : ℕ)) => ∃ (x4 : Bool ⊕ Fin (17 : ℕ)) (x5 : Bool ⊕ Fin (17 : ℕ)), (∀ (x6 : Fin (17 : ℕ)), x4 = Sum.inr x6 ∨ x5 = Sum.inr x6 → x6 < x3) ∧ ((∀ (x6 : Fin (9 : ℕ) → Bool), x2 x3 x6 = (x1 x2 x4 x6 && x1 x2 x5 x6)) ∨ ∀ (x6 : Fin (9 : ℕ) → Bool), x2 x3 x6 = (x1 x2 x4 x6 || x1 x2 x5 x6)); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size = (8 : ℕ) → ∀ (x6 : Fin (17 : ℕ)), (9 : ℕ) < ↑x6 → x2 (fun (x8 : Fin (17 : ℕ)) (x9 : Fin (9 : ℕ) → Bool) => (x3.wires (List.ofFn x9)).getD (↑x8) Bool.false) x6 := by
  dsimp only
  intro C hC hsz i hi
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have foldLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have foldPref : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (u : ℕ),
      u < w.length → (gs.foldl step w).getD u false = w.getD u false := by
    intro gs
    induction gs with
    | nil => intro w u _; rfl
    | cons g gs ih =>
      intro w u hu
      rw [List.foldl_cons, ih (step w g) u (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hu
  let k : ℕ := i.val - 9
  have hk : k < C.gates.length := by
    change C.gates.length = 8 at hsz
    have := i.isLt
    omega
  let g : PEqualNP.CircuitLowerBounds.Gate := C.gates[k]'hk
  have hgMem : g ∈ C.gates := List.getElem_mem hk
  obtain ⟨hgOp, hgLen⟩ := hC g hgMem
  have hsplit : C.gates = C.gates.take k ++ g :: C.gates.drop (k + 1) := by
    have h1 : C.gates.drop k = g :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [← h1, List.take_append_drop]
  have htakeLen : (C.gates.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  let pref (x : Fin 9 → Bool) : List Bool := (C.gates.take k).foldl step (List.ofFn x)
  have hprefLen (x : Fin 9 → Bool) : (pref x).length = i.val := by
    dsimp [pref]
    rw [foldLen, List.length_ofFn, htakeLen]
    omega
  have hwireEq (x : Fin 9 → Bool) (u : ℕ) (hu : u < i.val) :
      (C.wires (List.ofFn x)).getD u false = (pref x).getD u false := by
    change (C.gates.foldl step (List.ofFn x)).getD u false = _
    rw [hsplit, List.foldl_append]
    exact foldPref (g :: C.gates.drop (k + 1)) (pref x) u (by rw [hprefLen]; exact hu)
  have hwireAt (x : Fin 9 → Bool) :
      (C.wires (List.ofFn x)).getD i.val false =
        g.op.eval (g.inputs.map fun u => (pref x).getD u false) := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = _
    rw [hsplit, List.foldl_append, List.foldl_cons]
    have hstepLen : (step (pref x) g).length = i.val + 1 := by
      simp [step, hprefLen]
    rw [foldPref (C.gates.drop (k + 1)) (step (pref x) g) i.val (by omega)]
    dsimp [step]
    rw [List.getD_append_right _ _ _ _ (by rw [hprefLen])]
    rw [hprefLen, Nat.sub_self]
    rfl
  let z : Fin 17 → (Fin 9 → Bool) → Bool :=
    fun j x => (C.wires (List.ofFn x)).getD j.val false
  let resolve (u : ℕ) : Bool ⊕ Fin 17 :=
    if h : u < i.val then Sum.inr ⟨u, lt_trans h i.isLt⟩ else Sum.inl false
  have hresLt (u : ℕ) (j : Fin 17) (h : resolve u = Sum.inr j) : j < i := by
    dsimp [resolve] at h
    split_ifs at h with hu
    injection h with hj
    subst hj
    exact hu
  have hresVal (u : ℕ) (x : Fin 9 → Bool) :
      Sum.elim id (fun j : Fin 17 => z j x) (resolve u) = (pref x).getD u false := by
    dsimp [resolve]
    split_ifs with hu
    · exact hwireEq x u hu
    · symm
      exact List.getD_eq_default _ _ (by rw [hprefLen]; omega)
  rcases hgOp with hOp | hOp
  · cases hIn : g.inputs with
    | nil =>
      refine ⟨Sum.inl true, Sum.inl true, ?_, Or.inl ?_⟩
      · intro j hj; rcases hj with h | h <;> cases h
      · intro x
        rw [hwireAt x, hOp, hIn]
        rfl
    | cons u rest =>
      cases rest with
      | nil =>
        refine ⟨resolve u, Sum.inl true, ?_, Or.inl ?_⟩
        · intro j hj
          rcases hj with h | h
          · exact hresLt u j h
          · cases h
        · intro x
          rw [hwireAt x, hOp, hIn, hresVal u x]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      | cons v rest2 =>
        cases rest2 with
        | nil =>
          refine ⟨resolve u, resolve v, ?_, Or.inl ?_⟩
          · intro j hj
            rcases hj with h | h
            · exact hresLt u j h
            · exact hresLt v j h
          · intro x
            rw [hwireAt x, hOp, hIn, hresVal u x, hresVal v x]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        | cons _ _ =>
          rw [hIn] at hgLen
          simp at hgLen
  · cases hIn : g.inputs with
    | nil =>
      refine ⟨Sum.inl false, Sum.inl false, ?_, Or.inr ?_⟩
      · intro j hj; rcases hj with h | h <;> cases h
      · intro x
        rw [hwireAt x, hOp, hIn]
        rfl
    | cons u rest =>
      cases rest with
      | nil =>
        refine ⟨resolve u, Sum.inl false, ?_, Or.inr ?_⟩
        · intro j hj
          rcases hj with h | h
          · exact hresLt u j h
          · cases h
        · intro x
          rw [hwireAt x, hOp, hIn, hresVal u x]
          simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      | cons v rest2 =>
        cases rest2 with
        | nil =>
          refine ⟨resolve u, resolve v, ?_, Or.inr ?_⟩
          · intro j hj
            rcases hj with h | h
            · exact hresLt u j h
            · exact hresLt v j h
          · intro x
            rw [hwireAt x, hOp, hIn, hresVal u x, hresVal v x]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        | cons _ _ =>
          rw [hIn] at hgLen
          simp at hgLen
