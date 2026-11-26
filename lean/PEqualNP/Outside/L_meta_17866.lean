import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17866

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev F10 := (Fin 10 → Bool) → Bool

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stepF (ws : List F10) (g : Gate) : List F10 :=
  ws ++ [fun x => g.op.eval (g.inputs.map fun i => (ws.getD i (fun _ => false)) x)]

theorem getD_map_eval (ws : List F10) (x : Fin 10 → Bool) (i : ℕ) :
    (ws.map fun f => f x).getD i false = (ws.getD i (fun _ => false)) x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : ws[i]? with
  | none => rfl
  | some f => rfl

theorem foldl_stepF_eval (gs : List Gate) (ws : List F10) (x : Fin 10 → Bool) :
    (gs.foldl stepF ws).map (fun f => f x) = gs.foldl stepB (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [stepF, stepB, List.map_append, List.map_cons, List.map_nil]
    congr 2
    congr 1
    apply List.map_congr_left
    intro i _
    exact (getD_map_eval ws x i).symm

theorem getD_mem_or_default {α : Type} (l : List α) (i : ℕ) (d : α) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_iff_getElem?.mpr ⟨i, h⟩)

theorem foldl_inv (P : ℕ → Set F10 → Prop)
    (hstep : ∀ (k : ℕ) (T : Set F10) (op : GateOp) (pins : List F10),
      P k T → (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
      pins.length ≤ 2 → (∀ f ∈ pins, f ∈ T) →
      (fun x => op.eval (pins.map fun f => f x)) ∉ T →
      P (k + 1) (insert (fun x => op.eval (pins.map fun f => f x)) T))
    (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (ws : List F10) (k : ℕ) (T : Set F10)
    (hP : P k T) (hz : (fun _ => false) ∈ T) (hws : ∀ f ∈ ws, f ∈ T) :
    ∃ (k' : ℕ) (T' : Set F10), k' ≤ k + gs.length ∧ P k' T' ∧
      (fun _ => false) ∈ T' ∧ ∀ f ∈ gs.foldl stepF ws, f ∈ T' := by
  induction gs generalizing ws k T with
  | nil =>
    exact ⟨k, T, by simp, hP, hz, hws⟩
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (by simp [hg'])
    let pins : List F10 := g.inputs.map (fun i => ws.getD i (fun _ => false))
    have hplen : pins.length ≤ 2 := by simpa [pins] using hg.2
    have hpmem : ∀ f ∈ pins, f ∈ T := by
      intro f hf
      simp only [pins, List.mem_map] at hf
      obtain ⟨i, _, rfl⟩ := hf
      rcases getD_mem_or_default ws i (fun _ => false) with h | h
      · exact hws _ h
      · rw [h]; exact hz
    let fnew : F10 := fun x => g.op.eval (pins.map fun f => f x)
    have hstep_eq : stepF ws g = ws ++ [fnew] := by
      simp [stepF, fnew, pins, List.map_map, Function.comp_def]
    simp only [List.foldl_cons, hstep_eq]
    by_cases hmem : fnew ∈ T
    · have hws' : ∀ f ∈ ws ++ [fnew], f ∈ T := by
        intro f hf
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with h | rfl
        · exact hws f h
        · exact hmem
      obtain ⟨k', T', hk', hP', hz', hws''⟩ := ih hgs' (ws ++ [fnew]) k T hP hz hws'
      exact ⟨k', T', by simp; omega, hP', hz', hws''⟩
    · have hP1 : P (k + 1) (insert fnew T) := hstep k T g.op pins hP hg.1 hplen hpmem hmem
      have hz1 : (fun _ => false) ∈ insert fnew T := Set.mem_insert_of_mem _ hz
      have hws' : ∀ f ∈ ws ++ [fnew], f ∈ insert fnew T := by
        intro f hf
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with h | rfl
        · exact Set.mem_insert_of_mem _ (hws f h)
        · exact Set.mem_insert _ _
      obtain ⟨k', T', hk', hP', hz', hws''⟩ := ih hgs' (ws ++ [fnew]) (k + 1) (insert fnew T) hP1 hz1 hws'
      exact ⟨k', T', by simp; omega, hP', hz', hws''⟩

theorem main_proof :
    let x1 : Type := (Fin (10 : ℕ) → Bool) → Bool; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List x1) (x4 : Set x1) (x5 : ℕ → Set x1 → Prop), PEqualNP.MetaComplexity.FanInTwo x2 → (fun (x7 : Fin (10 : ℕ) → Bool) => Bool.false) ∈ x4 → (∀ x8 ∈ x3, x8 ∈ x4) → x5 (0 : ℕ) x4 → (∀ (x10 : ℕ) (x11 : Set x1) (x12 : PEqualNP.CircuitLowerBounds.GateOp) (x13 : List x1), x5 x10 x11 → x12 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x12 = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x12 = PEqualNP.CircuitLowerBounds.GateOp.not → x13.length ≤ (2 : ℕ) → (∀ x17 ∈ x13, x17 ∈ x11) → (fun (x18 : Fin (10 : ℕ) → Bool) => x12.eval (List.map (fun (x19 : x1) => x19 x18) x13)) ∉ x11 → x5 (x10 + (1 : ℕ)) (Insert.insert (fun (x19 : Fin (10 : ℕ) → Bool) => x12.eval (List.map (fun (x20 : x1) => x20 x19) x13)) x11)) → ∃ (x11 : ℕ) (x12 : Set x1), x11 ≤ x2.size ∧ x5 x11 x12 ∧ (fun (x13 : Fin (10 : ℕ) → Bool) => x2.eval (List.map (fun (x14 : x1) => x14 x13) x3)) ∈ x12 := by
  intro F C inputs S P hfan hz hin hP0 hstep
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hfan g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  obtain ⟨k, T, hk, hP, hz', hws⟩ := foldl_inv P hstep C.gates hgs inputs 0 S hP0 hz hin
  refine ⟨k, T, by simpa [Circuit.size] using hk, hP, ?_⟩
  have heq : (fun x => C.eval (inputs.map fun f => f x)) =
      (C.gates.foldl stepF inputs).getD C.output (fun _ => false) := by
    funext x
    change (C.gates.foldl stepB (inputs.map fun f => f x)).getD C.output false = _
    rw [← foldl_stepF_eval C.gates inputs x, getD_map_eval]
  rw [heq]
  rcases getD_mem_or_default (C.gates.foldl stepF inputs) C.output (fun _ => false) with h | h
  · exact hws _ h
  · rw [h]; exact hz'

end PEqualNP.Outside.L_meta_17866

theorem PEqualNP.Outside.L_meta_17866 : (let x1 : Type := (Fin (10 : ℕ) → Bool) → Bool; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List x1) (x4 : Set x1) (x5 : ℕ → Set x1 → Prop), PEqualNP.MetaComplexity.FanInTwo x2 → (fun (x7 : Fin (10 : ℕ) → Bool) => Bool.false) ∈ x4 → (∀ x8 ∈ x3, x8 ∈ x4) → x5 (0 : ℕ) x4 → (∀ (x10 : ℕ) (x11 : Set x1) (x12 : PEqualNP.CircuitLowerBounds.GateOp) (x13 : List x1), x5 x10 x11 → x12 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x12 = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x12 = PEqualNP.CircuitLowerBounds.GateOp.not → x13.length ≤ (2 : ℕ) → (∀ x17 ∈ x13, x17 ∈ x11) → (fun (x18 : Fin (10 : ℕ) → Bool) => x12.eval (List.map (fun (x19 : x1) => x19 x18) x13)) ∉ x11 → x5 (x10 + (1 : ℕ)) (Insert.insert (fun (x19 : Fin (10 : ℕ) → Bool) => x12.eval (List.map (fun (x20 : x1) => x20 x19) x13)) x11)) → ∃ (x11 : ℕ) (x12 : Set x1), x11 ≤ x2.size ∧ x5 x11 x12 ∧ (fun (x13 : Fin (10 : ℕ) → Bool) => x2.eval (List.map (fun (x14 : x1) => x14 x13) x3)) ∈ x12) := by
  exact PEqualNP.Outside.L_meta_17866.main_proof
