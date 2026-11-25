import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17145

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal (bank : List (BitVec 1024)) (g : Gate) : BitVec 1024 :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes 1024)
  | .or => args.foldr (· ||| ·) 0
  | .not => ~~~(args.headD 0)
  | _ => 0

def hcsStep (bank : List (BitVec 1024)) (g : Gate) : List (BitVec 1024) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit (bank : List (BitVec 1024)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit (xs : List (BitVec 1024)) (i : Fin 1024) :
    (xs.foldr (· &&& ·) (BitVec.allOnes 1024)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp only [List.foldr_nil, BitVec.getLsbD_allOnes, i.isLt, decide_true, List.map_nil, List.all_nil]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit (xs : List (BitVec 1024)) (i : Fin 1024) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit (bank : List (BitVec 1024)) (i : Fin 1024) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, GateOp.eval, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits (bank : List (BitVec 1024)) (i : Fin 1024) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

def fanInTwoBool (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
     | .and => true
     | .or => true
     | .not => true
     | _ => false) && decide (g.inputs.length ≤ 2)

theorem fanInTwo_of_bool (C : Circuit) (h : fanInTwoBool C = true) : FanInTwo C := by
  intro g hg
  have hall := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  refine ⟨?_, hall.2⟩
  cases hop : g.op <;> simp [hop] at hall ⊢

def witness : Circuit :=
  ⟨[
    ⟨.not, [0]⟩,
    ⟨.not, [1]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [10, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.not, [2]⟩,
    ⟨.not, [3]⟩,
    ⟨.not, [4]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.and, [2, 17]⟩,
    ⟨.and, [16, 3]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [19, 18]⟩,
    ⟨.and, [20, 18]⟩,
    ⟨.and, [21, 18]⟩,
    ⟨.and, [22, 18]⟩,
    ⟨.and, [19, 4]⟩,
    ⟨.and, [20, 4]⟩,
    ⟨.and, [21, 4]⟩,
    ⟨.and, [22, 4]⟩,
    ⟨.and, [12, 23]⟩,
    ⟨.and, [13, 23]⟩,
    ⟨.and, [14, 23]⟩,
    ⟨.and, [15, 23]⟩,
    ⟨.and, [12, 24]⟩,
    ⟨.and, [13, 24]⟩,
    ⟨.and, [14, 24]⟩,
    ⟨.and, [15, 24]⟩,
    ⟨.and, [12, 25]⟩,
    ⟨.and, [13, 25]⟩,
    ⟨.and, [14, 25]⟩,
    ⟨.and, [15, 25]⟩,
    ⟨.and, [12, 26]⟩,
    ⟨.and, [13, 26]⟩,
    ⟨.and, [14, 26]⟩,
    ⟨.and, [15, 26]⟩,
    ⟨.and, [12, 27]⟩,
    ⟨.and, [13, 27]⟩,
    ⟨.and, [14, 27]⟩,
    ⟨.and, [15, 27]⟩,
    ⟨.and, [12, 28]⟩,
    ⟨.and, [13, 28]⟩,
    ⟨.and, [14, 28]⟩,
    ⟨.and, [15, 28]⟩,
    ⟨.and, [12, 29]⟩,
    ⟨.and, [13, 29]⟩,
    ⟨.and, [14, 29]⟩,
    ⟨.and, [15, 29]⟩,
    ⟨.and, [12, 30]⟩,
    ⟨.and, [13, 30]⟩,
    ⟨.and, [14, 30]⟩,
    ⟨.and, [15, 30]⟩,
    ⟨.or, [52, 56]⟩,
    ⟨.or, [37, 41]⟩,
    ⟨.or, [40, 46]⟩,
    ⟨.or, [55, 59]⟩,
    ⟨.or, [39, 44]⟩,
    ⟨.or, [35, 57]⟩,
    ⟨.or, [31, 50]⟩,
    ⟨.or, [49, 64]⟩,
    ⟨.or, [36, 51]⟩,
    ⟨.or, [42, 61]⟩,
    ⟨.or, [32, 63]⟩,
    ⟨.or, [34, 65]⟩,
    ⟨.or, [58, 66]⟩,
    ⟨.or, [48, 69]⟩,
    ⟨.or, [33, 54]⟩,
    ⟨.or, [62, 76]⟩,
    ⟨.or, [47, 67]⟩,
    ⟨.or, [60, 71]⟩,
    ⟨.or, [43, 72]⟩,
    ⟨.or, [70, 74]⟩,
    ⟨.or, [53, 79]⟩,
    ⟨.or, [38, 53]⟩,
    ⟨.or, [40, 49]⟩,
    ⟨.or, [45, 68]⟩,
    ⟨.or, [31, 47]⟩,
    ⟨.or, [75, 81]⟩,
    ⟨.or, [45, 63]⟩,
    ⟨.or, [41, 77]⟩,
    ⟨.or, [34, 71]⟩,
    ⟨.or, [63, 64]⟩,
    ⟨.or, [37, 89]⟩,
    ⟨.or, [73, 83]⟩,
    ⟨.or, [35, 59]⟩,
    ⟨.or, [39, 87]⟩,
    ⟨.or, [68, 90]⟩,
    ⟨.or, [31, 56]⟩,
    ⟨.or, [65, 70]⟩,
    ⟨.or, [35, 73]⟩,
    ⟨.or, [60, 82]⟩,
    ⟨.or, [69, 99]⟩,
    ⟨.or, [40, 91]⟩,
    ⟨.or, [63, 67]⟩,
    ⟨.or, [33, 58]⟩,
    ⟨.or, [55, 64]⟩,
    ⟨.or, [32, 67]⟩,
    ⟨.or, [66, 85]⟩,
    ⟨.or, [32, 43]⟩,
    ⟨.or, [57, 94]⟩,
    ⟨.or, [74, 92]⟩,
    ⟨.or, [44, 78]⟩,
    ⟨.or, [35, 107]⟩,
    ⟨.or, [73, 103]⟩,
    ⟨.or, [60, 84]⟩,
    ⟨.or, [48, 72]⟩,
    ⟨.or, [31, 80]⟩,
    ⟨.or, [86, 112]⟩,
    ⟨.or, [75, 80]⟩,
    ⟨.or, [62, 82]⟩,
    ⟨.or, [54, 98]⟩,
    ⟨.or, [33, 85]⟩,
    ⟨.or, [46, 49]⟩,
    ⟨.or, [70, 88]⟩,
    ⟨.or, [41, 44]⟩,
    ⟨.or, [60, 122]⟩,
    ⟨.or, [117, 122]⟩,
    ⟨.or, [83, 118]⟩,
    ⟨.or, [74, 97]⟩,
    ⟨.or, [96, 106]⟩,
    ⟨.or, [93, 110]⟩,
    ⟨.or, [88, 118]⟩,
    ⟨.or, [114, 132]⟩,
    ⟨.or, [106, 113]⟩,
    ⟨.or, [68, 116]⟩,
    ⟨.or, [45, 50]⟩,
    ⟨.or, [74, 75]⟩,
    ⟨.or, [87, 108]⟩,
    ⟨.or, [59, 131]⟩,
    ⟨.or, [46, 139]⟩,
    ⟨.or, [55, 89]⟩,
    ⟨.or, [102, 141]⟩,
    ⟨.or, [59, 129]⟩,
    ⟨.or, [66, 101]⟩,
    ⟨.or, [84, 98]⟩,
    ⟨.or, [80, 108]⟩,
    ⟨.or, [107, 144]⟩,
    ⟨.or, [45, 69]⟩,
    ⟨.or, [134, 148]⟩,
    ⟨.or, [39, 66]⟩,
    ⟨.or, [115, 116]⟩,
    ⟨.or, [58, 86]⟩,
    ⟨.or, [71, 102]⟩,
    ⟨.or, [42, 145]⟩,
    ⟨.or, [143, 154]⟩,
    ⟨.or, [94, 97]⟩,
    ⟨.or, [119, 156]⟩,
    ⟨.or, [52, 152]⟩,
    ⟨.or, [72, 147]⟩,
    ⟨.or, [33, 159]⟩,
    ⟨.or, [93, 138]⟩,
    ⟨.or, [151, 161]⟩,
    ⟨.or, [58, 100]⟩,
    ⟨.or, [51, 121]⟩,
    ⟨.or, [125, 136]⟩,
    ⟨.or, [68, 130]⟩,
    ⟨.or, [73, 135]⟩,
    ⟨.or, [137, 167]⟩,
    ⟨.or, [78, 84]⟩,
    ⟨.or, [92, 169]⟩,
    ⟨.or, [100, 146]⟩,
    ⟨.or, [165, 171]⟩,
    ⟨.or, [81, 104]⟩,
    ⟨.or, [95, 120]⟩,
    ⟨.or, [55, 90]⟩,
    ⟨.or, [95, 96]⟩,
    ⟨.or, [114, 176]⟩,
    ⟨.or, [104, 124]⟩,
    ⟨.or, [97, 178]⟩,
    ⟨.or, [32, 34]⟩,
    ⟨.or, [68, 180]⟩,
    ⟨.or, [109, 153]⟩,
    ⟨.or, [47, 78]⟩,
    ⟨.or, [173, 174]⟩,
    ⟨.or, [105, 184]⟩,
    ⟨.or, [78, 81]⟩,
    ⟨.or, [75, 79]⟩,
    ⟨.or, [34, 158]⟩,
    ⟨.or, [130, 188]⟩,
    ⟨.or, [150, 182]⟩,
    ⟨.or, [56, 190]⟩,
    ⟨.or, [42, 101]⟩,
    ⟨.or, [91, 113]⟩,
    ⟨.or, [65, 87]⟩,
    ⟨.or, [119, 183]⟩,
    ⟨.or, [93, 195]⟩,
    ⟨.or, [105, 112]⟩,
    ⟨.or, [49, 197]⟩,
    ⟨.or, [99, 110]⟩,
    ⟨.or, [95, 194]⟩,
    ⟨.or, [60, 200]⟩,
    ⟨.or, [46, 193]⟩,
    ⟨.or, [187, 202]⟩,
    ⟨.or, [163, 175]⟩,
    ⟨.or, [67, 123]⟩,
    ⟨.or, [204, 205]⟩,
    ⟨.or, [33, 111]⟩,
    ⟨.or, [69, 207]⟩,
    ⟨.or, [115, 125]⟩,
    ⟨.or, [86, 120]⟩,
    ⟨.or, [138, 199]⟩,
    ⟨.or, [77, 211]⟩,
    ⟨.or, [79, 124]⟩,
    ⟨.or, [117, 213]⟩,
    ⟨.or, [121, 210]⟩,
    ⟨.or, [109, 215]⟩,
    ⟨.or, [123, 164]⟩,
    ⟨.or, [209, 217]⟩,
    ⟨.or, [77, 192]⟩,
    ⟨.or, [57, 219]⟩,
    ⟨.or, [111, 166]⟩,
    ⟨.or, [186, 221]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [223, 149]⟩,
    ⟨.and, [5, 155]⟩,
    ⟨.or, [224, 225]⟩,
    ⟨.and, [223, 140]⟩,
    ⟨.and, [5, 168]⟩,
    ⟨.or, [227, 228]⟩,
    ⟨.and, [223, 133]⟩,
    ⟨.and, [5, 189]⟩,
    ⟨.or, [230, 231]⟩,
    ⟨.and, [223, 198]⟩,
    ⟨.and, [5, 157]⟩,
    ⟨.or, [233, 234]⟩,
    ⟨.and, [223, 142]⟩,
    ⟨.and, [5, 172]⟩,
    ⟨.or, [236, 237]⟩,
    ⟨.and, [223, 162]⟩,
    ⟨.and, [5, 160]⟩,
    ⟨.or, [239, 240]⟩,
    ⟨.and, [223, 170]⟩,
    ⟨.and, [5, 191]⟩,
    ⟨.or, [242, 243]⟩,
    ⟨.and, [223, 208]⟩,
    ⟨.and, [5, 179]⟩,
    ⟨.or, [245, 246]⟩,
    ⟨.and, [223, 206]⟩,
    ⟨.and, [5, 126]⟩,
    ⟨.or, [248, 249]⟩,
    ⟨.and, [223, 218]⟩,
    ⟨.and, [5, 177]⟩,
    ⟨.or, [251, 252]⟩,
    ⟨.and, [223, 222]⟩,
    ⟨.and, [5, 128]⟩,
    ⟨.or, [254, 255]⟩,
    ⟨.and, [223, 185]⟩,
    ⟨.and, [5, 196]⟩,
    ⟨.or, [257, 258]⟩,
    ⟨.and, [223, 181]⟩,
    ⟨.and, [5, 201]⟩,
    ⟨.or, [260, 261]⟩,
    ⟨.and, [223, 220]⟩,
    ⟨.and, [5, 203]⟩,
    ⟨.or, [263, 264]⟩,
    ⟨.and, [223, 216]⟩,
    ⟨.and, [5, 214]⟩,
    ⟨.or, [266, 267]⟩,
    ⟨.and, [223, 212]⟩,
    ⟨.and, [5, 127]⟩,
    ⟨.or, [269, 270]⟩,
    ⟨.not, [6]⟩,
    ⟨.not, [7]⟩,
    ⟨.not, [8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [272, 273]⟩,
    ⟨.and, [6, 273]⟩,
    ⟨.and, [272, 7]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.and, [274, 275]⟩,
    ⟨.and, [8, 275]⟩,
    ⟨.and, [274, 9]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.and, [276, 280]⟩,
    ⟨.and, [277, 280]⟩,
    ⟨.and, [278, 280]⟩,
    ⟨.and, [279, 280]⟩,
    ⟨.and, [276, 281]⟩,
    ⟨.and, [277, 281]⟩,
    ⟨.and, [278, 281]⟩,
    ⟨.and, [279, 281]⟩,
    ⟨.and, [276, 282]⟩,
    ⟨.and, [277, 282]⟩,
    ⟨.and, [278, 282]⟩,
    ⟨.and, [279, 282]⟩,
    ⟨.and, [276, 283]⟩,
    ⟨.and, [277, 283]⟩,
    ⟨.and, [278, 283]⟩,
    ⟨.and, [279, 283]⟩,
    ⟨.and, [284, 226]⟩,
    ⟨.and, [285, 229]⟩,
    ⟨.and, [286, 232]⟩,
    ⟨.and, [287, 235]⟩,
    ⟨.and, [288, 238]⟩,
    ⟨.and, [289, 241]⟩,
    ⟨.and, [290, 244]⟩,
    ⟨.and, [291, 247]⟩,
    ⟨.and, [292, 250]⟩,
    ⟨.and, [293, 253]⟩,
    ⟨.and, [294, 256]⟩,
    ⟨.and, [295, 259]⟩,
    ⟨.and, [296, 262]⟩,
    ⟨.and, [297, 265]⟩,
    ⟨.and, [298, 268]⟩,
    ⟨.and, [299, 271]⟩,
    ⟨.or, [300, 301]⟩,
    ⟨.or, [316, 302]⟩,
    ⟨.or, [317, 303]⟩,
    ⟨.or, [318, 304]⟩,
    ⟨.or, [319, 305]⟩,
    ⟨.or, [320, 306]⟩,
    ⟨.or, [321, 307]⟩,
    ⟨.or, [322, 308]⟩,
    ⟨.or, [323, 309]⟩,
    ⟨.or, [324, 310]⟩,
    ⟨.or, [325, 311]⟩,
    ⟨.or, [326, 312]⟩,
    ⟨.or, [327, 313]⟩,
    ⟨.or, [328, 314]⟩,
    ⟨.or, [329, 315]⟩], 330⟩

theorem basis : FanInTwo witness :=
  fanInTwo_of_bool witness (by decide +kernel)

def words (xs : List ℕ) : BitVec 1024 :=
  BitVec.ofNat 1024 (xs.foldr (fun w rest => w + rest * 2 ^ 64) 0)

def inputTables : List (BitVec 1024) := [
  words [0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa],
  words [0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc],
  words [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0],
  words [0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00],
  words [0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000],
  words [0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000],
  words [0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]]

def outputTable : BitVec 1024 := words [0x16c08e9d01086553, 0x5f228a1a1661e142, 0x0d214559df3a7a3b, 0x3ff12536880e2005, 0x333c6632032cc641, 0x7104af4e73674ac1, 0x131c9763826a04c1, 0x5fa43d540228864d, 0x200402040ba4a516, 0x1231033b22d4a481, 0x844b6111c72b9f59, 0xbb3b4061da24bf5c, 0x300182110400001a, 0x1911a13a24848e4c, 0x79153d618684d65b, 0x2014022517e5a747]

set_option maxHeartbeats 10000000 in
theorem hRaw :
    hcsCheckPow (fun r => (inputTables.map fun v => v.getLsbD r) ==
      List.ofFn fun j : Fin 10 => r.testBit j.val) 10 0 = true := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem hGoal :
    hcsCheckPow (fun r => outputTable.getLsbD r ==
      PEqualNP.Represents.adjFun (k := 5) (l := 5)
        (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val))
        (fun j : Fin 10 => r.testBit j.val)) 10 0 = true := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem hEval :
    (witness.gates.foldl hcsStep inputTables).getD witness.output 0 = outputTable := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem eval_eq : ∀ x : Fin 10 → Bool, witness.eval (List.ofFn x) =
    PEqualNP.Represents.adjFun (k := 5) (l := 5)
      (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val)) x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 1024 := hcsBitsNat_lt x
  have hx : x = fun j : Fin 10 => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : inputTables.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin 10 => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (by omega))
  have hfg : outputTable.getLsbD r =
      PEqualNP.Represents.adjFun (k := 5) (l := 5)
        (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val))
        (fun j : Fin 10 => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (by omega))
  have hbits := hcsFoldBits inputTables ⟨r, hr⟩ witness.gates basis
  change (witness.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin 10 => r.testBit j.val)).getD witness.output false = _
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]

end PEqualNP.Outside.L_meta_17145

open PEqualNP.Outside.L_meta_17145 in
theorem PEqualNP.Outside.L_meta_17145 : (PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val))) 330) := by
  exact ⟨witness, basis, by decide +kernel, eval_eq⟩
