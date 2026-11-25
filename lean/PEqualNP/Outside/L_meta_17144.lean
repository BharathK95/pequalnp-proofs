import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17144

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def bvGateVal (bank : List (BitVec 1024)) (g : Gate) : BitVec 1024 :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes 1024)
  | .or => args.foldr (· ||| ·) 0
  | _ => 0

def bvStep (bank : List (BitVec 1024)) (g : Gate) : List (BitVec 1024) :=
  bank ++ [bvGateVal bank g]

theorem bvGetDBit (bank : List (BitVec 1024)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem bvAndBit (xs : List (BitVec 1024)) (i : Fin 1024) :
    (xs.foldr (· &&& ·) (BitVec.allOnes 1024)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp only [List.foldr_nil, BitVec.getLsbD_allOnes, i.isLt, decide_true, List.map_nil, List.all_nil]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem bvOrBit (xs : List (BitVec 1024)) (i : Fin 1024) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem bvGateBit (bank : List (BitVec 1024)) (i : Fin 1024) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    (bvGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · simp only [bvGateVal, GateOp.eval, bvAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact bvGetDBit bank i.val k
  · simp only [bvGateVal, GateOp.eval, bvOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact bvGetDBit bank i.val k

theorem bvFoldBits (bank : List (BitVec 1024)) (i : Fin 1024) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gs.foldl bvStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (bvStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [bvStep, List.map_append, List.map_cons, List.map_nil,
        bvGateBit bank i g (hmono g List.mem_cons_self).1]
    rw [ih (bvStep bank g) (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')), hstep]

def mono2Bool (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with
     | .and => true
     | .or => true
     | _ => false) && decide (g.inputs.length ≤ 2)

theorem mono2_of_bool (C : Circuit) (h : mono2Bool C = true) : Monotone2 C := by
  intro g hg
  have hall := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  refine ⟨?_, hall.2⟩
  cases hop : g.op <;> simp [hop] at hall ⊢

def witness : Circuit :=
  ⟨[
    ⟨.or, [21, 25]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [24, 28]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [4, 26]⟩,
    ⟨.or, [0, 19]⟩,
    ⟨.or, [18, 65]⟩,
    ⟨.or, [5, 20]⟩,
    ⟨.or, [11, 30]⟩,
    ⟨.or, [1, 64]⟩,
    ⟨.or, [3, 66]⟩,
    ⟨.or, [27, 67]⟩,
    ⟨.or, [17, 70]⟩,
    ⟨.or, [2, 23]⟩,
    ⟨.or, [31, 77]⟩,
    ⟨.or, [16, 68]⟩,
    ⟨.or, [29, 72]⟩,
    ⟨.or, [12, 73]⟩,
    ⟨.or, [71, 75]⟩,
    ⟨.or, [22, 80]⟩,
    ⟨.or, [7, 22]⟩,
    ⟨.or, [9, 18]⟩,
    ⟨.or, [14, 69]⟩,
    ⟨.or, [0, 16]⟩,
    ⟨.or, [76, 82]⟩,
    ⟨.or, [14, 64]⟩,
    ⟨.or, [10, 78]⟩,
    ⟨.or, [3, 72]⟩,
    ⟨.or, [64, 65]⟩,
    ⟨.or, [6, 90]⟩,
    ⟨.or, [74, 84]⟩,
    ⟨.or, [4, 28]⟩,
    ⟨.or, [8, 88]⟩,
    ⟨.or, [69, 91]⟩,
    ⟨.or, [0, 25]⟩,
    ⟨.or, [66, 71]⟩,
    ⟨.or, [4, 74]⟩,
    ⟨.or, [29, 83]⟩,
    ⟨.or, [70, 100]⟩,
    ⟨.or, [9, 92]⟩,
    ⟨.or, [64, 68]⟩,
    ⟨.or, [2, 27]⟩,
    ⟨.or, [24, 65]⟩,
    ⟨.or, [1, 68]⟩,
    ⟨.or, [67, 86]⟩,
    ⟨.or, [1, 12]⟩,
    ⟨.or, [26, 95]⟩,
    ⟨.or, [75, 93]⟩,
    ⟨.or, [13, 79]⟩,
    ⟨.or, [4, 108]⟩,
    ⟨.or, [74, 104]⟩,
    ⟨.or, [29, 85]⟩,
    ⟨.or, [17, 73]⟩,
    ⟨.or, [0, 81]⟩,
    ⟨.or, [87, 113]⟩,
    ⟨.or, [76, 81]⟩,
    ⟨.or, [31, 83]⟩,
    ⟨.or, [23, 99]⟩,
    ⟨.or, [2, 86]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [71, 89]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [29, 123]⟩,
    ⟨.or, [118, 123]⟩,
    ⟨.or, [84, 119]⟩,
    ⟨.or, [75, 98]⟩,
    ⟨.or, [97, 107]⟩,
    ⟨.or, [94, 111]⟩,
    ⟨.or, [89, 119]⟩,
    ⟨.or, [115, 133]⟩,
    ⟨.or, [107, 114]⟩,
    ⟨.or, [69, 117]⟩,
    ⟨.or, [14, 19]⟩,
    ⟨.or, [75, 76]⟩,
    ⟨.or, [88, 109]⟩,
    ⟨.or, [28, 132]⟩,
    ⟨.or, [15, 140]⟩,
    ⟨.or, [24, 90]⟩,
    ⟨.or, [103, 142]⟩,
    ⟨.or, [28, 130]⟩,
    ⟨.or, [67, 102]⟩,
    ⟨.or, [85, 99]⟩,
    ⟨.or, [81, 109]⟩,
    ⟨.or, [108, 145]⟩,
    ⟨.or, [14, 70]⟩,
    ⟨.or, [135, 149]⟩,
    ⟨.or, [8, 67]⟩,
    ⟨.or, [116, 117]⟩,
    ⟨.or, [27, 87]⟩,
    ⟨.or, [72, 103]⟩,
    ⟨.or, [11, 146]⟩,
    ⟨.or, [144, 155]⟩,
    ⟨.or, [95, 98]⟩,
    ⟨.or, [120, 157]⟩,
    ⟨.or, [21, 153]⟩,
    ⟨.or, [73, 148]⟩,
    ⟨.or, [2, 160]⟩,
    ⟨.or, [94, 139]⟩,
    ⟨.or, [152, 162]⟩,
    ⟨.or, [27, 101]⟩,
    ⟨.or, [20, 122]⟩,
    ⟨.or, [126, 137]⟩,
    ⟨.or, [69, 131]⟩,
    ⟨.or, [74, 136]⟩,
    ⟨.or, [138, 168]⟩,
    ⟨.or, [79, 85]⟩,
    ⟨.or, [93, 170]⟩,
    ⟨.or, [101, 147]⟩,
    ⟨.or, [166, 172]⟩,
    ⟨.or, [82, 105]⟩,
    ⟨.or, [96, 121]⟩,
    ⟨.or, [24, 91]⟩,
    ⟨.or, [96, 97]⟩,
    ⟨.or, [115, 177]⟩,
    ⟨.or, [105, 125]⟩,
    ⟨.or, [98, 179]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [69, 181]⟩,
    ⟨.or, [110, 154]⟩,
    ⟨.or, [16, 79]⟩,
    ⟨.or, [174, 175]⟩,
    ⟨.or, [106, 185]⟩,
    ⟨.or, [79, 82]⟩,
    ⟨.or, [76, 80]⟩,
    ⟨.or, [3, 159]⟩,
    ⟨.or, [131, 189]⟩,
    ⟨.or, [151, 183]⟩,
    ⟨.or, [25, 191]⟩,
    ⟨.or, [11, 102]⟩,
    ⟨.or, [92, 114]⟩,
    ⟨.or, [66, 88]⟩,
    ⟨.or, [120, 184]⟩,
    ⟨.or, [94, 196]⟩,
    ⟨.or, [106, 113]⟩,
    ⟨.or, [18, 198]⟩,
    ⟨.or, [100, 111]⟩,
    ⟨.or, [96, 195]⟩,
    ⟨.or, [29, 201]⟩,
    ⟨.or, [15, 194]⟩,
    ⟨.or, [188, 203]⟩,
    ⟨.or, [164, 176]⟩,
    ⟨.or, [68, 124]⟩,
    ⟨.or, [205, 206]⟩,
    ⟨.or, [2, 112]⟩,
    ⟨.or, [70, 208]⟩,
    ⟨.or, [116, 126]⟩,
    ⟨.or, [87, 121]⟩,
    ⟨.or, [139, 200]⟩,
    ⟨.or, [78, 212]⟩,
    ⟨.or, [80, 125]⟩,
    ⟨.or, [118, 214]⟩,
    ⟨.or, [122, 211]⟩,
    ⟨.or, [110, 216]⟩,
    ⟨.or, [124, 165]⟩,
    ⟨.or, [210, 218]⟩,
    ⟨.or, [78, 193]⟩,
    ⟨.or, [26, 220]⟩,
    ⟨.or, [112, 167]⟩,
    ⟨.or, [187, 222]⟩,
    ⟨.and, [32, 150]⟩,
    ⟨.and, [33, 156]⟩,
    ⟨.and, [34, 141]⟩,
    ⟨.and, [35, 169]⟩,
    ⟨.and, [36, 134]⟩,
    ⟨.and, [37, 190]⟩,
    ⟨.and, [38, 199]⟩,
    ⟨.and, [39, 158]⟩,
    ⟨.and, [40, 143]⟩,
    ⟨.and, [41, 173]⟩,
    ⟨.and, [42, 163]⟩,
    ⟨.and, [43, 161]⟩,
    ⟨.and, [44, 171]⟩,
    ⟨.and, [45, 192]⟩,
    ⟨.and, [46, 209]⟩,
    ⟨.and, [47, 180]⟩,
    ⟨.and, [48, 207]⟩,
    ⟨.and, [49, 127]⟩,
    ⟨.and, [50, 219]⟩,
    ⟨.and, [51, 178]⟩,
    ⟨.and, [52, 223]⟩,
    ⟨.and, [53, 129]⟩,
    ⟨.and, [54, 186]⟩,
    ⟨.and, [55, 197]⟩,
    ⟨.and, [56, 182]⟩,
    ⟨.and, [57, 202]⟩,
    ⟨.and, [58, 221]⟩,
    ⟨.and, [59, 204]⟩,
    ⟨.and, [60, 217]⟩,
    ⟨.and, [61, 215]⟩,
    ⟨.and, [62, 213]⟩,
    ⟨.and, [63, 128]⟩,
    ⟨.or, [224, 225]⟩,
    ⟨.or, [256, 226]⟩,
    ⟨.or, [257, 227]⟩,
    ⟨.or, [258, 228]⟩,
    ⟨.or, [259, 229]⟩,
    ⟨.or, [260, 230]⟩,
    ⟨.or, [261, 231]⟩,
    ⟨.or, [262, 232]⟩,
    ⟨.or, [263, 233]⟩,
    ⟨.or, [264, 234]⟩,
    ⟨.or, [265, 235]⟩,
    ⟨.or, [266, 236]⟩,
    ⟨.or, [267, 237]⟩,
    ⟨.or, [268, 238]⟩,
    ⟨.or, [269, 239]⟩,
    ⟨.or, [270, 240]⟩,
    ⟨.or, [271, 241]⟩,
    ⟨.or, [272, 242]⟩,
    ⟨.or, [273, 243]⟩,
    ⟨.or, [274, 244]⟩,
    ⟨.or, [275, 245]⟩,
    ⟨.or, [276, 246]⟩,
    ⟨.or, [277, 247]⟩,
    ⟨.or, [278, 248]⟩,
    ⟨.or, [279, 249]⟩,
    ⟨.or, [280, 250]⟩,
    ⟨.or, [281, 251]⟩,
    ⟨.or, [282, 252]⟩,
    ⟨.or, [283, 253]⟩,
    ⟨.or, [284, 254]⟩,
    ⟨.or, [285, 255]⟩], 286⟩

theorem mono : Monotone2 witness :=
  mono2_of_bool witness (by decide +kernel)

def colBase : Nat :=
  0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001

def rawInputs : List (BitVec 1024) :=
  List.ofFn (fun u : Fin 32 => BitVec.ofNat 1024 ((2 ^ 32 - 1) <<< (32 * u.val))) ++
  List.ofFn (fun v : Fin 32 => BitVec.ofNat 1024 (colBase <<< v.val))

def graphNum : Nat :=
  0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573

def checkRowBit (u : Fin 32) (idx : Nat) : Bool :=
  (BitVec.ofNat 1024 ((2 ^ 32 - 1) <<< (32 * u.val))).getLsbD idx

def checkColBit (v : Fin 32) (idx : Nat) : Bool :=
  (BitVec.ofNat 1024 (colBase <<< v.val)).getLsbD idx

set_option maxHeartbeats 10000000 in
theorem hRowBits :
    ∀ (i u v : Fin 32), checkRowBit i (32 * u.val + v.val) = decide (i = u) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
theorem hColBits :
    ∀ (j u v : Fin 32), checkColBit j (32 * u.val + v.val) = decide (j = v) := by
  decide +kernel

theorem rawInputs_bit (u v : Fin 32) :
    rawInputs.map (fun w => w.getLsbD (32 * u.val + v.val)) = oneEach u v := by
  simp only [rawInputs, oneEach, List.map_append, List.map_ofFn]
  congr 1
  · apply List.ext_getElem
    · simp only [List.length_ofFn]
    · intro idx h1 h2
      simp only [List.length_ofFn] at h2
      simp only [List.getElem_ofFn, Function.comp_apply]
      exact hRowBits ⟨idx, h2⟩ u v
  · apply List.ext_getElem
    · simp only [List.length_ofFn]
    · intro idx h1 h2
      simp only [List.length_ofFn] at h2
      simp only [List.getElem_ofFn, Function.comp_apply]
      exact hColBits ⟨idx, h2⟩ u v

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem hEval :
    (witness.gates.foldl bvStep rawInputs).getD witness.output 0 = BitVec.ofNat 1024 graphNum := by
  decide +kernel

theorem rep_ok : Represents (fun u v : Fin 32 => Nat.testBit graphNum (32 * u.val + v.val)) witness := by
  intro u v
  have hlt : 32 * u.val + v.val < 1024 := by omega
  have hbank := rawInputs_bit u v
  have hbits := bvFoldBits rawInputs ⟨32 * u.val + v.val, hlt⟩ witness.gates mono
  change (witness.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (oneEach u v)).getD witness.output false = Nat.testBit graphNum (32 * u.val + v.val)
  rw [← hbank, ← hbits, ← bvGetDBit, hEval, BitVec.getLsbD_ofNat]
  simp [hlt]

end PEqualNP.Outside.L_meta_17144

open PEqualNP.Outside.L_meta_17144 in
theorem PEqualNP.Outside.L_meta_17144 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 32 => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val)) 224) := by
  exact ⟨witness, mono, by decide +kernel, rep_ok⟩
