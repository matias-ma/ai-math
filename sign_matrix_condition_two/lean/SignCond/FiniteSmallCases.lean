import SignCond.FiniteMatrix

namespace SignCond.FiniteMatrix.Order1
open Matrix
private def Adata : Array (Array ℚ) := #[#[1]]
private def A : QMat 1 := fun i j => ((Adata)[i.val]!)[j.val]!
private def Ldata : Array (Array ℚ) := #[#[1]]
private def L : QMat 1 := fun i j => ((Ldata)[i.val]!)[j.val]!
private def Udata : Array (Array ℚ) := #[#[1]]
private def U : QMat 1 := fun i j => ((Udata)[i.val]!)[j.val]!
private def ldata : Array ℚ := #[0]
private def l (i : Fin 1) : ℚ := (ldata)[i.val]!
private def udata : Array ℚ := #[29/10]
private def u (i : Fin 1) : ℚ := (udata)[i.val]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness : ∃ (X : Matrix (Fin 1) (Fin 1) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
    (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  exact window A L U l u (1) (39/10) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end SignCond.FiniteMatrix.Order1

namespace SignCond.FiniteMatrix.Order5
open Matrix
private def Adata : Array (Array ℚ) := #[#[-1, 1, 1, 1, 1],
#[1, -1, 1, 1, 1],
#[1, 1, -1, 1, 1],
#[1, 1, 1, -1, 1],
#[1, 1, 1, 1, -1]]
private def A : QMat 5 := fun i j => ((Adata)[i.val]!)[j.val]!
private def Ldata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0],
#[5/12, 1, 0, 0, 0],
#[5/12, 5/17, 1, 0, 0],
#[5/12, 5/17, 5/22, 1, 0],
#[5/12, 5/17, 5/22, 5/27, 1]]
private def L : QMat 5 := fun i j => ((Ldata)[i.val]!)[j.val]!
private def Udata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0],
#[-10/53, 1, 0, 0, 0],
#[-10/53, -10/43, 1, 0, 0],
#[-10/53, -10/43, -10/33, 1, 0],
#[-10/53, -10/43, -10/33, -10/23, 1]]
private def U : QMat 5 := fun i j => ((Udata)[i.val]!)[j.val]!
private def ldata : Array ℚ := #[12/5, 119/60, 154/85, 189/110, 224/135]
private def l (i : Fin 5) : ℚ := (ldata)[i.val]!
private def udata : Array ℚ := #[53/10, 2709/530, 2079/430, 483/110, 819/230]
private def u (i : Fin 5) : ℚ := (udata)[i.val]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness : ∃ (X : Matrix (Fin 5) (Fin 5) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
    (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  exact window A L U l u (13/5) (103/10) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end SignCond.FiniteMatrix.Order5

namespace SignCond.FiniteMatrix.Order7
open Matrix
private def Adata : Array (Array ℚ) := #[#[1, 1, 1, 1, 1, 1, 1],
#[-1, -1, -1, -1, 1, 1, 1],
#[-1, -1, -1, 1, -1, 1, 1],
#[-1, -1, 1, 1, 1, -1, -1],
#[-1, 1, -1, 1, 1, -1, -1],
#[-1, 1, 1, -1, -1, -1, 1],
#[-1, 1, 1, -1, -1, 1, -1]]
private def A : QMat 7 := fun i j => ((Adata)[i.val]!)[j.val]!
private def Ldata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0],
#[-2/7, 1, 0, 0, 0, 0, 0],
#[-2/7, 38/45, 1, 0, 0, 0, 0],
#[-2/7, -2/5, -18/83, 1, 0, 0, 0],
#[-2/7, -2/5, -18/83, 358/441, 1, 0, 0],
#[-2/7, -2/5, -18/83, -34/49, -18/47, 1, 0],
#[-2/7, -2/5, -18/83, -34/49, -18/47, 70/117, 1]]
private def L : QMat 7 := fun i j => ((Ldata)[i.val]!)[j.val]!
private def Udata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0],
#[10/69, 1, 0, 0, 0, 0, 0],
#[10/69, -2170/4661, 1, 0, 0, 0, 0],
#[10/69, 10/79, 590/2491, 1, 0, 0, 0],
#[10/69, 10/79, 590/2491, -88430/158179, 1, 0, 0],
#[10/69, 10/79, 590/2491, 190/2681, 590/3671, 1, 0],
#[10/69, 10/79, 590/2491, 190/2681, 590/3671, -1370/2301, 1]]
private def U : QMat 7 := fun i j => ((Udata)[i.val]!)[j.val]!
private def ldata : Array ℚ := #[7/2, 45/14, 83/90, 441/166, 799/882, 117/94, 187/234]
private def l (i : Fin 7) : ℚ := (ldata)[i.val]!
private def udata : Array ℚ := #[69/10, 4661/690, 246609/46610, 158179/24910, 6905151/1581790, 227799/36710, 30723/7670]
private def u (i : Fin 7) : ℚ := (udata)[i.val]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness : ∃ (X : Matrix (Fin 7) (Fin 7) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
    (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  exact window A L U l u (7/2) (139/10) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end SignCond.FiniteMatrix.Order7

namespace SignCond.FiniteMatrix.Order9
open Matrix
private def Adata : Array (Array ℚ) := #[#[-1, -1, -1, -1, -1, -1, -1, -1, -1],
#[-1, -1, 1, -1, -1, 1, 1, -1, 1],
#[-1, 1, -1, 1, -1, -1, 1, -1, 1],
#[-1, -1, -1, 1, 1, 1, 1, -1, -1],
#[1, -1, 1, 1, -1, -1, -1, -1, -1],
#[1, 1, 1, -1, 1, -1, 1, -1, -1],
#[-1, 1, 1, 1, -1, 1, -1, 1, -1],
#[-1, 1, 1, 1, 1, -1, -1, -1, 1],
#[-1, -1, 1, 1, 1, -1, 1, 1, -1]]
private def A : QMat 9 := fun i j => ((Adata)[i.val]!)[j.val]!
private def Ldata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0, 0, 0],
#[2/11, 1, 0, 0, 0, 0, 0, 0, 0],
#[2/11, 2/13, 1, 0, 0, 0, 0, 0, 0],
#[2/11, 2/13, 2/15, 1, 0, 0, 0, 0, 0],
#[6/11, -34/117, -34/135, -2/9, 1, 0, 0, 0, 0],
#[-2/11, -2/13, -2/15, -2/17, 6/17, 1, 0, 0, 0],
#[-2/11, -2/13, -2/15, -2/17, 6/17, -130/159, 1, 0, 0],
#[-2/11, -2/13, 86/135, -2/9, 2/3, 34/477, 34/87, 1, 0],
#[-2/11, -2/13, -2/15, 2/3, 2/3, 34/477, 34/87, 34/121, 1]]
private def L : QMat 9 := fun i j => ((Ldata)[i.val]!)[j.val]!
private def Udata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0, 0, 0],
#[-10/49, 1, 0, 0, 0, 0, 0, 0, 0],
#[-10/49, -10/39, 1, 0, 0, 0, 0, 0, 0],
#[-10/49, -10/39, -10/29, 1, 0, 0, 0, 0, 0],
#[-30/49, 190/2301, 190/1711, 10/59, 1, 0, 0, 0, 0],
#[10/49, 10/39, 10/29, 10/19, -590/1691, 1, 0, 0, 0],
#[10/49, 10/39, 10/29, 10/19, -590/1691, 9230/41359, 1, 0, 0],
#[10/49, 10/39, -970/1711, 10/59, -10/89, -18810/41359, -190/511, 1, 0],
#[10/49, 10/39, 10/29, -30/59, -10/89, -18810/41359, -190/511, -190/321, 1]]
private def U : QMat 9 := fun i j => ((Udata)[i.val]!)[j.val]!
private def ldata : Array ℚ := #[11/2, 117/22, 135/26, 51/10, 17/6, 159/34, 493/318, 2057/1566, 2635/2178]
private def l (i : Fin 9) : ℚ := (ldata)[i.val]!
private def udata : Array ℚ := #[49/10, 2301/490, 1711/390, 1121/290, 1691/590, 41359/16910, 961191/413590, 603801/301490, 82137/63130]
private def u (i : Fin 9) : ℚ := (udata)[i.val]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness : ∃ (X : Matrix (Fin 9) (Fin 9) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
    (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  exact window A L U l u (7/2) (139/10) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end SignCond.FiniteMatrix.Order9

namespace SignCond.FiniteMatrix.Order11
open Matrix
private def Adata : Array (Array ℚ) := #[#[1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1],
#[1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1],
#[1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1],
#[1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1],
#[1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1],
#[1, -1, 1, -1, -1, 1, -1, 1, 1, 1, 1],
#[1, 1, -1, -1, -1, -1, 1, 1, 1, 1, 1],
#[1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1],
#[-1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1],
#[-1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1],
#[-1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1]]
private def A : QMat 11 := fun i j => ((Adata)[i.val]!)[j.val]!
private def Ldata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[-5/22, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[-5/22, -5/17, 1, 0, 0, 0, 0, 0, 0, 0, 0],
#[-5/22, -5/17, -5/12, 1, 0, 0, 0, 0, 0, 0, 0],
#[-5/22, -5/17, -5/12, 5/9, 1, 0, 0, 0, 0, 0, 0],
#[-5/22, -5/17, -5/12, 5/9, 5/14, 1, 0, 0, 0, 0, 0],
#[-5/22, -5/17, -5/12, 5/9, 5/14, 5/19, 1, 0, 0, 0, 0],
#[-5/22, -5/17, -5/12, 5/9, 5/14, 5/19, 5/24, 1, 0, 0, 0],
#[15/22, -35/459, -35/324, -5/27, -5/42, -5/57, -5/72, -5/87, 1, 0, 0],
#[-5/22, 305/459, -35/324, -5/27, -5/42, -5/57, -5/72, -5/87, -535/3554, 1, 0],
#[-5/22, -5/17, 205/324, -5/27, -5/42, -5/57, -5/72, -5/87, -535/3554, -535/3019, 1]]
private def L : QMat 11 := fun i j => ((Ldata)[i.val]!)[j.val]!
private def Udata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[10/153, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[10/153, 10/163, 1, 0, 0, 0, 0, 0, 0, 0, 0],
#[10/153, 10/163, 10/173, 1, 0, 0, 0, 0, 0, 0, 0],
#[10/153, 10/163, 10/173, -30/143, 1, 0, 0, 0, 0, 0, 0],
#[10/153, 10/163, 10/173, -30/143, -30/113, 1, 0, 0, 0, 0, 0],
#[10/153, 10/163, 10/173, -30/143, -30/113, -30/83, 1, 0, 0, 0, 0],
#[10/153, 10/163, 10/173, -30/143, -30/113, -30/83, -30/53, 1, 0, 0, 0],
#[-10/51, 1830/23309, 1830/24739, 10/143, 10/113, 10/83, 10/53, 10/23, 1, 0, 0],
#[10/153, -4690/23309, 1830/24739, 10/143, 10/113, 10/83, 10/53, 10/23, -170/2199, 1, 0],
#[10/153, 10/163, -5090/24739, 10/143, 10/113, 10/83, 10/53, 10/23, -170/2199, -170/2029, 1]]
private def U : QMat 11 := fun i j => ((Udata)[i.val]!)[j.val]!
private def ldata : Array ℚ := #[22/5, 459/110, 324/85, 63/20, 98/45, 19/10, 168/95, 203/120, 24878/11745, 993251/479790, 30268/15095]
private def l (i : Fin 11) : ℚ := (ldata)[i.val]!
private def udata : Array ℚ := #[153/10, 23309/1530, 24739/1630, 26169/1730, 20679/1430, 15189/1130, 9699/830, 4209/530, 402417/32890, 12748207/1048190, 245037/20290]
private def u (i : Fin 11) : ℚ := (udata)[i.val]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness : ∃ (X : Matrix (Fin 11) (Fin 11) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
    (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  exact window A L U l u (33/5) (263/10) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end SignCond.FiniteMatrix.Order11

namespace SignCond.FiniteMatrix.Order13
open Matrix
private def Adata : Array (Array ℚ) := #[#[-1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1],
#[1, -1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1],
#[1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1],
#[1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1, -1],
#[-1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, 1],
#[1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1],
#[1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1],
#[1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1],
#[1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1],
#[1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1],
#[-1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1],
#[1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1],
#[-1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1]]
private def A : QMat 13 := fun i j => ((Adata)[i.val]!)[j.val]!
private def Ldata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[5/28, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[5/28, 5/33, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 1, 0, 0, 0, 0, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 1, 0, 0, 0, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 1, 0, 0, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 5/58, 1, 0, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 5/58, 5/63, 1, 0, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 5/58, 5/63, 5/68, 1, 0, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 5/58, 5/63, 5/68, 5/73, 1, 0, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 5/58, 5/63, 5/68, 5/73, 5/78, 1, 0],
#[5/28, 5/33, 5/38, 5/43, 5/48, 5/53, 5/58, 5/63, 5/68, 5/73, 5/78, 5/83, 1]]
private def L : QMat 13 := fun i j => ((Ldata)[i.val]!)[j.val]!
private def Udata : Array (Array ℚ) := #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[-2/33, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[-2/33, -2/31, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, 1, 0, 0, 0, 0, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, 1, 0, 0, 0, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, 1, 0, 0, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, -2/21, 1, 0, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, -2/21, -2/19, 1, 0, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, -2/21, -2/19, -2/17, 1, 0, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, -2/21, -2/19, -2/17, -2/15, 1, 0, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, -2/21, -2/19, -2/17, -2/15, -2/13, 1, 0],
#[-2/33, -2/31, -2/29, -2/27, -2/25, -2/23, -2/21, -2/19, -2/17, -2/15, -2/13, -2/11, 1]]
private def U : QMat 13 := fun i j => ((Udata)[i.val]!)[j.val]!
private def ldata : Array ℚ := #[28/5, 759/140, 874/165, 989/190, 1104/215, 1219/240, 1334/265, 1449/290, 1564/315, 1679/340, 1794/365, 1909/390, 2024/415]
private def l (i : Fin 13) : ℚ := (ldata)[i.val]!
private def udata : Array ℚ := #[33/2, 1085/66, 1015/62, 945/58, 875/54, 161/10, 735/46, 95/6, 595/38, 525/34, 91/6, 385/26, 315/22]
private def u (i : Fin 13) : ℚ := (udata)[i.val]!
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem witness : ∃ (X : Matrix (Fin 13) (Fin 13) ℝ) (s : ℚ), IsSign X ∧ 0 < s ∧
    (X * Xᵀ - (s : ℝ) • 1).PosSemidef ∧ ((4*(s : ℝ)) • 1 - X * Xᵀ).PosDef := by
  exact window A L U l u (37/5) (59/2) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end SignCond.FiniteMatrix.Order13
