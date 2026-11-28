import Graph189CompletionRows

namespace Graph189ModerateK3
open SimpleGraph Graph189Completion

set_option maxRecDepth 24000
set_option maxHeartbeats 6000000

def k3p000L := maskGraph 11 [2, 5, 10, 404, 40, 80, 32, 1544, 1544, 1408, 896]
def k3p000U := maskGraph 11 [1150, 1149, 1147, 1527, 1135, 1119, 1087, 1544, 1544, 1408, 1023]
theorem k3p000 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p000L k3p000U := by
  unfold k3p000L k3p000U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 7, 9, 8, 10]) (by decide) (by decide) (by decide))

def k3p001L := maskGraph 11 [2, 5, 10, 916, 40, 80, 32, 1544, 1544, 392, 384]
def k3p001U := maskGraph 11 [1150, 1149, 1147, 2039, 1135, 1119, 1087, 1544, 1544, 1416, 1023]
theorem k3p001 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p001L k3p001U := by
  unfold k3p001L k3p001U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 7, 9, 8, 10]) (by decide) (by decide) (by decide))

def k3p002L := maskGraph 11 [2, 5, 10, 532, 40, 80, 32, 1792, 1664, 392, 384]
def k3p002U := maskGraph 11 [1150, 1149, 1147, 1655, 1135, 1119, 1087, 1792, 1664, 1416, 1023]
theorem k3p002 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p002L k3p002U := by
  unfold k3p002L k3p002U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 9, 7, 8, 10]) (by decide) (by decide) (by decide))

def k3p003L := maskGraph 11 [2, 5, 10, 276, 40, 80, 32, 1792, 648, 1408, 640]
def k3p003U := maskGraph 11 [1150, 1149, 1147, 1399, 1135, 1119, 1087, 1792, 1672, 1408, 1023]
theorem k3p003 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p003L k3p003U := by
  unfold k3p003L k3p003U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 8, 7, 9, 10]) (by decide) (by decide) (by decide))

def k3p004L := maskGraph 11 [2, 5, 10, 788, 40, 80, 32, 1792, 648, 392, 128]
def k3p004U := maskGraph 11 [1150, 1149, 1147, 1911, 1135, 1119, 1087, 1792, 1672, 1416, 1023]
theorem k3p004 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p004L k3p004U := by
  unfold k3p004L k3p004U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 8, 9, 7, 10]) (by decide) (by decide) (by decide))

def k3p005L := maskGraph 11 [2, 5, 10, 148, 40, 80, 32, 776, 1664, 1408, 768]
def k3p005U := maskGraph 11 [1150, 1149, 1147, 1271, 1135, 1119, 1087, 1800, 1664, 1408, 1023]
theorem k3p005 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p005L k3p005U := by
  unfold k3p005L k3p005U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 7, 8, 9, 10]) (by decide) (by decide) (by decide))

def k3p006L := maskGraph 11 [2, 5, 10, 660, 40, 80, 32, 776, 1664, 392, 256]
def k3p006U := maskGraph 11 [1150, 1149, 1147, 1783, 1135, 1119, 1087, 1800, 1664, 1416, 1023]
theorem k3p006 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p006L k3p006U := by
  unfold k3p006L k3p006U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 7, 9, 8, 10]) (by decide) (by decide) (by decide))

def k3p007L := maskGraph 11 [2, 5, 10, 404, 40, 80, 32, 776, 648, 1408, 512]
def k3p007U := maskGraph 11 [1150, 1149, 1147, 1527, 1135, 1119, 1087, 1800, 1672, 1408, 1023]
theorem k3p007 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p007L k3p007U := by
  unfold k3p007L k3p007U
  apply Rejection.path
  exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 3, 7, 8, 9, 10]) (by decide) (by decide) (by decide))

def k3p008L := maskGraph 11 [2, 5, 10, 916, 40, 80, 32, 776, 648, 392, 0]
def k3p008U := maskGraph 11 [1150, 1149, 1147, 2039, 1135, 1119, 1087, 1800, 1672, 1416, 1023]
theorem k3p008 : Rejection (10 : Fin 11) 8 8 3 (fun v => if v=10 then 2 else 3) k3p008L k3p008U := by
  unfold k3p008L k3p008U
  apply Rejection.forbid 2 4
  · exact Or.inl (hasPath_of_list (a := 0) (l := [1, 2, 4, 3, 7, 8, 9]) (by simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, sup_adj, edge_adj, maskGraph, fromRel_adj]; decide) (by decide) (by decide))
  have hu : RowsRepresent (maskRows [1150, 1149, 1131, 2039, 1131, 1119, 1087, 1800, 1672, 1416, 1023]) ((maskGraph 11 [1150, 1149, 1147, 2039, 1135, 1119, 1087, 1800, 1672, 1416, 1023]) \ edge 2 4) := by
    unfold RowsRepresent
    simp only [maskRows, Finset.mem_filter, Finset.mem_univ, true_and, sdiff_adj, edge_adj, maskGraph, fromRel_adj]
    decide
  have hl : RowsRepresent (maskRows [2, 5, 10, 916, 40, 80, 32, 776, 648, 392, 0]) (maskGraph 11 [2, 5, 10, 916, 40, 80, 32, 776, 648, 392, 0]) := maskRows_represent _ (by decide) (by decide)
  exact Rejection.even 2 (hl.excess_of_pairs hu 2 [(7, 3), (8, 3), (9, 3), (4, 3)] (by decide) (by decide) (by decide))

#print axioms k3p000
#print axioms k3p001
#print axioms k3p002
#print axioms k3p003
#print axioms k3p004
#print axioms k3p005
#print axioms k3p006
#print axioms k3p007
#print axioms k3p008
end Graph189ModerateK3
