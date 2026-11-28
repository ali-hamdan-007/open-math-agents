# The same three-degree theorem for k≥12

Apply three-consecutive-degrees-16.md for k≥16. The following small integer bounds extend it through 12≤k≤15.

The long-leaf case has q≥h=ceil(k/2), 8q+h+2≤5k+1 and, when a=2k−3q≥2, the verified local inequality (a+3)q+h+2a≤5k+1. There is no q obeying all of these: for k=12,13,14,15 the first two bounds respectively allow only q=6,7,7,8. The resulting lower bounds (a+3)q+h+2a are 72,73,91,92 respectively, exceeding 5k+1 in all four cases. The short-leaf lower bound min over b≥h+1 of (max(2,k−b+1)+2)b+3h+1 equals 63,70,74,81 respectively, exceeding 5k+1 in each case. This minimum follows by concavity on h+1≤b≤k−1 and monotonicity thereafter.

In the Hamilton-connected whole-component case, let m=|C| and p its maximum contact matching size. The constraints m≥h+2, p≥max(3,k−m+1) and (p+2)m+p≤5k+1 leave m=k−1,p=3 and m=k−2,p=3 throughout, plus m=k−3,p=4 throughout and m=8,p=5 at k=12. In the latter cases p=k−m+1, so all p covering vertices must be marks, every member of C touches every mark, and C is a clique by degree. The upper bound on total gap excess is σ=5k+1−((p+2)m+p)<p. The already proved endpoint-rotation lemma from common-attachment-clique.md supplies a high endpoint avoiding A on a path with this same vertex set; its degree is ≤m−1+σ<k, impossible.

The finite bound used in the other cases improves as follows: any w with at least k−2 members of C at exact distance two has ≤2 exterior positive-even witnesses. Each such penultimate t hits at most k distance-three targets of w, since all targets adjacent to t are at distance two from any fixed predecessor of t on a shortest path from w. Hence if all contacts of C lie among A' and w neighbors one of A', then

    |V−C|≤1+d(w)+2+2k+(|A'|−1)=d(w)+2k+2+|A'|.

At m=k−1, all preceding three-mark cases produce |A'|≤6 and w seeing ≥k−2 C members. The lower |P|≥4k−1 exceeds 3k+10 as soon as k≥12. The proof in the 16-paper already shows that a three-mark universal C member exists if no mark is itself universal, for k≥10.

At m=k−2, all C members touch the same three marks A and C is a clique. The rooted wedge sum of ../root/rooted-local-ore.md applies to our longest path viewed as rooted at its first vertex. Choose x∈C. With three successor wedges, each ambient endpoint has degree ≥k, hence the sum of the excesses d(succ)−k is ≤3(5k+1−n)/k≤24/k, using n≥5(k−2)+3=5k−7. Since k≥12, at least one successor w has degree k, and w sees all C at distance two. The refined finite bound gives |P|≤3k+5<4k−5, impossible. This completes the proof through k≥12.
