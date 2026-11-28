# The degree-five (3,3) layer c=2

The argument as written does not establish the claimed rooted path cover. Hall puts five contacts in R=L∪U, so b,c,d,e need not be in L. In particular if b,c∈U then the operation described as cutting their two L-cover paths and joining these paths through q has no such input paths. Counting b,c first as contacts and then as unused universal separators would use a vertex twice. Even for L contacts, exposing endpoints alone does not ensure they are on distinct pieces.

The following repair proves the same conclusion under precisely the stated conditions. Set u=|U|=k−3, l=|L|=k+1 and let r≤floor((k+1)/2) be the initial number of cover paths of L. Take any five distinct contacts a,b,c,d,e provided by (14), and let j of them lie in U. Orient every initial cover path. At every one of the 5−j L contacts, delete its outgoing edge if present. No resulting piece contains two contacts, because the earlier one along a path has no outgoing edge. Every L contact is the last vertex of its piece. Subdivide additional pieces if necessary to obtain at least five pieces; there are l≥12 vertices, and subdivisions preserve the two properties just proved. The number n of pieces now satisfies
     
    5 ≤ n ≤ max(5,r+5−j).
    
At most 5−j pieces carry L contacts. Match each of the j contacts in U to a distinct contact-free piece and append it at an endpoint using the complete U–L join. Now each of the five contacts is an endpoint of a different piece. Attach the root port p at a, concatenate the b and c pieces through q, and concatenate the d and e pieces through the third port. This produces n−2 paths. One has endpoint p; all other free endpoints are in L. This includes a contact-free piece previously extended by a U contact: once the port is attached, its free end is in L.

Use n−3 of the as-yet-unused U vertices to join the n−2 paths, starting from the p end. This is possible because
     
    j+n−3 ≤ max(j+2,r+2) ≤ max(7,floor((k+1)/2)+2) ≤ k−3 = u
     
for k≥11. Insert any surplus U consecutively into one join; n≥5 guarantees a join exists. This is a rooted spanning path in the selectively closed D. The original leaf-marker reversal recorded in the parent note returns a rooted spanning path in original D. Thus (17) survives without requiring all four internal contacts to lie in L.
