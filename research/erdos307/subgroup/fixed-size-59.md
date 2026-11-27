# A fixed-size obstruction at the omitted prime 59

There is a set of 6,094 distinct odd primes omitting 59 with reciprocal mass above 2 for which the quadratic condition has a witness with side sizes 3 and 6,091. No partition with those sizes satisfies the two swap equations modulo 59. Keeping the same quadratic root and changing the first side size to 5 gives a witness for both swaps.

Take all odd primes up to 77,933, omitting 59 and any prime with reciprocal residue in

$$
D=\{1,6,15,19,25,27,31,41,48,51,53,58\}.
$$

Adjoin 78,241 and 78,487, whose reciprocal residues are 17 and 7. The support contains all eligible odd primes below 167 and represents all 46 reciprocal classes outside $D$. The integer mass lower bound is

$$
\sum_{p\in S}\lfloor 10^{12}/p\rfloor=2{,}000{,}102{,}412{,}336.
$$

Write $N=\prod_{p\in S}p$ and $C=N\sum_{p\in S}1/p$, computed in the field of order 59. For a partition $S=T\sqcup T^c$ write $A,B$ for the side products and $U,V$ for the side reciprocal sums. The swap equations $AU=B$ and $BV=A$ imply $A^2+B^2=C$, since $AB=N$ and $U+V=C/N$. Thus $x=A^2$ satisfies

$$
x^2-Cx+N^2=0.
$$

Here $N=15$ and $C=30$, so the quadratic is $(x-15)^2$. The side $T=\{3,5,61\}$ has $A=B=30$ and $U=3$, and hence attains the unique root $x=15$.

If a three-element side satisfied both swaps, then $U=B/A=N/x=1$. Its three reciprocal residues $a,b,c$ would satisfy $a+b+c=1$ and $(abc)^2=1/15=4$, so $abc=2$ or $abc=-2$. The entire list of unordered triples in the field is below. The bold entries are in $D$. One can produce the list by looping over $1\le a\le b\le58$, setting $c$ to the least nonnegative residue of $1-a-b$, and retaining the pairs with $b\le c$ and $abc=\pm2$.

| Product | Triples |
|---|---|
| $2$ | (**1**, 23, 36), (3, **15**, 42), (4, 8, **48**), (**6**, 26, 28), (11, 18, **31**), (12, 49, **58**), (**19**, 45, 55) |
| $-2$ | (2, **25**, 33), (3, 9, **48**), (5, **19**, 36), (**6**, 17, 37), (14, 52, **53**), (**15**, 16, 29), (18, 50, **51**), (**27**, 35, 57), (39, 39, **41**) |

All sixteen triples use an excluded class. Interchanging the sides gives the same obstruction if the second side has size 3. The five-element side $\{3,5,7,29,109\}$ has $A^2=15$ and $U=V=1$, so $B=A$ and the two swap equations hold with sizes 5 and 6,089.

The companion script verifies the support statistics, both witnesses and the complete finite search over modular triples using integer arithmetic. The deduction from the unique quadratic root applies to any support with these modular invariants and reciprocal class exclusions.
