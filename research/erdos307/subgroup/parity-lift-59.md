# Lifting a quadratic witness modulo 59

Let $S$ be a finite set of distinct odd primes omitting 59, with reciprocal mass at least 2. Start with a subset $T$ and fix, as in $T$, the placement of any at most six primes. Among subsets that respect those placements, have the same cardinality parity as $T$, and have the same squared product modulo 59, every reciprocal sum modulo 59 is attained. In particular, fixing three primes on each side preserves minimum side sizes of three.

To apply this to the quadratic condition, let $N=\prod_{p\in S}p$, let $C=N\sum_{p\in S}1/p$, and write $A,B$ and $U,V$ for the respective side products and reciprocal sums in $\mathbb F_{59}$. For a starting subset that gives $A^2+B^2=C$, put $x=A^2$. Choose the reciprocal sum $U=N/x$ by the lifting statement. The complement then has $V=C/N-U=x/N$. It follows that $AU=B$ and $BV=A$.

## Independent choices for the squared product and reciprocal sum

Call a prime ordinary if its residue is outside $\{1,-1\}$. First suppose at least 57 ordinary primes remain after fixing the prescribed placements. Set aside any 57 of them for controlling the squared product and parity. The group of squared products and parities is $\mathbb F_{59}^{\times 2}\times \mathbb Z/2\mathbb Z$, cyclic of order 58. Every ordinary prime contributes a generator $(p^2,1)$, since $p^2$ has order 29 and $1$ has order 2. Each additional independent choose-or-skip generator strictly enlarges the set of attainable group elements until all 58 elements are attained. Indeed equality with its translate by a generator would force any nonempty set to be the whole group. Thus the 57 primes give every desired pair of squared product and parity.

Use the other unreserved primes for reciprocal-sum choices. For an opposite pair of residues $r,-r$ with populations $m,n$, pair $\min(m,n)$ individual primes from opposite classes, and select exactly one from each pair. Both choices have the same squared product and the same parity, and their reciprocal sums differ by $2/r$ up to sign. The leftover primes all have the same residue; divide them into disjoint blocks of length $d_r=2$ if $r=\pm1$ and $d_r=58$ otherwise. Select either all or none of each block. These choices again preserve the squared product and parity, and give a nonzero reciprocal increment. The number of independent reciprocal-sum choices from the two classes is

$$
q_r=\min(m,n)+\left\lfloor\frac{|m-n|}{d_r}\right\rfloor.
$$

Put any leftover primes in the complement. The squared-product and parity contribution of these reciprocal-sum choices is fixed, so the 57 ordinary primes can supply the remaining product and parity. In $\mathbb F_{59}$ each of the reciprocal-sum choices adds a two-point sumset whose nonzero difference generates the additive group. After 58 independent choices all reciprocal sums occur, by the same strict-growth argument.

## Mass certificate for 58 choices

Suppose $\sum q_r\le 57$ and let $K=10^{12}$. The total number of reserved primes is at most 63. For each nonzero residue $r$, let $P_r(k)$ be the sum of the first $k$ eligible prime reciprocals in that residue, each rounded up after scaling by $K$. Use the integer penalty $L=10^9$ and define

$$
F_r(k)=\max_{0\le i\le63}\bigl(P_r(k+i)-Li\bigr).
$$

For an opposite pair let $s=\min(m,n)$ and $q=q_r$. Its larger unreserved population is at most $b=s+d_r(q-s+1)-1$. If $c$ reserved primes are in the pair, monotonicity of $P_r$ bounds the pair's scaled reciprocal mass by $Lc$ plus the larger of $F_r(s)+F_{-r}(b)$ and $F_r(b)+F_{-r}(s)$. Subtract $Lq$ from those last two bounds and maximize them over $0\le s\le q\le57$. Summing the 29 maxima and adding $L(57+63)$ is therefore a scaled upper bound for the mass of any support with at most 57 choices. The companion script gives $1{,}940{,}509{,}126{,}540<2K$. It enumerates prime prefixes with an integer sieve and checks that each class has enough terms for every maximum.

## Fewer than 57 ordinary primes

If fewer than 57 ordinary primes remain and each of the two exceptional classes has at most 116 unfixed primes, then the total support size is at most $56+2\cdot116+6=294$. The same script bounds the mass of the first 294 eligible odd primes above by $1.771968605177$, so this case has reciprocal mass less than 2.

Thus one class $r=\pm1$ has at least 117 unfixed primes. Keep every placement outside that unfixed class from the starting subset. Vary the number of selected unfixed primes in the class through all counts of its original parity. The squared product is unaffected because $r^2=1$. The counts give at least 59 terms in an arithmetic progression of step $2/r$, yielding all 59 reciprocal sums. This proves the lift in the remaining case.
