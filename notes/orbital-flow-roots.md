# Orbital flow roots on the unit interval and in the complex plane

**The real theorem.** Every open subinterval of $[0,1]$ contains a real root of the univariate orbital flow polynomial of a finite connected simple planar graph. The specified automorphism group can always be the cyclic group of order two.

**The complex theorem.** Every open disk in $\mathbb C$ contains a root of such a polynomial, again with the group fixed to the cyclic group of order two. In both theorems the polynomial is nonzero and the action is faithful.

Peter Cameron asked the real question as Problem 72(2) and in §3.3 of his 14 February 2008 Isaac Newton Institute notes. Cameron and Kayibi proved density on the negative real axis in 2007 and exhibited reciprocals of positive integers as accumulation points in the unit interval. Part (1) of Problem 72 asks a different question about an upper bound on real roots. The complex theorem here concerns approximation by complex roots. I found no earlier proof of the two theorems stated above in the sources searched. Priority remains unconfirmed. [Problem 72](https://cameroncounts.github.io/web/QM/oldprob.html) · [2008 notes](https://citeseerx.ist.psu.edu/document?doi=e0aba325e900e994eecfb1e5a5d11596677521ab&repid=rep1&type=pdf) · [Cameron and Kayibi, §3](https://webspace.maths.qmul.ac.uk/p.j.cameron/preprints/orbitalroots.pdf)

## One symmetry and one extra factor

Orient the edges of a graph $H$. A nowhere-zero flow assigns a nonzero element of a finite abelian group $A$ to every edge, with equal incoming and outgoing totals at every vertex. Write $q=|A|$ and let $F(q)$ count these flows. Take two copies of $H$, identify one distinguished vertex of each, and let the specified involution interchange the copies. This construction preserves planarity and connectedness. Before joining the copies we may replace every edge by a path of length three with two private internal vertices. This gives a simple graph, including when the original graph has loops or parallel edges. Conservation at the new vertices extends each original flow uniquely.

The flow on each copy is independent. Conservation at the common vertex follows separately in each copy by summing all other vertex equations. Thus a flow on the joined graph is an ordered pair of flows on $H$. Swapping copies makes its orbit an unordered pair with repetition allowed. The orbital polynomial is

$$
  P(q)=\frac{F(q)(F(q)+1)}{2}.
$$

This counts orbits for every finite abelian $A$. In particular, its values at positive odd integers give Cameron's univariate orbital polynomial by uniqueness of polynomial interpolation. The graph automorphism moves an edge from the first copy to the second, so the action is faithful. Counting unordered collections of identical blocks already appears in Cameron and Kayibi's negative-axis argument. Here the choice of the blocks controls where $F=-1$. [Original construction, Theorem 3.1](https://webspace.maths.qmul.ac.uk/p.j.cameron/preprints/orbitalroots.pdf)

## A real root in any prescribed interval

Start with a ring consisting of $k$ double-edge stages followed by one single return edge, all oriented consistently. Attach $m-1$ loops at its first vertex, where $m\ge1$. If $k=0$, use a single return loop. A flow chooses a nonzero return current $a$. Each double stage must have currents $b,a-b$, so $b$ can be anything except $0,a$. Each extra loop independently takes any nonzero current. For $q\ge2$ the count is therefore

$$
 F_{m,k}(q)=(q-1)^m(q-2)^k.
$$

It is also correct at $q=1$, where the return edge has no possible current. The graph is planar by drawing the stages around a circle, each parallel edge alongside its partner.

For odd $m$ and even $k$, the equation $F_{m,k}(x)=-1$ on $(0,1)$ becomes

$$
  \frac{-\log(1-x)}{\log(2-x)}=\frac{k}{m}.
$$

The left side increases continuously from zero to infinity. Its positive numerator strictly increases and its positive denominator strictly decreases. The allowed fractions on the right are dense in the positive reals, since their spacing at each odd denominator $m$ is $2/m$. Consequently every open subinterval contains a solution. For instance, $m=1,k=2$ gives $(1-x)(2-x)^2=1$ with its unique solution between $0.534$ and $0.535$. The formal proof obtains the same density by separating endpoint values with integral powers and applying the intermediate value theorem. [Lean theorem and graph witness](../Conjectures/OrbitalFlowTheorem.lean)

## Complex roots inside the disk $|z-1|<1$

Take two parallel rails with common start and finish, a return edge, and $s$ rungs between corresponding interior vertices. Orient both rails forward and all rungs from the upper rail to the lower. For a fixed nonzero return current $a$, write the currents on rail segment $j$ as $b_j,a-b_j$. The rung between successive segments has current $b_j-b_{j+1}$. There are $q-2$ choices of $b_0$. Each later $b_j$ must avoid $0,a,b_{j-1}$, three distinct elements. Add $m$ loops at the start. The resulting planar graph has ordinary polynomial

$$
 H_{m,s}(z)=(z-1)^{m+1}(z-2)(z-3)^s.
$$

For small group orders at which a required initial choice is impossible, both the flow count and the displayed polynomial vanish. Glue $d$ identical ladders at their starting vertices. The ordinary polynomial becomes $H_{m,s}^d$. Its two-copy orbital polynomial has a zero wherever $H_{m,s}^d=-1$.

Inside any open disk $D$ contained in $|z-1|<1$, choose two points $u,v$ on the same vertical line with $|\operatorname{Im}u|<|\operatorname{Im}v|$ and $u\ne1$. Then both distances to $1$ and $3$ strictly increase. Throughout $D$ the first distance is less than one and the second exceeds one. Choose positive integers $i,k$ with

$$
 \frac{\log|u-3|}{-\log|u-1|}
 < \frac{i}{k} <
 \frac{\log|v-3|}{-\log|v-1|}.
$$

It follows that $|(u-1)^i(u-3)^k|<1<|(v-1)^i(v-3)^k|$. For sufficiently large $n$, the polynomial $H=H_{ni,nk}$ still has modulus below one at $u$ and above one at $v$, after including the fixed factors. Its image on the disk crosses the unit circle. Since $H$ is nonconstant and holomorphic, its image is open and hence contains an arc of that circle. The numbers $\exp((2j+1)\pi i/d)$ are dense on the circle as positive $d$ and integer $j$ vary. One belongs to $H(D)$, giving the exact equality $H(w)^d=-1$ for some $w\in D$. Taking closures also covers the boundary. [Lean analysis](../Conjectures/FlowSwapDisk.lean) · [Ladder flow count](../Conjectures/FlowLadder.lean)

## Complex roots outside the disk

Sokal's Theorem 1.1 proves that chromatic roots of equal-length generalized theta graphs are dense outside $|z-1|<1$. A plane dual has ordinary flow polynomial equal to the chromatic polynomial divided by $z$. A root of that flow polynomial survives the two-copy swap because $F$ divides $F(F+1)/2$. This gives the exterior part of the complex theorem directly from published work. [Sokal, 2004](https://arxiv.org/abs/cond-mat/0012369)

The Lean development also proves the exterior case directly. Draw a ring of $p$ stages with $s$ parallel edges in each stage. Conservation forces the same total at every stage. Let $A_s$ count the ways to realize total zero at one stage and $B_s$ the ways to realize one specified nonzero total. Starting from $(A_0,B_0)=(1,0)$, adding an edge gives $A_{s+1}=(q-1)B_s$ and $B_{s+1}=A_s+(q-2)B_s$. The ordinary polynomial is $A_s^p+(q-1)B_s^p$. The recurrence gives

$$
 q A_s=(q-1)^s+(-1)^s(q-1),\qquad
 q B_s=(q-1)^s-(-1)^s.
$$

Write $x=1-z$. For $|x|>1$, the denominators $z$ and $x^s-1$ are nonzero. The polynomial therefore vanishes exactly when $R_s(x)^p=x$, where $R_s(x)=(x^s-x)/(x^s-1)$.

In any disk contained in $|x|>1$, choose $u$ with $u^d=-j$ for integers $d\ge1,j>1$ and $\operatorname{Re}u\ne1$. Such points are dense there. At radius $r>1$, approximate the angle by an odd multiple of $\pi/d$ and the radius by $\lceil r^d\rceil^{1/d}$ as $d\to\infty$. Put $s=2dn$ and $v=u\exp(\pi i/s)$. Then $u^s=j^{2n}$, $v^s=-j^{2n}$ and $v\to u$. For real $a$ and complex $h$,

$$
 |a-h|^2-|a-1|^2=|h|^2-1+2a(1-\operatorname{Re}h).
$$

Taking $(a,h)=(u^s,u)$ and $(v^s,v)$ gives opposite signs when $n$ is large. Thus $R_s$ takes values with moduli on both sides of one inside the disk. Its open image contains an arc of the unit circle and hence a root of unity $\omega=R_s(y)$. Let $k$ be its order. Near $y$ consider the holomorphic function

$$
 L(t)=\frac{\log(R_s(t)/\omega)}{\log(t/y)+\log y}.
$$

The two variable logarithms use the branch analytic at $1$. The constant $\log y$ is nonzero since $|y|>1$. We have $L(y)=0$. If $L$ were constant near $y$, exponentiation and the identity theorem would force $R_s$ to be constant on the disk, despite the different moduli. By the open mapping theorem, $L$ attains $1/p$ there for a sufficiently large multiple $p$ of $k$. Exponentiating gives $R_s(t)^p=t$. This supplies an ordinary flow root in the chosen exterior disk and completes the proof. [Bundle flow count](../Conjectures/FlowBundles.lean) · [Exterior proof](../Conjectures/FlowSokalExterior.lean)

## What Lean checks

The real theorem produces an exact real root in each requested interval. The complex theorem proves density for the explicit ladder and parallel-edge families under the fixed two-copy action. The witnesses include connectedness, simplicity, a faithful group of order two, the graph-induced action on currents, and the equality of the polynomial with actual orbit counts over every finite abelian coefficient group. Both theorems exclude the zero polynomial. The plane drawings above establish planarity of the families. The formal statements do not include an embedding predicate. [Real theorem](../Conjectures/OrbitalFlowTheorem.lean) · [Complex theorem](../Conjectures/OrbitalFlowPlaneTheorem.lean) · [Axiom audit](../Audit.lean)
