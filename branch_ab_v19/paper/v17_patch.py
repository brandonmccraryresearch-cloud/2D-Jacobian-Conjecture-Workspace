#!/usr/bin/env python3
"""v17 manuscript patch: insert the algebraic, Lean-formalized proof of Proposition 6.1 (m = 7).

Applies exact-string replacements to branch_ab_elimination_v3.tex (each must match exactly once)
and inserts the new subsection \\ref{sec:chartproof} before Section 7. The mechanical listings
lst:proofchartclass, lst:unconditional, lst:lczero are then filled by scripts/gen_listings_v10.py.
Usage: python3 v17_patch.py branch_ab_elimination_v3.tex
"""
import sys
p = sys.argv[1]
s = open(p, encoding='utf-8').read()

def rep(old, new):
    global s
    n = s.count(old)
    assert n == 1, f"expected exactly one match ({n}) for: {old[:90]}"
    s = s.replace(old, new)

# 1. Abstract: top layer and logical status
rep(r"""The $35$ solutions are distinct and form a single Galois orbit: one real solution and $17$ conjugate pairs, in five $S$-orbits.""",
    r"""The $35$ solutions are distinct and form a single Galois orbit: one real solution and $17$ conjugate pairs, in five $S$-orbits. For $m=7$ we also give an algebraic proof of this classification, valid over every field of characteristic~$0$. In reversed coordinates the chart equations are the coefficient recursion of $(1+y_1v+\dots+y_7v^7)^{3/2}$. Six weighted-homogeneous relations, of weights $4,5,5,6,6,7$ and with explicit certificates, cut out the five torus orbits. We formalize this proof in Lean.""")
rep(r"""Hence no polynomials $P,Q$ satisfying $\mathrm{NewtonNF2}$ have $[P,Q]=\lambda x^2$ with $\lambda\neq0$ (Theorem~\ref{thm:main}; the $b_{12,24}=0$ part follows from \texttt{no\_completion\_K5\_PQ} together with \texttt{topLayerClassification\_of\_chart}, only the NewtonNF2 form is itself a single kernel-checked theorem (\texttt{main\_theorem\_of\_chart}) conditional on \texttt{ChartClassification}; the $a_{8,16}=0$ part is computer algebra).""",
    r"""Hence no polynomials $P,Q$ satisfying $\mathrm{NewtonNF2}$ have $[P,Q]=\lambda x^2$ with $\lambda\neq0$ (Theorem~\ref{thm:main}). In Lean this NewtonNF2 form is a single unconditional kernel-checked theorem, \texttt{main\_theorem}, on the standard axioms only. Its top-layer input is \texttt{chartClassification\_holds}, a formalized algebraic proof of the $m=7$ top-layer classification of Proposition~\ref{prop:top-class}, in the normalized chart (\S\ref{sec:chartproof}). The $a_{8,16}=0$ part is computer algebra.""")

# 2. Introduction: proof overview
rep(r"""determine the top layer via the Belyi-map/Riemann-existence argument (Figure~\ref{fig:top}), and obstruct the descent via the Lean-formalized layer certificates (\S\ref{sec:descent}).""",
    r"""determine the top layer via the Belyi-map/Riemann-existence argument (Figure~\ref{fig:top}), and independently by an algebraic argument formalized in Lean (\S\ref{sec:chartproof}). We then obstruct the descent via the Lean-formalized layer certificates (\S\ref{sec:descent}).""")

# 3. Remark 1.3 (conditional status -> logical status)
rep(r"""\subsection{Conditional status}""", r"""\subsection{Logical status}""")
rep(r"""Theorem~\ref{thm:main} does not depend on GGHV. Its proof uses Proposition~6.1,
which is proved on paper via Riemann's existence theorem and is not formalized.
In Lean, \texttt{main\_theorem\_of\_chart} (listing~\ref{lst:chart}) assumes the
explicit statement \texttt{ChartClassification} (listing~\ref{lst:def-chartclass})
in place of Proposition~6.1, and every other step is checked by the kernel.
The $b_{12,24}=0$ part follows from \texttt{no\_completion\_K5\_PQ} together with \texttt{topLayerClassification\_of\_chart} (only the NewtonNF2 form is itself a single kernel-checked theorem, \texttt{main\_theorem\_of\_chart}); the $a_{8,16}=0$ part is computer""",
    r"""Theorem~\ref{thm:main} does not depend on GGHV. Its proof uses Proposition~6.1 for $m=7$,
which is proved twice. On paper it follows from Riemann's existence theorem
(\S\ref{sec:top}). In \S\ref{sec:chartproof} the classification it provides is proved
algebraically, in the normalized chart, and that proof is formalized in Lean as
\texttt{chartClassification\_holds} (listing~\ref{lst:proofchartclass}).
In Lean, \texttt{main\_theorem\_of\_chart} (listing~\ref{lst:chart}) derives the NewtonNF2 form of
Theorem~\ref{thm:main} from the explicit statement \texttt{ChartClassification}
(listing~\ref{lst:def-chartclass}). \texttt{main\_theorem} (listing~\ref{lst:unconditional})
combines it with \texttt{chartClassification\_holds} into a single unconditional kernel-checked
theorem, and \texttt{\#print axioms} reports only \texttt{propext}, \texttt{Classical.choice}
and \texttt{Quot.sound}.
The $b_{12,24}=0$ part follows from \texttt{no\_completion\_K5\_PQ} together with \texttt{topLayerClassification\_of\_chart} and \texttt{chartClassification\_holds}; the $a_{8,16}=0$ part is computer""")

# 4. Remark on the status of ChartClassification
rep(r"""It is presented here as an \emph{unproven hypothesis} corresponding to paper-level Proposition~6.1. The Lean theorem \texttt{main\_theorem\_of\_chart} has the form $\texttt{ChartClassification}\ L \to \lnot\exists\dots$; if any of the $17$ equations contained a typo, the hypothesis could be false and the implication vacuously true. The equations were verified against the \texttt{chart\_system\_Q.sing} Singular script (see the computational archive).""",
    r"""Up to v16 of the artifact it was an unproven hypothesis standing for the case $m=7$ of Proposition~6.1. It is now a theorem, \texttt{chartClassification\_holds} (\S\ref{sec:chartproof}), so the implication $\texttt{ChartClassification}\ L \to \lnot\exists\dots$ of \texttt{main\_theorem\_of\_chart} is discharged and cannot be vacuous. The statement itself is unchanged. Its $17$ equations were verified against the \texttt{chart\_system\_Q.sing} Singular script and by the mechanical chart audit (see the computational archive). The generator of the proof in \S\ref{sec:chartproof} reads this same statement from the Lean source.""")

# 5. New subsection before Section 7
NEW = r"""
\subsection{An algebraic proof of the top-layer classification for $m=7$, and its formalization}\label{sec:chartproof}

The proof of Proposition~\ref{prop:top-class} above rests on Riemann's existence theorem, which is not in Mathlib (at least not in the version pinned by the artifact). For $m=7$ we now give a second proof of the classification it provides, in the normalized chart of \S\ref{sec:normalization}: every solution is one of the points $(P_j(w),Q_k(w))$ with $R(w)=0$, the five $K_5$-conjugates. This is the form in which the main theorem uses Proposition~\ref{prop:top-class}. The eliminant $\mathcal{W}$ and the cases $m=3,5$ are not reproved here. The proof is purely algebraic and valid over every field of characteristic~$0$, and it is formalized: Theorem~\ref{thm:chartclass} is the Lean theorem \texttt{chartClassification\_holds} (listing~\ref{lst:proofchartclass}). We work in the Lean chart of \S\ref{sec:normalization}: $\alpha=1+a_1u+\dots+a_7u^7$, $\beta=b_0+b_1u+\dots+b_9u^9+u^{10}$, and $E_n=\sum_{i+k=n}(1+2k-3i)\,a_ib_k$ ($1\le n\le 16$) is the coefficient of $u^n$ in $\alpha\beta+u(2\alpha\beta'-3\alpha'\beta)$.

\begin{theorem}[\texttt{chartClassification\_holds}]\label{thm:chartclass}
Let $L$ be a field of characteristic~$0$. Suppose $(a_1,\dots,a_7,b_0,\dots,b_9)\in L^{17}$ satisfies $E_1=\dots=E_{16}=0$ and $a_7^3b_0^2=1$. Then $(a_j,b_k)=(P_j(w),Q_k(w))$ for a root $w\in L$ of $R$. Here $P_j,Q_k\in\mathbb{Q}[w]$ are the coordinates in listing~\ref{lst:def-chartclass}.
\end{theorem}

\begin{proof}
\emph{Step 1: reversed coordinates.} Since $a_7^3b_0^2=1$, we have $a_7\neq0$. Put $y_i=a_{7-i}/a_7$ for $1\le i\le 6$ and $y_7=1/a_7$, and give $y_i$ the weight~$i$. Define $S_k\in\mathbb{Q}[y_1,\dots,y_7]$, weighted homogeneous of weight~$k$, by
\[
(1+y_1v+\dots+y_7v^7)^{3/2}=\sum_{k\ge0}S_k\,v^k ,
\]
or, equivalently, by $S_0=1$ and $2k\,S_k=\sum_{i=1}^{7}(5i-2k)\,y_i\,S_{k-i}$. Write $\tilde\beta_k=b_{10-k}$ for $0\le k\le 10$ (so $\tilde\beta_0=1$) and $\tilde\beta_k=0$ for $k>10$; in both recursions, terms with a negative index are zero. Reindexing $E_{17-k}$ by $i\mapsto 7-i$, $k\mapsto 10-k$ gives
\[
E_{17-k}/a_7=-2k\,\tilde\beta_k+\sum_{i=1}^{7}(5i-2k)\,y_i\,\tilde\beta_{k-i}\qquad(1\le k\le 16).
\]
This is the recursion for $S_k$. Induction on $k$ gives $b_{10-k}=S_k(y)$ for $1\le k\le 10$, and
\begin{equation}\label{eq:Ssystem}
S_{11}(y)=\dots=S_{16}(y)=0,\qquad S_{10}(y)^2=y_7^3 .
\end{equation}
The last equation holds because $b_0=S_{10}(y)$ and $a_7^3b_0^2=1$. In the language of \S\ref{sec:top}, the reversed $\beta$ is the truncation of the power-series square root of the reversed $\alpha^3/a_7^3$. This is the Davenport--Stothers condition.

\emph{Step 2: the orbit relations.} Consider the six weighted-homogeneous relations
\begin{align*}
y_4&=\tfrac{2431}{18240}y_1^4-\tfrac{1027}{1710}y_1^2y_2+\tfrac{143}{380}y_2^2+\tfrac{41}{60}y_1y_3,\\
y_5&=\tfrac{1154351}{25313472}y_1^5-\tfrac{3833107}{18985104}y_1^3y_2+\tfrac{6512}{43947}y_1y_2^2+\tfrac{24449}{166536}y_1^2y_3,\\
y_6&=\tfrac{4206749569}{4242031637760}y_1^6+\tfrac{8589189473}{1590761864160}y_1^4y_2-\tfrac{440013827}{9819517680}y_1^2y_2^2\\&\qquad+\tfrac{7454351}{734423760}y_1^3y_3+\tfrac{253}{5054}y_2^3,\\
y_7&=-\tfrac{4539711243127}{16353031963564800}y_1^7+\tfrac{13373800868041}{6132386986336800}y_1^5y_2-\tfrac{214713769679}{37854240656400}y_1^3y_2^2\\&\qquad+\tfrac{81661753}{707800898700}y_1^4y_3+\tfrac{92333}{19483170}y_1y_2^3,\\
y_2y_3&=\tfrac{3738317}{46630080}y_1^5-\tfrac{16882087}{34972560}y_1^3y_2+\tfrac{115021}{161910}y_1y_2^2+\tfrac{2277881}{5828760}y_1^2y_3,\\
y_3^2&=\tfrac{740761013029}{10605079094400}y_1^6-\tfrac{754440973541}{1988452330200}y_1^4y_2+\tfrac{3827878261}{8182931400}y_1^2y_2^2\\&\qquad+\tfrac{137816863}{918029700}y_1^3y_3+\tfrac{289}{12635}y_2^3 .
\end{align*}
Write $g=0$ for any of them. Each satisfies
\[
y_7^3\cdot g\in(S_{11},\dots,S_{16})\subset\mathbb{Q}[y_1,\dots,y_7],
\]
with explicit cofactors of $341$ to $694$ terms, whose numerators and denominators have at most $42$ digits. Since $y_7\neq0$, every solution of~\eqref{eq:Ssystem} satisfies all six relations.

The relations were found by exact interpolation on the $K_5$ point, as all weighted-homogeneous forms of weight at most~$7$ that vanish on the five orbits. The cofactors come from exact weighted-homogeneous linear algebra over $\mathbb{Q}$. Let $(g)$ be the ideal of the six relations. A Gr\"obner computation over $\mathbb{Q}$ (\filename{saturation\_check.py}) shows that $(S_{11},\dots,S_{16})\subseteq(g)$ and $(g):y_7=(g)$. With the certificates this gives
\[
(S_{11},\dots,S_{16}):y_7^\infty=(S_{11},\dots,S_{16}):y_7^3=(g).
\]
The ideal $(g)$ has Krull dimension~$1$ and needs all six generators, so it is a weighted complete intersection. It has exactly five solutions in the chart $y_1=1$ and none with $y_1=0$ other than $y=0$, in agreement with weighted B\'ezout, $4\cdot5\cdot5\cdot6\cdot6\cdot7/7!=5$. These facts explain the choice of relations but are not used in the proof.

\emph{Step 3: a resultant.} The relation for $y_7$ shows $y_7\in y_1\,\mathbb{Q}[y_1,y_2,y_3]$, so $y_1\neq0$. Put $t=y_2/y_1^2$ and $s=y_3/y_1^3$. The relation for $y_2y_3$ becomes $(t-c)\,s=N(t)$ with $c=\tfrac{2277881}{5828760}$ and $\deg N=2$, and the relation for $y_3^2$ becomes monic quadratic in~$s$. Their Sylvester resultant in $s$ is $\kappa\,m(t)$ with $\kappa\in\mathbb{Q}^\times$ and
\[
\begin{aligned}
m(t)={}&287548593020928\,t^5-688401965085696\,t^4+640652914818432\,t^3\\
&-292066554895024\,t^2+65563255857792\,t-5817852446211,
\end{aligned}
\]
which is irreducible over $\mathbb{Q}$. Hence $t-c$ is invertible modulo~$m$, and $s=q_3(t)$. The first four relations then give $y_i/y_1^i=q_i(t)$ for $4\le i\le 7$, with $q_i\in\mathbb{Q}[t]$ reduced modulo~$m$.

\emph{Step 4: the torus.} Let $z=1/y_1$. By weighted homogeneity,
\[
z^{10}S_{10}(y)=S_{10}\bigl(1,t,q_3(t),\dots,q_7(t)\bigr)\equiv\sigma(t)\pmod m\qquad\text{and}\qquad z^7y_7=q_7(t).
\] Multiplying $S_{10}^2=y_7^3$ by $z^{21}$ gives $z\,\sigma(t)^2=q_7(t)^3$, that is,
\[
y_1=\sigma(t)^2\,q_7(t)^{-3}\bmod m(t).
\]
This fixes the torus without a seventh root, as in \S\ref{sec:normalization}, and makes every $y_i$ a polynomial in $t$ modulo~$m$. The substitution $w=\omega(t)$, with $\omega\in\mathbb{Q}[t]$ of degree~$4$, induces an isomorphism $\mathbb{Q}[t]/(m)\cong\mathbb{Q}[w]/(R)=K_5$ and gives $R(w)=0$ and $y_i=Y_i(w)$.

\emph{Step 5: back to the chart.} The formulas $a_7=1/y_7$ and $a_{7-i}=y_i/y_7$, together with the recursion of Step~1 for $b_{10-k}$, give $a_j=P_j(w)$ and $b_k=Q_k(w)$.
\end{proof}

\begin{remark}[Formalization]\label{rem:chartproof-lean}
The proof is formalized in \filename{lean/Jacobian/ChartProof/}: $12$ modules, all generated by \filename{lean/certgen/chartproof/} except the hand-written \filename{Reflect.lean}.
\begin{itemize}[nosep]
\item \emph{Steps.} There are $111$ steps. In $105$ of them a polynomial $g$ vanishes because $g=\sum_i c_ie_i$ for polynomials $e_i$ already known to vanish. In the other six, one for each relation of Step~2, the identity $y_7^3\,g=e$ holds with $e$ already known to vanish, and $y_7^3$ is cancelled using $y_7\neq0$.
\item \emph{Kernel checking.} Every identity is checked by the Lean kernel. \texttt{lc\_zero} (listing~\ref{lst:lczero}) and \texttt{eq\_of\_toPolyK} reduce it to an equality of normal forms. These are computed by the verified normalizer of \texttt{Lean.Grind.CommRing} from Lean core, with a kernel-friendly multiplication defined by recursors (\texttt{toPolyK}, soundness theorem \texttt{denote\_toPolyK}), and \texttt{decide +kernel} evaluates them.
\item \emph{Axioms.} No \texttt{native\_decide} is used. \texttt{\#print axioms} for \texttt{chartClassification\_holds} and for \texttt{main\_theorem} reports only \texttt{propext}, \texttt{Classical.choice} and \texttt{Quot.sound}.
\item \emph{Batching.} The certificates of Step~2 have between $27{,}747$ and $56{,}999$ monomial products each. They are split into batches of at most $9{,}000$ products, one declaration per batch.
\item \emph{Independent checks.} Every certificate was also verified by exact SymPy expansion before it was written, and the generator reproduces all eleven generated modules byte-identically. A second checker, written independently of the generator (\filename{independent\_check.py}), parses the Lean text and re-verifies all $111$ identities over $\mathbb{Z}$. Six controls behave as expected: four one-integer perturbations are rejected by \texttt{decide}, a planted \texttt{sorry} is flagged, and an unmodified module is accepted.
\item \emph{Cost.} The build takes about $25$ minutes sequentially and needs at most $5.4$\,GB of memory for any one module.
\end{itemize}
\end{remark}

\begin{remark}[Why these coordinates]
Earlier formulations failed to yield certificates of practical size because of the degenerate Davenport--Stothers components of lower degree (the solutions for $m=1,3,5$). With $a_0=b_0=1$ and $b$ eliminated, these components force saturation by $a_7^7$ or $a_7^8$, so the certificates have weight~$61$. In the chart $a_0=b_{10}=1$, the sub-case $a_1=0$ alone needed $503{,}254$ cofactor terms modulo a prime. Replayed over~$\mathbb{Q}$, its Buchberger trace reached coefficients of $2{,}722$ digits after $929$ of its $2{,}065$ elements (\filename{lean/CLASSIFICATION\_STATUS.md}, \S5). In the reversed coordinates the same components lie on $y_7=0$, and $y_7^3$ suffices, at weight at most~$28$. The five orbits then form a weighted complete intersection that can be written down explicitly. The six certificates of Step~2 have $341$ to $694$ cofactor terms each over~$\mathbb{Q}$, roughly a thousand times fewer than the modular lift for $a_1=0$ alone.
\end{remark}

% keep the caption of the next listing on the same page as its code
\par\vskip 0pt plus 8\baselineskip\penalty-200\vskip 0pt plus -8\baselineskip\relax
% BEGIN-MECHANICAL:lst:proofchartclass
% END-MECHANICAL:lst:proofchartclass
% BEGIN-MECHANICAL:lst:unconditional
% END-MECHANICAL:lst:unconditional
% BEGIN-MECHANICAL:lst:lczero
% END-MECHANICAL:lst:lczero

"""
rep("\\section{Descent}\\label{sec:descent}", NEW + "\\section{Descent}\\label{sec:descent}")

# 6. "given Proposition 6.1" qualifiers
rep(r"""covering all top-layer solutions given Proposition~6.1.
\end{enumerate}""", r"""covering all top-layer solutions by Proposition~6.1, whose $m=7$ classification is formalized (\texttt{chartClassification\_holds}, \S\ref{sec:chartproof}).
\end{enumerate}""")
rep(r"""\item exact $K_5$-descent (Lean \texttt{no\_completion\_K5} via \texttt{main\_theorem\_of\_chart}) covering all roots of $R$ and all torus parameters, given Proposition~6.1.""",
    r"""\item exact $K_5$-descent (Lean \texttt{no\_completion\_K5} via \texttt{main\_theorem\_of\_chart}) covering all roots of $R$ and all torus parameters;
\item an algebraic proof of the $m=7$ top-layer classification (Proposition~6.1 in the normalized chart), using reversed coordinates, six orbit relations and a Sylvester resultant (\S\ref{sec:chartproof}). It is formalized in Lean, so the NewtonNF2 form of Theorem~\ref{thm:main} is the unconditional kernel-checked theorem \texttt{main\_theorem}.""")
rep(r"""holds for every solution of the top-layer system given Proposition~6.1, not just the $K_5$-point.""",
    r"""holds for every solution of the top-layer system by Proposition~6.1 (for $m=7$ formalized as \texttt{chartClassification\_holds}), not just the $K_5$-point.""")

# 7. Attribution
rep(r"""and the independent Lean build. Claude also performed the independent blind replication""",
    r"""and the independent Lean build. During the v17 review Claude also found the algebraic proof of the $m=7$ top-layer classification in \S\ref{sec:chartproof} (the reversed coordinates, the six orbit relations and their certificates) and wrote its Lean formalization (\filename{lean/Jacobian/ChartProof}, with the generator \filename{lean/certgen/chartproof}). Claude further performed the independent blind replication""")

# 8. Computational archive
rep(r"""\item $E_2$ rank verification (injectivity of the $19\times12$ operator).
\end{itemize}""",
    r"""\item $E_2$ rank verification (injectivity of the $19\times12$ operator).
\end{itemize}
The generator of the Lean proof of Theorem~\ref{thm:chartclass} (\S\ref{sec:chartproof}) ships with the Lean project, in \filename{lean/certgen/chartproof/}. It finds the orbit relations by exact interpolation, computes the certificates by weighted-homogeneous linear algebra over $\mathbb{Q}$, and verifies all $105$ step identities in SymPy; \filename{regenerate\_chartproof.sh} checks byte-identical regeneration.""")

# 9. "What remains": only the Jacobian-conjecture corollary depends on GGHV (consistent with Remark 1.3)
rep(r"""The result is conditional on~\cite[Proposition~4.3]{GGHV} (Remark~\ref{rem:conditional}).""",
    r"""The application of Theorem~\ref{thm:main} to the Jacobian conjecture, Corollary~\ref{cor:gghv}, is conditional on~\cite[Proposition~4.3]{GGHV} (Remark~\ref{rem:conditional}).""")

open(p, 'w', encoding='utf-8').write(s)
print("v17 patch applied")
