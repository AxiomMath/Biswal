We consider the sequende of polynomials
\[
p_0(x)=p_1(x)=1,\qquad p_{n+1}(x)=p_n(x)-x p_{n-1}(x)\quad (n\ge 1).
\]
Equivalently, we have that
\[
p_n(x)=x^{n/2}U_n\!\left((2\sqrt{x})^{-1}\right),
\]
where $U_n$ denotes the Chebyshev polynomial of the second kind. For an integer partition
$\xi=(\xi_1\ge \xi_2\ge \cdots \ge \xi_\ell>0)$, set
\[
p_\xi(x):=\prod_{i=1}^\ell p_{\xi_i}(x).
\]
Fix $m\ge 1$, we make the convention that
\[
n=n_1m+n_0,\qquad 0\le n_0<m,
\]
and we define
\[
F(x)=\frac{p_{m-n_0-1}(x)p_\xi(x)}{p_m(x)^{n_1+1}}=\sum_{r\ge 0} a_r x^r.
\]

The purpose of this note is to establish a certain positivity statement for the coefficients $a_r$.


\begin{problem}\label{thm:mainthm}
Fix $m\ge 1$, let $\xi$ be a partition with $\xi_i\le m$ for all $i$, write
\[
n=n_1m+n_0,\qquad 0\le n_0<m,
\]
and set
\[
F(x)=\frac{p_{m-n_0-1}(x)p_\xi(x)}{p_m(x)^{n_1+1}}=\sum_{r\ge 0}a_rx^r.
\]
If we let
\[
t:=\#\{i: \xi_i=m\},
\]
then prove that the following are true:
\begin{enumerate}
\item If $m=1$, then $F(x)=1$.
\item Assume $m\ge 2$.
  \begin{enumerate}
  \item If $t\ge n_1+1$, then $F(x)$ is a polynomial. In particular, $a_r=0$ for all
  sufficiently large $r$.
  \item If $t\le n_1$, then $a_r>0$ for all sufficiently large $r$.
  \end{enumerate}
\end{enumerate}
\end{problem}
