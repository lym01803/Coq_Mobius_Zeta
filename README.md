# README

##  Compilation Order

```pseudocode
Mobius_Definition.v -> Mobius_Lemmas.v -> Mobius_Lemma2.v -> Mobius_Lemma3.v -> Main.v
```

##  Main Proof Steps

- Theorem 10.11
  - To proof that moving  summation constraint from outside to the inside is valid.
  - To proof that exchanging summation order is valid.
  - To proof $\sum_{Y: Z\subset Y\subset X} (-1)^{|Y|} = 0$.
- Theorem 10.13
  - To proof that for given set $A,B, A\cup B\subset X$, $\sum_{Y: Y\subset X}[A\cup B=Y] = 1$
- Theorem 10.15
  - To proof for given $0\leq k\leq n, \sum_{i=0}^n[i=k] = 1$
  - To proof for given set $A,B,X$, $A\cup B=X \rightarrow (A\cap B=\emptyset \leftrightarrow |A| + |B| = |X|)$
- Theorem 10.12
  - To proof that $\zeta_j f$ can be calculate in a recursive type 
  - To proof that $\zeta_n f$  is the same as $\zeta f$

Theorem 10.14 and 10.16 is about time complexity, we do not proof them. 

