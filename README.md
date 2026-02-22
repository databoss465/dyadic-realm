# Interval Arithmetic and Presentation of Non-Trivial Groups

This repository hosts the code for my Bachelor's Thesis project at the Indian Institute of Science, Bengaluru, advised by Prof. Siddhartha Gadgil. The project focuses on building native verification tools within Lean 4 to bridge numerical analysis and algebraic proofs.

### Dyadic Interval Arithmetic

The core of this library is a verified numerical solver that utilizes arithmetic of Dyadic Intervals, $[x, y]$ where $x, y \in \lbrace \frac{a}{2^n} \mid a, n \in \mathbb{Z}, \text{a is odd} \rbrace$. Interval Newton method (for single variable polynomials) and the Krawczyk Method are implemented to solve for Dyadic Intervals containing unique roots of polynomials in several variables.

### Application to Group Theory

The primary application of this solver is to certify the non-triviality of finitely presented groups. By mapping group generators to elements of a compact Lie Group (such as $SU(n), SO(n) $), the group is shown to be non-trivial if there exists a non-trivial root to the group homomorphism.

### References
* Moore, R. E., Kearfott, R. B., & Cloud, M. J. (2009). [*Introduction to Interval Analysis*](http://interval.ict.nsc.ru/Library/InteBooks/IntroIntervAn.pdf)
* Tucker, W. (2011). *Validated Numerics: A Short Introduction to Rigorous Computing*
