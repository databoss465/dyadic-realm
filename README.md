# Automated Root Certification in Lean for Transversal Polynomial Systems

This repository hosts the code for my Bachelor's Thesis project at the Indian Institute of Science, under the supervision of Prof. Siddhartha Gadgil. The project develops a framework for validated numerics in Lean to turn approximate computations into formal proofs. 

### Dyadic Interval Arithmetic
The foundation of this library is a custom `DyadicInterval` type, restricting interval endpoints to dyadic rationals because they admit exact binary representation. 
* The library implements verified interval arithmetic, including operations like addition, multiplication, and a custom division function.
* To counteract the dependency problem (where repeated variables cause systematic overestimation), we implemented specific optimizations, such as a specialized exponentiation function to preserve sharpness.

### Root Certification and the Krawczyk Operator
We formalize computable multivariate polynomials with rational coefficients (`MvRatPol n`). To find roots for these systems, we implemented a recursive branch-and-bound algorithm that subdivides an initial interval vector. 
* This search utilizes the Krawczyk operator, a Newton-like method that scales without the need to compute the inverse of an interval matrix. 
* The algorithm outputs two lists: one containing subintervals certified to have a unique root, and another of unresolved subintervals. 
* If both lists are empty, it certifies the absence of roots.

### The `krawcheck` Tactic
To make the framework accessible, we use metaprogramming to introduce custom syntax for building polynomial systems and dyadic intervals compactly. Furthermore, we provide a custom `krawcheck` tactic that automates several aspects of proof writing. This tactic automatically searches over a grid of parameters, iteratively increasing precision and depth, to convert computational results into proof terms that close goals.

### Application and Motivation
While the core mechanism is a polynomial root-finder, the broader motivation includes proving complex mathematical statements. For instance, certifying the non-triviality of arbitrarily presented groups by showing a homomorphism to $SU(n)$ or $SO(n)$ can be encoded as polynomial constraints. Validated numerics then provides a pathway to rigorously prove these statements.

### References
* Moore, R. E., Kearfott, R. B., & Cloud, M. J. (2009). [*Introduction to Interval Analysis*](http://interval.ict.nsc.ru/Library/InteBooks/IntroIntervAn.pdf)
* Tucker, W. (2011). *Validated Numerics: A Short Introduction to Rigorous Computing*
* Neumaier, A. (1990). *Interval Methods for Systems of Equations*. Cambridge University Press.
