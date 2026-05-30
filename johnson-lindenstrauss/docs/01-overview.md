# The Johnson-Lindenstrauss Lemma: Overview

## Statement

Let `n ≥ 2` points be given in any metric space. For any `0 < ε < 1` and `0 < δ ≤ 1`, if

$$m \geq \frac{4(\ln n + \ln(1/\delta))}{\varepsilon^2}$$

then there exists a mapping `f: X → ℝᵐ` such that for all `x, y ∈ X`:

$$ (1-\varepsilon) \|x - y\|^2 \leq \|f(x) - f(y)\|^2 \leq (1+\varepsilon) \|x - y\|^2 $$

More specifically, a **random Gaussian projection** achieves this with probability ≥ `1 - δ`.

## Proof Strategy

The proof follows Dasgupta & Gupta (1999) and consists of five main steps:

1. **Taylor bounds**: Derive algebraic inequalities for `log(1+ε)` and `log(1-ε)`
2. **Normal MGF**: Compute the moment generating function of a squared standard normal
3. **Chi-squared MGF**: Use the product measure structure of the Gaussian to compute the MGF of the squared norm
4. **Chernoff tail bounds**: Apply the Chernoff method to get exponential concentration
5. **JL lemma**: Combine tail bounds with a union bound over all `n(n-1)/2` pairs

## References

- Dasgupta, S. & Gupta, A. (1999). *An elementary proof of a theorem of Johnson and Lindenstrauss.*
  https://www.eecs.harvard.edu/~michaelm/postscripts/tr-01-05.pdf
- Johnson, W. & Lindenstrauss, J. (1984). *Extensions of Lipschitz mappings into a Hilbert space.*
  https://projecteuclid.org/euclid.hrr/1175446450
- Ingrosso, A. & Schmidt, M. (2020). *Simpler Proof of the Johnson-Lindenstrauss Lemma.*
  https://arxiv.org/abs/2005.10830
