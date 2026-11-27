# x^5 + y^5 = 88 z^5 (open: the only c <= 100 unresolved, see arXiv 2412.11933 Sec 3.2)

Brute-force search over coprime pairs 1 <= x < 200000, -x < y <= x: no solution
(x^5 + y^5 divisible by 88 with quotient a perfect fifth power). search88.c, 4 cores, about 10 minutes.
Equivalent to 4x^5 + 4y^5 = 11z^5; the associated genus-2 curve is Y^2 = 20*88*W^5 + 5.
