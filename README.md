# Duality theory in linear optimization and its extensions

Farkas established that a system of linear inequalities has a solution if and only if we cannot obtain
a contradiction by taking a linear combination of the inequalities.
We state and formally prove several Farkas-like theorems in Lean 4.
Furthermore, we consider a linearly ordered field extended with two special elements denoted by $\bot$ and $\top$
where $\bot$ is below every element and $\top$ is above every element.
We define $\bot + a = \bot = a + \bot$ for all $a$ and we define $\top + b = \top = b + \top$ for all $b \neq \bot$.
Instead of multiplication, we define scalar action $c \bullet \bot = \bot$ for every $c \ge 0$ but we define
$d \bullet \top = \top$ only for $d > 0$ because $0 \bullet \top = 0$.
We extend certain Farkas-like theorems to a setting where coefficients are from an extended linearly ordered field.

![AI-generated image](AI-generated.jpg)

## Main results

* [Farkas-Bartl theorem](https://github.com/madvorak/duality/blob/cd780dad0de8271e248006d54327cc9307eb8022/Duality/FarkasBartl.lean#L216)
* [Strong duality for extended LP](https://github.com/madvorak/duality/blob/cd780dad0de8271e248006d54327cc9307eb8022/Duality/LinearProgramming.lean#L1019)

[Overview](duality.pdf)
