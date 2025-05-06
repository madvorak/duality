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


## Main corollaries

* [Farkas for equalities](https://github.com/madvorak/duality/blob/0cc3ca1fb564adab101c37b93947279c48037c67/Duality/FarkasBasic.lean#L26)
* [Farkas for inequalities](https://github.com/madvorak/duality/blob/0cc3ca1fb564adab101c37b93947279c48037c67/Duality/FarkasBasic.lean#L103)
* [Strong duality for standard LP](https://github.com/madvorak/duality/blob/0cc3ca1fb564adab101c37b93947279c48037c67/Duality/LinearProgramming.lean#L1087)


## Main results

* [Farkas-Bartl theorem](https://github.com/madvorak/duality/blob/0cc3ca1fb564adab101c37b93947279c48037c67/Duality/FarkasBartl.lean#L217)
* [Extended Farkas theorem](https://github.com/madvorak/duality/blob/0cc3ca1fb564adab101c37b93947279c48037c67/Duality/FarkasSpecial.lean#L284)
* [Strong duality for extended LP](https://github.com/madvorak/duality/blob/ea1887033d86c29999f64a6d5c056d2267f3814c/Duality/LinearProgramming.lean#L1083)
