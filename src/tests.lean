import bigop

open list

#eval big[(*)/1]_(i ∈ (range' 1 5) | true) i
#eval big[(*)/1]_(i ∈ (range' 1 5)) i
#eval big[(*)/1]_(i = 1 .. 5) i
#eval big[(*)/1]_(i=1..5) i
#eval Π_(i = 1..5) i
#eval Π_(i ∈ (range' 1 5) | true) i

#eval Σ_(i ∈ range 5 | nat.prime i) i
#eval Σ_(i = 1..5 | nat.prime i) i
#eval Σ_(i = 1..5) i