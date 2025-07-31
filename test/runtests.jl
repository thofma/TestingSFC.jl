using Test, TestingSFC

QG = group_algebra(QQ, dicyclic_group(8))
ZG = integral_group_ring(QG)
@test has_SFC(ZG)
@test has_SFC_naive(ZG)

QG = group_algebra(QQ, dicyclic_group(16))
ZG = integral_group_ring(QG)
@test has_SFC(ZG)
@test has_SFC_naive(ZG)
