# Handle types
| Handle | Integer ID |
| --- | --- |
| noDH | 0 |
| DH | 1 |
| PSK | 2 |
| noPSK | 3 |
| XTR | 4 |
| XPD | 5 |
| 0salt | 6 |
| 0ikm | 7 |

# Key package names
| Name | Integer ID |
| --- | --- |
| psk | 0 |
| hs | 1 |
| es | 2 |
| as | 3 |
| rm | 4 |
| esalt | 5 |
| hsalt | 6 |
| bind | 7 |
| binder | 8 |
| eem | 9 |
| cet | 10 |
| sht | 11 |
| cht | 12 |
| cat | 13 |
| sat | 14 |
| eam | 15 |

# NKey package names
| Name | Integer ID |
| --- | --- |
| dh | 0 |
| 0ikm | 1 |
| 0salt | 2 |

# Log package patterns and mapping parameters
| Pattern | Integer ID |
| --- | --- |
| Z | 0 |
| A | 1 |
| D | 2 |
| F | 3 |

Pattern R is not useful in lemmata C.2 and C.5.

| Mapping | Integer ID |
| --- | --- |
| 0 | 0 |
| 1 | 1 |
| $\infty$ | 2 |

# Algorithms

We assume algorithm 0 is None.

# Separation points and early points

bind is a separation point for binder key (output key).

early: cet, eem

cht, sht, 
cat, sat, eam, 

rm or psk could both be separation point for $psk \in O$ 

# Labels

| Label | Integer ID |
| --- | --- |
| EMPTY | 0 |
| ext binder | 1 |
| res binder | 2 |
| c e traffic | 3 |
| e exp master | 4 |
| derived | 5 |
| c hs traffic | 6 |
| s hs traffic | 7 |
| c ap traffic | 8 |
| s ap traffic | 9 |
| exp master | 10 |
| res master | 11 |
| resumption | 12 |