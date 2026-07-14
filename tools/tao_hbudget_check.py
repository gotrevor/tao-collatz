#!/usr/bin/env python3
"""Judge pass 28: does the PROVED kernel's `hbudget` close from the planned window?

hbudget (fnat_lt_of_suffix_window, as PROVED):
    l*ln2 + (C*ln2 + (5/4)*(C*ln2)^2)*ln n + ln4  <  n*ln3
i.e. required slack   n*ln3 - l*ln2  >  COST(C)*ln n + ln4,
     COST(C) = C*ln2 + 1.25*(C*ln2)^2
Windows supply   n*ln3 - l*ln2  >=  BUDGET(C)*ln n:
     (6.8) paper half-window : l <= n*log2(3) - 0.5*C^2*ln n   -> BUDGET = ln2*0.5*C^2
     tight (Bk + one-step Ek): l <= n*log2(3) - (C^2-2C)*ln n  -> BUDGET = ln2*(C^2-2C)
"""
from math import log
ln2, ln3 = log(2), log(3)

def cost(C):   return C*ln2 + 1.25*(C*ln2)**2      # the proved lemma (AM-GM at eps=1/5)
def cost_e4(C):return 1.0*(C*ln2)**2               # the reflection's claimed eps=1/4 figure
def half(C):   return ln2*0.5*C**2                 # paper (6.8)
def tight(C):  return ln2*(C**2 - 2*C)             # Bk + one-step Ek

print(f"{'C':>4} {'COST(proved)':>13} {'(6.8) budget':>13} {'tight budget':>13}  {'(6.8)?':>7} {'tight?':>7}")
for C in (10, 15, 20, 22, 23, 25, 30, 50, 100):
    c, h, t = cost(C), half(C), tight(C)
    print(f"{C:>4} {c:>13.2f} {h:>13.2f} {t:>13.2f}  {'OK' if h>c else 'FAIL':>7} {'OK' if t>c else 'FAIL':>7}")

# exact thresholds
a = ln2 - 1.25*ln2**2          # coeff of C^2 in tight - cost
b = -(2*ln2 + ln2)             # coeff of C
print(f"\ntight closes iff {a:.5f}*C^2 + {b:.5f}*C > 0  ->  C > {-b/a:.2f}")
ah = 0.5*ln2 - 1.25*ln2**2
print(f"(6.8) closes iff {ah:.5f}*C^2 - {ln2:.5f}*C > 0  -> C^2 coeff is {'NEGATIVE -> NEVER closes' if ah<0 else 'positive'}")
print(f"\nreflection/DIRECTION claimed eps=1/4 cost {cost_e4(10):.2f} at C=10 vs tight budget {tight(10):.2f} -> would 'close'")
print(f"but the PROVED lemma (eps=1/5) costs {cost(10):.2f} at C=10 vs tight budget {tight(10):.2f} -> FAILS")
