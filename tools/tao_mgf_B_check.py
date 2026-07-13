from fractions import Fraction as F
import math

# parameters
theta = F(1,16)
l1 = 16*theta      # = 1
l2 = -5*theta      # = -5/16
print("l1",l1,"l2",l2, "3l2", 3*l2, "l1+3l2", l1+3*l2)

# exp_bound style: for |x|<=1, exp x in [P_{n-1}(x) - E, P + E], E = |x|^n * (n+1)/(n! * n)
def taylor(x,n):
    return sum(F(x)**i / math.factorial(i) for i in range(n))
def expbound(x,n):
    x=F(x)
    P=taylor(x,n)
    E=abs(x)**n * F(n+1,1)/ (math.factorial(n)*n)
    return P-E, P+E   # lower, upper

# We need:
#  e^{l1}=e^1 upper  (use exp_one_lt_d9 approx)
e1_up = F(27182818286,10000000000)
# e^{l2}=e^{-5/16} upper (for Zgh upper) and this is <1
lo,up = expbound(l2,6); e_l2_up = up; print("e^{-5/16} in",float(lo),float(up),"actual",math.exp(float(l2)))
# e^{3l2}=e^{-15/16} lower (subtracted atom) 
lo3,up3 = expbound(3*l2,7); e_3l2_lo = lo3; print("e^{-15/16} in",float(lo3),float(up3),"actual",math.exp(float(3*l2)))
# e^{l1+3l2}=e^{1/16} upper (numerator)
lo4,up4 = expbound(theta,6); e_num_up=up4; print("e^{1/16} in",float(lo4),float(up4),"actual",math.exp(float(theta)))
# e^{theta}=e^{1/16} upper for the '1-1/4 e^theta' margin check (ρ<1)
e_theta_up = up4

# Zgh(l2) = e^{l2}/(2-e^{l2}) increasing in e^{l2}; upper via e_l2_up
Zgh_up = e_l2_up/(2-e_l2_up)
print("Zgh upper", float(Zgh_up), "actual", math.exp(float(l2))/(2-math.exp(float(l2))))
Zpascal_up = Zgh_up**2
# Z_ne3 = (4/3)Zpascal - (1/3)e^{3l2}; upper: (4/3)Zpascal_up - (1/3)e_3l2_lo
Zne3_up = F(4,3)*Zpascal_up - F(1,3)*e_3l2_lo
Zne3_act = F(4,3)*(math.exp(float(l2))/(2-math.exp(float(l2))))**2 - F(1,3)*math.exp(float(3*l2))
print("Zne3 upper", float(Zne3_up), "actual", float(Zne3_act))

# ratio r = 3/4 * e^{l1} * Zne3 ; upper via e1_up, Zne3_up
r_up = F(3,4)*e1_up*Zne3_up
print("ratio r upper", float(r_up), "actual", 0.75*math.exp(1)*float(Zne3_act))
print("r<1?", r_up<1)

# rho = (e^{l1+3l2}/4)/(1-r)  ; upper via e_num_up numerator, r_up denominator
if r_up<1:
    rho_up = (e_num_up/4)/(1-r_up)
    print("rho upper", float(rho_up), "rho<1?", rho_up<1)
    # tail = rho/(1-rho) * e^{-theta B} <= 1/16
    if rho_up<1:
        C = rho_up/(1-rho_up)
        print("C=rho/(1-rho) upper", float(C))
        # need e^{-theta B} <= (1/16)/C  -> B >= (1/theta) ln(16 C)
        import math as m
        B = (1/float(theta))*m.log(16*float(C))
        print("required B", B)
