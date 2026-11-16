"""Exact-Fraction witnesses for SMC-21 calibration-only residual transfer."""
from fractions import Fraction as F
def q(x):return x if isinstance(x,F) else F(x)
def ridge(x,y):
    if not x or len(x)!=len(y):raise ValueError("paired calibration required")
    xx=sum((q(v)**2 for v in x),F(0))
    if not xx:raise ValueError("degenerate residual")
    cross=sum((q(a)*q(b) for a,b in zip(x,y)),F(0))
    return min(F(2),max(F(-2),F(20,21)*cross/xx))
def risk(x,y,beta,absolute=False):
    if not x or len(x)!=len(y):raise ValueError("paired residuals required")
    return sum((abs(q(b)-q(beta)*q(a)) if absolute
                else (q(b)-q(beta)*q(a))**2)
               for a,b in zip(x,y))/len(x)
def moments(x,y):
    if not x or len(x)!=len(y):raise ValueError("paired residuals required")
    return (sum(q(v)**2 for v in y)/len(y),sum(q(a)*q(b) for a,b in zip(x,y))/len(x),
            sum(q(v)**2 for v in x)/len(x))
def risk_shift(cal,test,beta):
    a,c,b=moments(*cal);a2,c2,b2=moments(*test);t=q(beta)
    return ((a2-a)-2*t*(c2-c)+t*t*(b2-b),
            abs(a2-a)+2*abs(t)*abs(c2-c)+t*t*abs(b2-b))
def heavy_tail_witness():
    x=[F(1)]*10;y=[F(0)]*9+[F(10)];beta=ridge(x,y)
    return {'beta':beta,'direct_MAE':risk(x,y,0,True),
            'calibrated_MAE':risk(x,y,beta,True),
            'direct_MSE':risk(x,y,0),'calibrated_MSE':risk(x,y,beta)}
def flip_witness():
    cal=([-1,1],[-1,1]);test=([-1,1],[1,-1]);b=ridge(*cal)
    return {'beta':b,'source_marginal_constant':cal[0]==test[0],
            'direct_test_MAE':risk(*test,0,True),
            'calibrated_test_MAE':risk(*test,b,True),
            'risk_shift':risk_shift(cal,test,b)}
if __name__=="__main__":
    print(heavy_tail_witness());print(flip_witness())
